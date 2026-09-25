"""Whole-proof cache checks must not enable parallel compilation or lose checkpoints."""

from __future__ import annotations

import signal
import subprocess
from pathlib import Path
from unittest.mock import Mock, patch

import pytest

from scripts.conditional_dusart_ci import build, replay_units, run_lake, validate_cached
from scripts.conditional_dusart_plan import Unit, required_artifacts

DEADLINE = float("inf")
RUNNER = "scripts.conditional_dusart_ci"


@pytest.mark.parametrize("status", [0, 3])
def test_validation_disables_compilation_and_accepts_only_cache_statuses(status: int) -> None:
    with patch(f"{RUNNER}.subprocess.Popen") as popen:
        popen.return_value.__enter__.return_value.wait.return_value = status
        assert run_lake(Path("."), ("A", "B"), DEADLINE, check=True) == status
    assert popen.call_args.args[0] == ["lake", "build", "--no-build", "-q", "+A", "+B"]
    assert popen.call_args.kwargs["start_new_session"] is True


@pytest.mark.parametrize("check,status", [(True, 1), (True, 143), (True, -15), (False, 3)])
def test_non_cache_failures_are_fatal(check: bool, status: int) -> None:
    with patch(f"{RUNNER}.subprocess.Popen") as popen:
        process = popen.return_value.__enter__.return_value
        process.wait.return_value = status
        process.args = ["lake", "build", "+A"]
        with pytest.raises(subprocess.CalledProcessError) as error:
            run_lake(Path("."), ("A",), DEADLINE, check=check)
    assert error.value.returncode == status


def test_actual_compilation_accepts_exactly_one_target() -> None:
    with patch(f"{RUNNER}.subprocess.Popen") as popen:
        with pytest.raises(ValueError, match="one target"):
            run_lake(Path("."), ("A", "B"), DEADLINE, check=False)
        popen.assert_not_called()
        popen.return_value.__enter__.return_value.wait.return_value = 0
        build(Path("."), "A", DEADLINE)
    assert popen.call_args.args[0] == ["lake", "build", "+A"]


def test_empty_prefix_does_not_start_lake() -> None:
    with patch(f"{RUNNER}.run_lake") as run:
        validate_cached(Path("."), (), DEADLINE)
    run.assert_not_called()


def test_fresh_prefix_uses_one_check_and_no_builds() -> None:
    with patch(f"{RUNNER}.run_lake", return_value=0) as run:
        validate_cached(Path("."), ("A", "B", "C"), DEADLINE)
    run.assert_called_once_with(Path("."), ("A", "B", "C"), DEADLINE, check=True)


def test_stale_prefix_repairs_in_order_and_rechecks_right_after_left() -> None:
    fresh = {"A", "C"}
    compiled: list[str] = []

    def run(root: Path, targets: tuple[str, ...], deadline: float, *, check: bool) -> int:
        if check:
            return 0 if set(targets) <= fresh else 3
        assert len(targets) == 1
        target = targets[0]
        compiled.append(target)
        fresh.add(target)
        if target == "B":
            # D can become fresh when B's absent output is repaired.
            fresh.add("D")
        return 0

    with patch(f"{RUNNER}.run_lake", side_effect=run):
        validate_cached(Path("."), ("A", "B", "C", "D", "E"), DEADLINE)
    assert compiled == ["B", "E"]


def test_validation_error_does_not_fall_back_to_compilation() -> None:
    with (
        patch(f"{RUNNER}.run_lake", side_effect=subprocess.CalledProcessError(1, ["lake"])) as run,
        pytest.raises(subprocess.CalledProcessError),
    ):
        validate_cached(Path("."), ("A", "B"), DEADLINE)
    assert run.call_count == 1


def test_expired_budget_starts_nothing() -> None:
    with (
        patch(f"{RUNNER}.subprocess.Popen") as popen,
        pytest.raises(TimeoutError, match="before starting Lake"),
    ):
        run_lake(Path("."), ("A",), 0, check=True)
    popen.assert_not_called()


def test_validation_timeout_terminates_only_its_process_group() -> None:
    with (
        patch(f"{RUNNER}.subprocess.Popen") as popen,
        patch(f"{RUNNER}.time.monotonic", side_effect=[0, 0, 1, 11, 11, 12]),
        patch(f"{RUNNER}.os.killpg") as kill,
    ):
        process = popen.return_value.__enter__.return_value
        process.pid = 12345
        process.wait.side_effect = [subprocess.TimeoutExpired(["lake"], 9), 0]
        with pytest.raises(TimeoutError, match="time budget reached"):
            run_lake(Path("."), ("A", "B"), 10, check=True)
    kill.assert_called_once_with(12345, signal.SIGTERM)


def unit(number: int, *modules: str) -> Unit:
    return Unit(tuple(modules), f"{number:064x}", "certificates")


def local_artifacts(root: Path, units: list[Unit]) -> None:
    for u in units:
        for path in required_artifacts(u):
            target = root / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(b"fixture")


def cache_hit(events: list[object], event: object) -> int:
    events.append(event)
    return 0


def test_saved_prefix_is_restored_before_one_validation(tmp_path: Path) -> None:
    units = [unit(1, "A", "B"), unit(2, "C", "D")]
    store = Mock(assets={u.asset for u in units}, read_only=False)
    store.download.side_effect = lambda u, scratch: scratch / u.asset
    events: list[object] = []
    with (
        patch(f"{RUNNER}.Store", return_value=store),
        patch(f"{RUNNER}.restore", side_effect=lambda root, u, archive: events.append(u.asset)),
        patch(f"{RUNNER}.run_lake", side_effect=lambda root, ms, d, **kw: cache_hit(events, ms)),
        patch(f"{RUNNER}.validate_cached") as validate,
        patch(f"{RUNNER}.build") as compile_one,
        patch(f"{RUNNER}.pack") as pack,
    ):
        replay_units(tmp_path, units, "o/r", "commit", DEADLINE, read_only=False)
    assert events == [units[0].asset, units[1].asset, ("A", "B", "C", "D")]
    compile_one.assert_not_called()
    validate.assert_not_called()
    pack.assert_not_called()
    store.upload.assert_not_called()


def test_cold_unit_is_saved_before_work_on_the_next_unit(tmp_path: Path) -> None:
    units = [unit(1, "A", "B"), unit(2, "C", "D"), unit(3, "E")]
    store = Mock(assets={units[0].asset, units[2].asset}, read_only=False)
    store.download.side_effect = lambda u, scratch: (
        scratch / u.asset if u.asset in store.assets else None
    )
    events: list[object] = []
    store.upload.side_effect = lambda u, archive: events.append(("save", u.asset))
    with (
        patch(f"{RUNNER}.Store", return_value=store),
        patch(f"{RUNNER}.restore"),
        patch(f"{RUNNER}.pack"),
        patch(f"{RUNNER}.run_lake", side_effect=lambda root, ms, d, **kw: cache_hit(events, ms)),
        patch(f"{RUNNER}.build", side_effect=lambda root, m, d: events.append(("build", m))),
    ):
        replay_units(tmp_path, units, "o/r", "commit", DEADLINE, read_only=False)
    assert events == [("A", "B"), ("build", "C"), ("build", "D"), ("save", units[1].asset), ("E",)]


def test_local_artifact_without_remote_copy_is_checked_then_saved(tmp_path: Path) -> None:
    u = unit(1, "A")
    local_artifacts(tmp_path, [u])
    store = Mock(assets=set(), read_only=False)
    events: list[object] = []
    store.upload.side_effect = lambda *_: events.append("save")
    with (
        patch(f"{RUNNER}.Store", return_value=store),
        patch(f"{RUNNER}.pack"),
        patch(
            f"{RUNNER}.run_lake",
            side_effect=lambda *args, **kw: cache_hit(events, "check"),
        ),
        patch(f"{RUNNER}.build") as compile_one,
    ):
        replay_units(tmp_path, [u], "o/r", "commit", DEADLINE, read_only=False)
    assert events == ["check", "save"]
    store.download.assert_not_called()
    compile_one.assert_not_called()


def test_corrupt_restore_never_reaches_validation_or_compilation(tmp_path: Path) -> None:
    u = unit(1, "A")
    store = Mock(assets={u.asset}, read_only=False)
    store.download.return_value = tmp_path / u.asset
    with (
        patch(f"{RUNNER}.Store", return_value=store),
        patch(f"{RUNNER}.restore", side_effect=ValueError("artifact digest mismatch")),
        patch(f"{RUNNER}.validate_cached") as validate,
        patch(f"{RUNNER}.run_lake") as run,
        patch(f"{RUNNER}.build") as compile_one,
        pytest.raises(ValueError, match="digest"),
    ):
        replay_units(tmp_path, [u], "o/r", "commit", DEADLINE, read_only=False)
    validate.assert_not_called()
    run.assert_not_called()
    compile_one.assert_not_called()


def test_read_only_cold_unit_is_never_uploaded(tmp_path: Path) -> None:
    store = Mock(assets=set(), read_only=True)
    store.download.return_value = None
    with (
        patch(f"{RUNNER}.Store", return_value=store) as constructor,
        patch(f"{RUNNER}.validate_cached"),
        patch(f"{RUNNER}.build") as compile_one,
        patch(f"{RUNNER}.pack") as pack,
    ):
        replay_units(tmp_path, [unit(1, "A")], "o/r", "commit", DEADLINE, read_only=True)
    assert constructor.call_args.kwargs["read_only"] is True
    compile_one.assert_called_once_with(tmp_path, "A", DEADLINE)
    store.upload.assert_not_called()
    pack.assert_not_called()


def test_whole_restored_proof_exceeds_old_batch_limit_but_uses_one_check(tmp_path: Path) -> None:
    units = [unit(i, f"Module{i}") for i in range(300)]
    store = Mock(assets={u.asset for u in units}, read_only=False)
    store.download.side_effect = lambda u, scratch: scratch / u.asset
    with (
        patch(f"{RUNNER}.Store", return_value=store),
        patch(f"{RUNNER}.restore"),
        patch(f"{RUNNER}.run_lake", return_value=0) as run,
        patch(f"{RUNNER}.validate_cached") as validate,
        patch(f"{RUNNER}.build") as compile_one,
    ):
        replay_units(tmp_path, units, "o/r", "commit", DEADLINE, read_only=False)
    run.assert_called_once_with(tmp_path, tuple(u.modules[0] for u in units), DEADLINE, check=True)
    validate.assert_not_called()
    compile_one.assert_not_called()


def test_whole_local_proof_checked_once_before_saving_missing_remote_copies(tmp_path: Path) -> None:
    units = [unit(1, "A"), Unit(("B",), "2" * 64, "foundations"), unit(3, "C")]
    local_artifacts(tmp_path, units)
    store = Mock(assets={units[0].asset}, read_only=False)
    events: list[object] = []
    store.upload.side_effect = lambda u, archive: events.append(("save", u.asset))
    with (
        patch(f"{RUNNER}.Store", return_value=store),
        patch(f"{RUNNER}.pack"),
        patch(
            f"{RUNNER}.run_lake",
            side_effect=lambda *args, **kw: cache_hit(events, ("check", args[1])),
        ) as run,
        patch(f"{RUNNER}.validate_cached") as validate,
        patch(f"{RUNNER}.build") as compile_one,
    ):
        replay_units(tmp_path, units, "o/r", "commit", DEADLINE, read_only=False)
    assert events == [
        ("check", ("A", "B", "C")),
        ("save", units[1].asset),
        ("save", units[2].asset),
    ]
    run.assert_called_once_with(tmp_path, ("A", "B", "C"), DEADLINE, check=True)
    store.download.assert_not_called()
    validate.assert_not_called()
    compile_one.assert_not_called()


def test_stale_whole_proof_saves_repaired_units_before_later_failure(tmp_path: Path) -> None:
    units = [unit(1, "A"), unit(2, "B")]
    local_artifacts(tmp_path, units)
    store = Mock(assets=set(), read_only=False)
    events: list[object] = []
    store.upload.side_effect = lambda u, archive: events.append(("save", u.asset))

    def repair(root: Path, targets: tuple[str, ...], deadline: float) -> None:
        events.append(("repair", targets))
        if targets == ("B",):
            raise subprocess.CalledProcessError(1, ["lake"])

    with (
        patch(f"{RUNNER}.Store", return_value=store),
        patch(f"{RUNNER}.pack"),
        patch(f"{RUNNER}.run_lake", return_value=3) as run,
        patch(f"{RUNNER}.validate_cached", side_effect=repair),
        pytest.raises(subprocess.CalledProcessError),
    ):
        replay_units(tmp_path, units, "o/r", "commit", DEADLINE, read_only=False)
    run.assert_called_once_with(tmp_path, ("A", "B"), DEADLINE, check=True)
    assert events == [("repair", ("A",)), ("save", units[0].asset), ("repair", ("B",))]


def test_whole_proof_error_does_not_rebuild_or_save(tmp_path: Path) -> None:
    units = [unit(1, "A", "B")]
    local_artifacts(tmp_path, units)
    store = Mock(assets=set(), read_only=False)
    with (
        patch(f"{RUNNER}.Store", return_value=store),
        patch(f"{RUNNER}.run_lake", side_effect=subprocess.CalledProcessError(143, ["lake"])),
        patch(f"{RUNNER}.validate_cached") as validate,
        patch(f"{RUNNER}.build") as compile_one,
        patch(f"{RUNNER}.pack") as pack,
        pytest.raises(subprocess.CalledProcessError),
    ):
        replay_units(tmp_path, units, "o/r", "commit", DEADLINE, read_only=False)
    validate.assert_not_called()
    compile_one.assert_not_called()
    pack.assert_not_called()
    store.upload.assert_not_called()


def test_read_only_warm_proof_checked_once_without_uploads(tmp_path: Path) -> None:
    units = [unit(1, "A"), unit(2, "B")]
    local_artifacts(tmp_path, units)
    store = Mock(assets=set(), read_only=True)
    with (
        patch(f"{RUNNER}.Store", return_value=store),
        patch(f"{RUNNER}.run_lake", return_value=0) as run,
        patch(f"{RUNNER}.pack") as pack,
    ):
        replay_units(tmp_path, units, "o/r", "commit", DEADLINE, read_only=True)
    run.assert_called_once_with(tmp_path, ("A", "B"), DEADLINE, check=True)
    store.download.assert_not_called()
    store.upload.assert_not_called()
    pack.assert_not_called()
