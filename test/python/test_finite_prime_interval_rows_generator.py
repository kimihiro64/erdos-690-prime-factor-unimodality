import re
from pathlib import Path

import pytest

from scripts.generate_finite_prime_interval_rows import main


def test_finite_prime_interval_rows_low_generation_is_sharded(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repo = Path(__file__).resolve().parents[2]
    monkeypatch.setattr(
        "sys.argv",
        [
            "generate_finite_prime_interval_rows.py",
            "--repo",
            str(repo),
            "--output-dir",
            str(tmp_path),
        ],
    )
    (tmp_path / "LowPart99.lean").write_text("stale generated shard")

    main()

    manifest = (tmp_path / "LowManifest.lean").read_text()
    match = re.search(r"finitePrimeIntervalRowsLowPartCount : Nat := (\d+)", manifest)
    assert match is not None
    count = int(match.group(1))
    assert count > 0

    facade = (tmp_path / "Low.lean").read_text()
    assert f"LowGroup{(count + 11) // 12:02d}" in facade
    assert "shared coverage data. -/" in facade
    assert "shared coverage data. -}" not in facade

    for part in range(1, count + 1):
        path = tmp_path / f"LowPart{part:02d}.lean"
        assert path.exists()
        # Each shard includes its local reusable Pocklington data table and
        # assembler proof; the generator's 32 KiB row-family target therefore
        # expands to at most this bounded source size.
        assert path.stat().st_size <= 80_000
        assert ".LowBase\n" in path.read_text()

    groups = sorted(tmp_path.glob("LowGroup*.lean"))
    assert groups
    assert all(f".LowGroup{index:02d}\n" in facade for index in range(1, len(groups) + 1))
    assert ".LowPart01\n" in groups[0].read_text()
    assert ".LowPart02\n" in groups[0].read_text()
    assert all(
        len(re.findall(r"^import .*\.LowPart\d+$", group.read_text(), re.MULTILINE)) <= 12
        for group in groups
    )

    first = (tmp_path / "LowPart01.lean").read_text()
    assert "apply DusartPrimeRowsChain.cons" in first
    assert "theorem lowPocklingtonPrime01" in first
    assert "theorem lowPrime_3299" not in first
    for path in tmp_path.glob("LowPart*.lean"):
        text = path.read_text()
        assert "apply DusartPrimeRowsChain.cons" in text
        assert "decide +kernel" not in text

    assert not list(tmp_path.glob(f"LowPart{count + 1:02d}.lean"))
    assert not (tmp_path / "LowPart99.lean").exists()
    assert not list(tmp_path.glob("LowGroup99.lean"))
