"""Audit the full half-open prefix data, provenance and serial assembly."""

from __future__ import annotations

from dataclasses import replace
from itertools import pairwise

import pytest

from scripts.generate_dusart_published_pi_prefix import (
    BATCH_SIZE,
    CUTOFF,
    DESTINATION,
    MODULE,
    ROOT,
    START,
    STEP_DEPTH,
    Row,
    certificate_rows,
    render_files,
    semantic_hash,
)
from scripts.generate_medium_log_rows import primes_through
from scripts.lean_source import lean_imports, strip_lean_comments


@pytest.fixture(scope="module")
def data() -> tuple[list[int], list[Row]]:
    primes = primes_through(CUTOFF)
    return primes, certificate_rows(primes)


def test_complete_coverage_and_counts(data: tuple[list[int], list[Row]]) -> None:
    primes, rows = data
    assert len(primes) == 256357
    assert len(rows) == 2093
    assert rows[0].left == START
    assert rows[-1].right == CUTOFF + 1
    assert len({row.left for row in rows}) == len(rows)
    assert all(first.right == second.left for first, second in pairwise(rows))
    assert all(row.valid(primes) for row in rows)
    assert sum(row.right - row.left for row in rows) == CUTOFF + 1 - START
    assert max(row.right - row.left for row in rows) == 14319


def test_local_count_depth_covers_every_transition(data: tuple[list[int], list[Row]]) -> None:
    def wheel_length(n: int) -> int:
        return (n + 1) // 6 + n // 6 + int(n % 6 != 0)

    _, rows = data
    point = START
    for row in rows:
        assert 0 <= wheel_length(row.left) - wheel_length(point) <= 2**STEP_DEPTH
        assert 0 <= wheel_length(row.right - 1) - wheel_length(row.left) <= 2**STEP_DEPTH
        point = row.right - 1


def test_prime_jump_is_not_charged_to_preceding_cell(data: tuple[list[int], list[Row]]) -> None:
    primes, rows = data
    row = next(row for row in rows if row.left == 1626)
    assert row.right == 1627
    assert row.left_count == row.before_count == 257
    assert 1627 in primes
    assert not replace(row, before_count=258).margins_valid()
    assert not replace(row, left_count=258).valid(primes)
    assert not replace(row, lower=(row.lower[0], row.lower[1] + 1, *row.lower[2:])).valid(primes)
    assert not replace(row, right=row.left).valid(primes)


def test_rendered_files_are_current_and_compact(data: tuple[list[int], list[Row]]) -> None:
    _, rows = data
    files = render_files(rows)
    assert len(files) == 11
    assert sum(len(source.encode()) for source in files.values()) < 210000
    digest = semantic_hash(rows)
    assert digest == "f5ffd585723ab3d44b013960bce5ef9c62e41e16c18c51821e22f3bb6d157fe0"
    for path, source in files.items():
        assert path.read_text() == source
        assert f"Semantic SHA-256: {digest}" in source
        assert len(source.splitlines()) <= BATCH_SIZE + 50
        assert "interval_cases" not in source
    for number in range(1, 10):
        source = files[DESTINATION / f"Part{number:02d}.lean"]
        previous = f"Part{number - 1:02d}" if number > 1 else "Base"
        assert source.startswith(f"import {MODULE}.{previous}\n")
        assert source.count("private theorem checked") == 1
        assert "checkDusartSievePiSteps" in source
    assert (
        "HasDusartRealPrimeCountingBoundsBelow 3594641" in files[DESTINATION.with_suffix(".lean")]
    )


def test_missing_rows_and_changed_provenance_are_detected(
    data: tuple[list[int], list[Row]],
) -> None:
    _, rows = data
    for incomplete in [rows[1:], rows[:-1], rows[:3] + rows[4:]]:
        with pytest.raises(ValueError):
            render_files(incomplete)
    assert semantic_hash(rows) != semantic_hash(
        [replace(rows[0], left_count=rows[0].left_count + 1), *rows[1:]]
    )


def test_prefix_does_not_import_unbounded_pnt_pipeline() -> None:
    pending = [MODULE]
    seen: set[str] = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        assert not module.startswith("PrimeNumberTheoremAnd.")
        source = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if source.is_file():
            pending.extend(lean_imports(strip_lean_comments(source.read_text())))
