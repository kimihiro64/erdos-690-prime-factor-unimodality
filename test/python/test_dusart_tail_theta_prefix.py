"""Audit the complete theta trace, fixed-point arithmetic and stable replay units."""

from __future__ import annotations

from dataclasses import replace
from itertools import pairwise

import pytest

from scripts.generate_dusart_tail_theta_prefix import (
    BATCH_SIZE,
    CUTOFF,
    DEPTH,
    DESTINATION,
    MODULE,
    ROOT,
    SEED,
    THRESHOLD,
    Row,
    certificate_rows,
    render_base,
    render_files,
    render_part,
    semantic_hash,
)
from scripts.generate_medium_log_rows import primes_through
from scripts.lean_source import lean_imports, strip_lean_comments


@pytest.fixture(scope="module")
def data() -> tuple[list[int], list[Row]]:
    primes = primes_through(CUTOFF)
    return primes, certificate_rows(primes)


def test_complete_trace_and_exact_counts(data: tuple[list[int], list[Row]]) -> None:
    primes, rows = data
    assert len(rows) == 9765
    assert rows[0].start == SEED
    assert rows[-1].next.point == CUTOFF
    assert rows[-1].next.count == 256357
    assert sum(row.next.point - row.start.point for row in rows) == CUTOFF - SEED.point
    assert all(first.next == second.start for first, second in pairwise(rows))
    assert len({row.next.point for row in rows}) == len(rows)
    assert all(row.valid(primes) for row in rows)
    assert any(row.start.point == THRESHOLD for row in rows)
    assert not any(row.start.point < THRESHOLD < row.next.point for row in rows)


def test_local_depth_is_sufficient(data: tuple[list[int], list[Row]]) -> None:
    def wheel_length(n: int) -> int:
        return (n + 1) // 6 + n // 6 + int(n % 6 != 0)

    _, rows = data
    assert max(row.next.point - row.start.point for row in rows) == 3588
    assert all(
        0 <= wheel_length(row.next.point) - wheel_length(row.start.point) <= 2**DEPTH
        for row in rows
    )


def test_corrupted_counts_logs_and_enclosures_fail(data: tuple[list[int], list[Row]]) -> None:
    primes, rows = data
    row = rows[-1]
    assert not replace(row, next=replace(row.next, count=row.next.count + 1)).valid(primes)
    assert not replace(row, next=replace(row.next, lower=row.next.lower + 1)).margins_valid()
    assert not replace(row, next=replace(row.next, upper=row.next.upper - 1)).margins_valid()
    bad_power = (row.lower[0], row.lower[1] + 1, *row.lower[2:])
    assert not replace(row, lower=bad_power).margins_valid()
    assert not replace(row, start=row.next).margins_valid()


def test_generated_sources_are_current_and_bounded(data: tuple[list[int], list[Row]]) -> None:
    _, rows = data
    files = render_files(rows)
    assert len(files) == 28
    assert sum(len(source.encode()) for source in files.values()) < 1400000
    assert semantic_hash(rows) == "71eaeed047c8df90d1b290d2372a8d19e36c67d9644d1c5d7d5b9f5e3de8e191"
    for path, source in files.items():
        assert path.read_text() == source
        assert len(source.splitlines()) < 850
        assert max(map(len, source.splitlines())) <= 100
        assert "interval_cases" not in source
    for number in range(1, 27):
        source = files[DESTINATION / f"Part{number:02d}.lean"]
        previous = f"Part{number - 1:02d}" if number > 1 else "Base"
        assert source.startswith(f"import {MODULE}.{previous}\n")
        assert source.count("private theorem checked") == 1
        assert "checkDusartThetaTrace" in source


def test_wrong_endpoints_or_missing_rows_are_rejected(data: tuple[list[int], list[Row]]) -> None:
    _, rows = data
    for incomplete in [[], rows[1:], rows[:-1], rows[:2] + rows[3:]]:
        with pytest.raises(ValueError):
            render_files(incomplete)


def test_later_changes_preserve_earlier_source_keys(data: tuple[list[int], list[Row]]) -> None:
    _, rows = data
    original = render_files(rows)
    changed = [
        *rows[:-1],
        replace(rows[-1], next=replace(rows[-1].next, upper=rows[-1].next.upper + 1)),
    ]
    assert semantic_hash(changed) != semantic_hash(rows)
    revised = render_files(changed)
    assert (
        revised[DESTINATION / "Base.lean"] == original[DESTINATION / "Base.lean"] == render_base()
    )
    assert revised[DESTINATION / "Part01.lean"] == original[DESTINATION / "Part01.lean"]
    assert revised[DESTINATION / "Part26.lean"] != original[DESTINATION / "Part26.lean"]
    assert render_part(rows[:BATCH_SIZE], 1) == original[DESTINATION / "Part01.lean"]


def test_prefix_keeps_the_unbounded_pipeline_out() -> None:
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
