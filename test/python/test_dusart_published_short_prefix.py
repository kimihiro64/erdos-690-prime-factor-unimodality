"""Audit compact full-domain prime witnesses and their exact logarithm budgets."""

from __future__ import annotations

from dataclasses import replace
from itertools import pairwise

import pytest

from scripts.generate_dusart_published_short_prefix import (
    BATCH_SIZE,
    CUTOFF,
    DESTINATION,
    MODULE,
    ROOT,
    SIEVE_LIMIT,
    SIEVE_ROOT,
    START,
    Row,
    certificate_rows,
    render_files,
    semantic_hash,
)
from scripts.generate_medium_log_rows import primes_through
from scripts.lean_source import lean_imports, strip_lean_comments


@pytest.fixture(scope="module")
def data() -> tuple[set[int], list[Row]]:
    primes = primes_through(SIEVE_LIMIT)
    return set(primes), certificate_rows(primes)


def test_complete_coverage_and_witnesses(data: tuple[set[int], list[Row]]) -> None:
    primes, rows = data
    assert len(rows) == 2022
    assert rows[0].left == START
    assert rows[-1].prime == 3601993 > CUTOFF
    assert rows[-1].left <= CUTOFF
    assert len({row.prime for row in rows}) == len(rows)
    assert all(first.prime == second.left for first, second in pairwise(rows))
    assert all(row.valid(primes) for row in rows)
    assert sum(row.prime - row.left for row in rows) == rows[-1].prime - START
    assert SIEVE_LIMIT <= SIEVE_ROOT**2
    assert all(3 * row.index + 1 + row.index % 2 == row.prime for row in rows)


def test_invalid_witnesses_and_widths_are_rejected(data: tuple[set[int], list[Row]]) -> None:
    primes, rows = data
    first, second = rows[:2]
    assert (first.left, first.prime, second.prime) == (3275, 3299, 3323)
    composite = replace(first, prime=3295, index=1098)
    assert composite.margins_valid()
    assert not composite.valid(primes)
    assert not replace(first, index=1100).valid(primes)
    assert not replace(second, left=3275).margins_valid()
    assert not replace(first, left=first.prime).valid(primes)
    assert not replace(first, power=(first.power[0], first.power[1] + 1, *first.power[2:])).valid(
        primes
    )


def test_sources_are_compact_and_serial(data: tuple[set[int], list[Row]]) -> None:
    _, rows = data
    files = render_files(rows)
    assert len(files) == 10
    assert sum(len(source.encode()) for source in files.values()) < 125000
    digest = semantic_hash(rows)
    assert digest == "0bc33166d15dc50b4cfaf567d22ffbe810893931e1f32d10811629333155e5fc"
    for path, source in files.items():
        assert path.read_text() == source
        assert f"Semantic SHA-256: {digest}" in source
        assert len(source.splitlines()) <= BATCH_SIZE + 50
        assert "interval_cases" not in source
    for number in range(1, 9):
        source = files[DESTINATION / f"Part{number:02d}.lean"]
        previous = f"Part{number - 1:02d}" if number > 1 else "Base"
        assert source.startswith(f"import {MODULE}.{previous}\n")
        assert source.count("private theorem checked") == 1
    assert "HasDusartShortIntervalPrimeBelow 3594641" in files[DESTINATION.with_suffix(".lean")]


def test_missing_rows_and_changed_provenance_are_detected(data: tuple[set[int], list[Row]]) -> None:
    _, rows = data
    for incomplete in [[], rows[1:], rows[:-1], rows[:3] + rows[4:]]:
        with pytest.raises(ValueError):
            render_files(incomplete)
    assert semantic_hash(rows) != semantic_hash([replace(rows[0], index=0), *rows[1:]])


def test_prefix_does_not_import_retired_or_unbounded_pipeline() -> None:
    pending = [MODULE]
    seen: set[str] = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        assert not module.startswith("PrimeNumberTheoremAnd.")
        assert not module.startswith(
            "PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Low"
        )
        source = ROOT.joinpath(*module.split(".")).with_suffix(".lean")
        if source.is_file():
            pending.extend(lean_imports(strip_lean_comments(source.read_text())))
