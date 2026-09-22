"""Regression tests for bounded rows, exact coverage, and replay dependencies."""

from __future__ import annotations

import hashlib
import json
import re
from itertools import pairwise
from pathlib import Path

import pytest

from scripts.full_record_gap_compact_helpers import (
    ROW_SIZE,
    Row,
    make_rows,
    render_aggregate,
    render_assembly,
    render_owners,
    render_replay,
)
from scripts.lean_source import lean_imports
from scripts.record_gap_ci import manifest


def test_rows_cover_offsets_once_in_order() -> None:
    factors = [2, 0, 13] * (ROW_SIZE // 3 + 5)
    rows = make_rows("Sub", factors, 1)
    assert rows[0].start == 1
    assert rows[-1].stop == len(factors) + 1
    assert all(left.stop == right.start for left, right in pairwise(rows))
    assert [q for row in rows for q in row.factors] == factors
    assert max(len(row.factors) for row in rows) <= ROW_SIZE


@pytest.mark.parametrize("values", [[], [1], [-2]])
def test_invalid_factor_schema_rejected(values: list[int]) -> None:
    with pytest.raises(ValueError):
        make_rows("Sub", values, 1)


def test_data_has_no_search_or_case_fanout() -> None:
    source = render_owners(Row("Sub", 1, (2, 0, 13), 1))
    assert "[ 2, 0, 13 ]" in source
    assert "eager_decide" in source
    assert not re.search(r"fin_cases|minFac|padicValNat|by_cases", source)
    assert len(source.splitlines()) < 40


def test_replay_serializes_within_shard_only() -> None:
    first = Row("Sub", 1, (2, 0), 1)
    second = Row("Sub", 3, (0, 5), 2)
    assert not any("Replay001" in item for item in lean_imports(render_replay(first, None)))
    assert any("Replay001" in item for item in lean_imports(render_replay(second, first)))
    assert render_replay(first, None).count("replay_gap_fermat") == 1


def test_assembly_rejects_missing_ranges() -> None:
    with pytest.raises(ValueError, match="incomplete Sub"):
        render_aggregate([Row("Sub", 2, (2,), 1)], [])


def test_module_imports_are_not_invisible_to_policy() -> None:
    assert lean_imports("module\npublic import A\npublic meta import B\nimport C\n") == [
        "A",
        "B",
        "C",
    ]


def test_committed_rows_match_generator_and_semantic_digest() -> None:
    root = Path(__file__).resolve().parents[2]
    directory = root / "PrimeFactorUnimodality/Proof/LargeRange/Generated/FullRecordGapCompactRows"
    data = manifest()
    rows: list[Row] = []
    sides: dict[str, list[int]] = {"Sub": [], "Add": []}
    max_exceptions = 0
    for shard in data["shards"]:
        previous = None
        exceptions = 0
        for tag in shard["rows"]:
            source = (directory / f"Owners{tag}.lean").read_text()
            match = re.search(r"compactGapCheck (true|false) (\d+)", source)
            assert match is not None
            side = "Add" if match[1] == "true" else "Sub"
            body = source.split(": List Nat :=", 1)[1].split("]", 1)[0]
            values = tuple(map(int, re.findall(r"\d+", body)))
            row = Row(side, int(match[2]), values, int(tag))
            assert row.start == len(sides[side]) + 1
            assert 1 <= len(values) <= ROW_SIZE
            assert source == render_owners(row)
            assert (directory / f"Replay{tag}.lean").read_text() == render_replay(row, previous)
            assert len(source.splitlines()) < 250
            sides[side].extend(values)
            exceptions += values.count(0)
            rows.append(row)
            previous = row
        max_exceptions = max(max_exceptions, exceptions)
    assert [len(sides[side]) for side in ("Sub", "Add")] == [455703, 657401]
    assert [sides[side].count(0) for side in ("Sub", "Add")] == [3815, 7103]
    encoded = json.dumps([sides["Sub"], sides["Add"]], separators=(",", ":")).encode()
    assert hashlib.sha256(encoded).hexdigest() == data["row_sha256"]
    # At the measured 81s/witness, leave headroom under the 150-minute step limit.
    assert max_exceptions <= 100
    for number, start in enumerate(range(0, len(rows), 32), 1):
        assert (directory / f"Assembly{number:03d}.lean").read_text() == render_assembly(
            rows[start : start + 32], number
        )
