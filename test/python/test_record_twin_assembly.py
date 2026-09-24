"""Keep semantic assembly typed in the residue algebra, without broad simplification."""

from __future__ import annotations

import importlib
import re
from pathlib import Path
from types import ModuleType

import pytest

ROOT = Path(__file__).resolve().parents[2]
GENERATED = ROOT / "PrimeFactorUnimodality/Proof/LargeRange/Generated"


@pytest.fixture
def renderer(monkeypatch: pytest.MonkeyPatch) -> ModuleType:
    monkeypatch.syspath_prepend(str(ROOT / "scripts"))
    return importlib.import_module("render_record_twin_seed_tail")


@pytest.mark.parametrize("task", ["upper-seed", "lower-seed"])
def test_assembly_types_every_power_and_reuses_checked_steps(
    renderer: ModuleType, task: str
) -> None:
    side, state_type, base, _ = renderer.names(task)
    source = renderer.render_assembly_group(task, 0, 463, "test provenance", 1)
    assert f"have h000 : (1 : {state_type}) =" in source
    assert source.count(f"({base} : {state_type}) ^") == 42
    assert "simpa only" not in source
    assert source.count("(boundary.trans ") == 40
    assert f"record{side}SeedTailChunk040Step.certifies" in source
    facade = renderer.render_facade(task, 463, "test provenance", 12)
    assert f"({base} : {state_type}) ^ recordSeedExponent" in facade
    assert f"recordSeedExponent = record{side}SeedTailPrefix463 := by\n  rfl" in facade


def test_group_and_checkpoint_boundaries(renderer: ModuleType) -> None:
    later = renderer.render_assembly_group("upper-seed", 0, 463, "test", 2)
    assert "Assembly.Part01" in later
    assert "Chunk041Before =\n        recordUpperSeedTailChunk040State" in later
    assert "boundary.trans recordUpperSeedTailGroup01_semantic" in later
    checkpoint = renderer.render_assembly_group("lower-seed", 3, 43, "test", 1)
    assert "Chunk004Before =\n        recordLowerSeedChunk003State" in checkpoint
    assert "boundary.trans h003" in checkpoint


@pytest.mark.parametrize("side", ["Lower", "Upper"])
def test_committed_assemblies_match_the_generator(renderer: ModuleType, side: str) -> None:
    task = f"{side.lower()}-seed"
    paths = sorted((GENERATED / f"RecordTwin{side}SeedTail/Assembly").glob("Part*.lean"))
    assert len(paths) == 12
    for group, path in enumerate(paths, 1):
        source = path.read_text()
        note = re.search(r"/-! (.+) Semantic tail assembly group \d+\. -/", source)
        assert note is not None
        assert source == renderer.render_assembly_group(task, 0, 463, note[1], group)
