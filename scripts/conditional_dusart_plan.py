"""Dependency-ordered, content-addressed units for the conditional all-k proof."""

from __future__ import annotations

import hashlib
import json
import platform
from dataclasses import dataclass
from pathlib import Path

from scripts.lean_source import lean_imports, strip_lean_comments

TARGET = "PrimeFactorUnimodality.Proof.CompleteClassificationSquaredConditional"
THEOREM = "PrimeFactorUnimodality.completeClassification_assuming_theta_error"
# These proved reductions are needed only by the one-theta conditional target.
# Keep the broad exclusion for every other unfinished Dusart provider.
THETA_DUSART_IMPORTS = {
    f"PrimeFactorUnimodality.Helpers.Analytic.{name}"
    for name in (
        "DusartJBounds",
        "DusartJComparison",
        "DusartTwoTermComparison",
        "DusartPrimeCountingSquared",
        "DusartShortIntervalSquared",
        "DusartSquaredAtPublishedCutoff",
        "DusartPublishedAnchors",
        "DusartPrimeCountingClosed",
        "DusartPublishedPrimeCounting",
        "DusartPublishedShortInterval",
        "DusartPublishedTailTheta",
    )
}
CONFIG = (
    "lean-toolchain",
    "lake-manifest.json",
    "lakefile.toml",
    "scripts/patch_pnt_compat.py",
    "scripts/patch_primecert_compat.py",
)
FORBIDDEN = (
    "PrimeFactorUnimodality.Helpers.Analytic.Dusart",
    "PrimeFactorUnimodality.Helpers.Analytic.Xi",
    "PrimeFactorUnimodality.Proof.Analytic.WangCrapisClosed",
    "PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCompact",
    "PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordPrimeWitnesses",
    "PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordReciprocalBlocks",
    "PrimeFactorUnimodality.Proof.LargeRange.RecordReciprocalCertificate",
)
ARTIFACT_SUFFIXES = (
    ".olean",
    ".olean.private",
    ".olean.server",
    ".ilean",
    ".ir",
    ".ir.sig",
    ".trace",
)


@dataclass(frozen=True)
class Unit:
    modules: tuple[str, ...]
    key: str
    phase: str

    @property
    def asset(self) -> str:
        return f"conditional-{self.key}.tar.gz"


def owned_plan(root: Path, target: str = TARGET) -> tuple[list[str], dict[str, list[str]]]:
    """Topologically order every owned import; never build the library facade."""
    ordered: list[str] = []
    imports: dict[str, list[str]] = {}
    visiting: set[str] = set()

    def visit(module: str) -> None:
        allowed = target == TARGET and module in THETA_DUSART_IMPORTS
        if module.startswith(FORBIDDEN) and not allowed:
            raise ValueError(f"unfinished or retired dependency in conditional target: {module}")
        path = root.joinpath(*module.split(".")).with_suffix(".lean")
        if not path.is_file():
            if module.startswith(("PrimeFactorUnimodality", "VendorPrimeNumberTheoremAnd")):
                raise ValueError(f"missing owned source: {module}")
            return
        if module in visiting:
            raise ValueError(f"import cycle: {module}")
        if module in imports:
            return
        visiting.add(module)
        direct = sorted(lean_imports(strip_lean_comments(path.read_text())))
        for dependency in direct:
            visit(dependency)
        visiting.remove(module)
        imports[module] = direct
        ordered.append(module)

    visit(target)
    return ordered, imports


def plan(root: Path, size: int = 16) -> list[Unit]:
    """Merkle keys include actual transitive source and locked build configuration.

    No commit SHA, unrelated source, or timestamp participates. A changed
    imported proof invalidates its consumers, not independent completed units.
    """
    if size < 1:
        raise ValueError("unit size must be positive")
    ordered, imports = owned_plan(root)
    config = hashlib.sha256(b"conditional-archive-v1")
    config.update(f"{platform.system()}-{platform.machine()}".encode())
    for name in CONFIG:
        config.update(name.encode() + b"\0" + (root / name).read_bytes())
    seed = config.digest()
    keys: dict[str, str] = {}
    heavy: dict[str, bool] = {}
    for module in ordered:
        source = root.joinpath(*module.split(".")).with_suffix(".lean").read_bytes()
        digest = hashlib.sha256(seed + module.encode() + b"\0" + source)
        for dependency in imports[module]:
            digest.update(dependency.encode() + b"\0" + keys.get(dependency, "locked").encode())
        keys[module] = digest.hexdigest()
        heavy[module] = (
            ".Generated." in module
            or ".FiniteCertificates." in module
            or any(heavy.get(dependency, False) for dependency in imports[module])
        )
    units: list[Unit] = []
    for phase in ("foundations", "certificates"):
        modules = [m for m in ordered if heavy[m] == (phase == "certificates")]
        for index in range(0, len(modules), size):
            chunk = tuple(modules[index : index + size])
            payload = json.dumps([(m, keys[m]) for m in chunk], separators=(",", ":"))
            units.append(Unit(chunk, hashlib.sha256(payload.encode()).hexdigest(), phase))
    return units


def artifact_paths(unit: Unit) -> list[Path]:
    """Only regular Lean artifacts belonging to this exact unit may be restored."""
    base = Path(".lake/build/lib/lean")
    files = [
        Path(str(base.joinpath(*module.split("."))) + suffix)
        for module in unit.modules
        for suffix in ARTIFACT_SUFFIXES
    ]
    files += [
        Path(str(Path(".lake/build/ir").joinpath(*module.split("."))) + suffix)
        for module in unit.modules
        for suffix in (".c", ".bc", ".setup.json")
    ]
    return files + [Path(str(path) + ".hash") for path in files]


def required_artifacts(unit: Unit) -> set[Path]:
    """Lake checks the C output as well as oleans even for Lean-only builds."""
    return {
        path for path in artifact_paths(unit) if path.suffix in {".olean", ".ilean", ".trace", ".c"}
    }
