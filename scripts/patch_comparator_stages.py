"""Expose pinned Comparator orchestration as separate native CI processes.

The existing comparison, axiom, NanoDa and kernel implementations stay byte-for-byte
unchanged. Only the CLI dispatch and additional orchestration are introduced.
"""

from __future__ import annotations

import argparse
import hashlib
import shutil
import subprocess
from pathlib import Path

PIN = "68a064109f01c08f47c8edc9f51d6a2bbffaa188"
MAIN_SHA256 = "602c1206dbb0545f83805c7bc77df0dd7bde26c8e797e89f9806581f8e321944"
NAMESPACE_END = "\nend Comparator\n"
OLD_DISPATCH = "  Comparator.M.run Comparator.compareIt config\n"
NEW_DISPATCH = """  match args[1]? with
  | none => Comparator.M.run Comparator.compareIt config
  | some phase => Comparator.M.run (Comparator.staged phase) config
"""
STAGES = r"""
def staged (phase : String) : M Unit := do
  let directory := System.FilePath.mk <|
    (<- IO.getEnv "COMPARATOR_STAGE_DIR").getD ".cache/palomar-comparator/exports"
  IO.FS.createDirAll directory
  let challengePath := directory / "challenge.export"
  let solutionPath := directory / "solution.export"
  IO.eprintln s!"Comparator stage starting: {phase}"
  match phase with
  | "export-challenge" =>
    let exportTargets := (<- builtinTargets) ++ (<- getTheoremNames) ++ (<- getLegalAxioms)
      ++ (<- primitiveTargets) ++ (<- getDefinitionNames)
    let module <- getChallengeModule
    safeLakeBuild module
    IO.FS.writeFile challengePath (<- safeExport module exportTargets)
  | "export-solution" =>
    let exportTargets := (<- builtinTargets) ++ (<- getTheoremNames) ++ (<- getLegalAxioms)
      ++ (<- primitiveTargets) ++ (<- getDefinitionNames)
    let module <- getSolutionModule
    safeLakeBuild module
    IO.FS.writeFile solutionPath (<- safeExport module exportTargets)
  | "match" =>
    let challengeText <- IO.FS.readFile challengePath
    let solutionText <- IO.FS.readFile solutionPath
    let challenge <- Export.parseStream (<- stringStream challengeText)
    let solution <- Export.parseStream (<- stringStream solutionText)
    let targets := (<- getTheoremNames) ++ (<- getLegalAxioms)
    IO.ofExcept <| Comparator.compareAt challenge solution targets
      (<- getDefinitionNames) (<- primitiveTargets)
  | "axioms" =>
    let solutionText <- IO.FS.readFile solutionPath
    let solution <- Export.parseStream (<- stringStream solutionText)
    IO.ofExcept <| Comparator.checkAxioms solution (<- getTheoremNames)
      (<- getDefinitionNames) (<- getLegalAxioms)
  | "nanoda" =>
    unless <- getNanodaEnabled do
      throw <| IO.userError "NanoDa is required"
    runNanoda (<- IO.FS.readFile solutionPath)
  | "kernel" =>
    let solutionText <- IO.FS.readFile solutionPath
    let solution <- Export.parseStream (<- stringStream solutionText)
    runKernel solution
  | _ => throw <| IO.userError s!"Unknown Comparator stage: {phase}"
  IO.eprintln s!"Comparator stage accepted: {phase}"
"""


def digest(source: str) -> str:
    return hashlib.sha256(source.encode("utf-8")).hexdigest()


def stage_source(source: str) -> tuple[str, bool]:
    """Accept only the reviewed upstream source or this exact CLI-only port."""
    source = source.replace("\r\n", "\n")
    if STAGES in source:
        if source.count(STAGES) != 1 or source.count(NEW_DISPATCH) != 1:
            raise ValueError("Comparator orchestration port is not unique")
        original = source.replace(STAGES, "", 1).replace(NEW_DISPATCH, OLD_DISPATCH, 1)
        if digest(original) != MAIN_SHA256:
            raise ValueError("Comparator checker source changed beneath the port")
        return source, False
    if digest(source) != MAIN_SHA256:
        raise ValueError("Comparator Main.lean differs from the reviewed pinned source")
    if source.count(NAMESPACE_END) != 1 or source.count(OLD_DISPATCH) != 1:
        raise ValueError("Comparator CLI anchors are not unique")
    result = source.replace(NAMESPACE_END, STAGES + NAMESPACE_END, 1)
    result = result.replace(OLD_DISPATCH, NEW_DISPATCH, 1)
    return result, True


def patch(root: Path) -> bool:
    root = root.resolve(strict=True)
    git_name = shutil.which("git")
    if git_name is None or not Path(git_name).is_file():
        raise ValueError("A resolved Git executable is required")
    head = subprocess.check_output(
        [git_name, "-C", str(root), "rev-parse", "HEAD"], text=True
    ).strip()
    tracked = subprocess.check_output(
        [git_name, "-C", str(root), "ls-files", "--error-unmatch", "--", "Main.lean"],
        text=True,
    ).splitlines()
    if head != PIN or tracked != ["Main.lean"]:
        raise ValueError("Comparator revision or tracked CLI path differs from the pin")
    path = root / tracked[0]
    if not path.is_file() or path.is_symlink():
        raise ValueError("Comparator CLI source must be a regular file")
    result, changed = stage_source(path.read_text(encoding="utf-8"))
    if changed:
        path.write_text(result, encoding="utf-8", newline="\n")
    return changed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    args = parser.parse_args()
    changed = patch(args.root)
    print("Comparator CLI stages " + ("applied" if changed else "already verified"))


if __name__ == "__main__":
    main()
