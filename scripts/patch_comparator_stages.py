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
LEGACY_STAGED_SHA256 = "6fe7dbea26bccb9ab82167346159829e2ff4b3f5f698b68688300e5b4928b23a"
NAMESPACE_END = "\nend Comparator\n"
OLD_DISPATCH = "  Comparator.M.run Comparator.compareIt config\n"
NEW_DISPATCH = """  match args[1]? with
  | none => Comparator.M.run Comparator.compareIt config
  | some phase => Comparator.M.run (Comparator.staged phase) config
"""
STAGES = r"""
def runNanodaPrepared (solutionPath : System.FilePath) : M Unit := do
  IO.println "Running nanoda kernel on solution with 4 workers"
  IO.FS.withTempFile fun config configPath => do
    let legalAxioms <- getLegalAxioms
    config.putStr <| Lean.Json.compress <| Lean.Json.mkObj [
      ("use_stdin", false),
      ("export_file_path", .str solutionPath.toString),
      ("num_threads", Lean.toJson (4 : Nat)),
      ("permitted_axioms", .arr <| legalAxioms.map (fun n => .str n.toString)),
      ("unpermitted_axiom_hard_error", true),
      ("nat_extension", true),
      ("string_extension", true),
    ]
    config.flush
    let spawnArgs := {
      cmd := (<- read).whichNanoda
      args := #[configPath.toString]
      envPass := #[]
      readablePaths := #[configPath.toString, solutionPath.toString]
      writablePaths := #[]
      executablePaths := #[]
    }
    let proc <- IO.Process.spawn {
      cmd := (<- read).whichLandrun
      args := buildLandrunArgs spawnArgs
      env := spawnArgs.envOverride
      cwd := (<- getProjectDir)
    }
    let ret <- proc.wait
    unless ret == 0 do
      throw <| IO.userError s!"Child exited with {ret}"
    IO.println "Nanoda kernel accepts the solution"
def readPrepared (path : System.FilePath) : M Export.ExportedEnv := do
  let started <- IO.monoMsNow
  let text <- IO.FS.readFile path
  let loaded <- IO.monoMsNow
  IO.eprintln s!"Export read {path}: {text.utf8ByteSize} bytes in {loaded - started} ms"
  let result <- Export.parseStream (<- stringStream text)
  let parsed <- IO.monoMsNow
  IO.eprintln s!"Export parsed {path}: {parsed - loaded} ms"
  return result

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
  | "match-axioms" =>
    let challenge <- readPrepared challengePath
    let solution <- readPrepared solutionPath
    let targets := (<- getTheoremNames) ++ (<- getLegalAxioms)
    let started <- IO.monoMsNow
    IO.ofExcept <| Comparator.compareAt challenge solution targets
      (<- getDefinitionNames) (<- primitiveTargets)
    let matched <- IO.monoMsNow
    IO.eprintln s!"Strict matching accepted: {matched - started} ms"
    IO.ofExcept <| Comparator.checkAxioms solution (<- getTheoremNames)
      (<- getDefinitionNames) (<- getLegalAxioms)
    let audited <- IO.monoMsNow
    IO.eprintln s!"Axiom inspection accepted: {audited - matched} ms"
  | "match" =>
    let challenge <- readPrepared challengePath
    let solution <- readPrepared solutionPath
    let targets := (<- getTheoremNames) ++ (<- getLegalAxioms)
    IO.ofExcept <| Comparator.compareAt challenge solution targets
      (<- getDefinitionNames) (<- primitiveTargets)
  | "axioms" =>
    let solution <- readPrepared solutionPath
    IO.ofExcept <| Comparator.checkAxioms solution (<- getTheoremNames)
      (<- getDefinitionNames) (<- getLegalAxioms)
  | "nanoda" =>
    unless <- getNanodaEnabled do
      throw <| IO.userError "NanoDa is required"
    IO.eprintln s!"NanoDa file input: {solutionPath}; 4 workers, 256 MiB stacks"
    runNanodaPrepared solutionPath
  | "kernel" =>
    let solution <- readPrepared solutionPath
    runKernel solution
  | _ => throw <| IO.userError s!"Unknown Comparator stage: {phase}"
  IO.eprintln s!"Comparator stage accepted: {phase}"
"""


def digest(source: str) -> str:
    return hashlib.sha256(source.encode("utf-8")).hexdigest()


def stage_source(source: str) -> tuple[str, bool]:
    """Accept only the reviewed upstream source or this exact CLI-only port."""
    source = source.replace("\r\n", "\n")
    if digest(source) == LEGACY_STAGED_SHA256:
        start = source.index("\ndef readPrepared")
        stop = source.index(NAMESPACE_END, start)
        source = source[:start] + source[stop:]
        source = source.replace(NEW_DISPATCH, OLD_DISPATCH, 1)
        if digest(source) != MAIN_SHA256:
            raise ValueError("Legacy Comparator orchestration did not recover the pin")
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
