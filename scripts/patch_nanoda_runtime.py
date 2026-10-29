"""Preserve the pinned NanoDa checker while adding timing and bounded worker stacks."""

from __future__ import annotations

import argparse
import hashlib
import shutil
import subprocess
from pathlib import Path

PIN = "68d5ca9db226849b41a6fff59d796ff19d0a8840"
SOURCE_SHA256: dict[str, str] = {
    "src/main.rs": "245ceaef34e8925cacaa3c5b99ce096a8c744710ce1f9184423e5a0333e8b35a",
    "src/parser.rs": "22b17bd188152fb3ded36a060fc1ade5e064aef7cc411aecf64c5730c40ea3e2",
    "src/tc.rs": "73f00401263871e533eb0f2cfa38162866204ee3fe7e7dd146755c5690f0b696",
    "src/lib.rs": "ca7a3ba8754a06ee08c85fbc5af9debdefc372629c50b02142bdc8aad55cb69e",
}

REPLACEMENTS: dict[str, tuple[tuple[str, str], ...]] = {
    "src/main.rs": (
        (
            (
                "    let (export_file, skipped_axioms) = cfg.to_export_file()?;\n  "
                "  // Check the environment\n    export_file.check_all_declars();"
            ),
            (
                "    let profile_started = std::time::Instant::now();\n    eprintln"
                '!("NANODA_PARSE_START");\n    let (export_file, skipped_axioms) = '
                'cfg.to_export_file()?;\n    eprintln!("NANODA_PARSE_DONE seconds={'
                '} declarations={}", profile_started.elapsed().as_secs_f64(), expo'
                "rt_file.declars.len());\n    // Check the environment\n    let prof"
                "ile_check_started = std::time::Instant::now();\n    export_file.ch"
                'eck_all_declars();\n    eprintln!("NANODA_CHECK_DONE seconds={}", '
                "profile_check_started.elapsed().as_secs_f64());"
            ),
        ),
    ),
    "src/parser.rs": (
        (
            ("        parser.line_num += 1;\n        line_buffer.clear();"),
            (
                "        parser.line_num += 1;\n        if parser.line_num % 1_000_"
                '000 == 0 {\n            eprintln!("NANODA_PARSE_LINES lines={} exp'
                'ressions={}", parser.line_num, parser.dag.exprs.len());\n        }'
                "\n        line_buffer.clear();"
            ),
        ),
        (
            ("    let name_cache = parser.dag.mk_name_cache();"),
            (
                '    eprintln!("NANODA_INPUT_DONE lines={} expressions={} declarat'
                'ions={}", parser.line_num, parser.dag.exprs.len(), parser.declars'
                ".len());\n    let profile_name_cache_started = std::time::Instant:"
                ":now();\n    let name_cache = parser.dag.mk_name_cache();\n    epri"
                'ntln!("NANODA_NAME_CACHE_DONE seconds={}", profile_name_cache_sta'
                "rted.elapsed().as_secs_f64());"
            ),
        ),
    ),
    "src/tc.rs": (
        (
            (
                "    pub(crate) fn check_all_declars_serial(&self) {\n        for d"
                "eclar in self.declars.values() {\n            self.check_declar(de"
                "clar);\n        }\n    }"
            ),
            (
                "    pub(crate) fn check_all_declars_serial(&self) {\n        for ("
                "index, declar) in self.declars.values().enumerate() {\n           "
                " let profile_name_idx = declar.info().name.idx;\n            eprin"
                'tln!("NANODA_DECL_START index={} name_id={}", index, profile_name'
                "_idx);\n            let profile_started = std::time::Instant::now("
                ');\n            self.check_declar(declar);\n            eprintln!("'
                'NANODA_DECL_END index={} name_id={} seconds={}", index, profile_n'
                "ame_idx, profile_started.elapsed().as_secs_f64());\n        }\n    "
                "}"
            ),
        ),
        (
            (
                "                            if let Some((_, declar)) = self.decla"
                "rs.get_index(idx) {\n                                self.check_de"
                "clar(declar);"
            ),
            (
                "                            if let Some((_, declar)) = self.decla"
                "rs.get_index(idx) {\n                                let profile_n"
                "ame_idx = declar.info().name.idx;\n                               "
                ' eprintln!("NANODA_DECL_START index={} name_id={}", idx, profile_'
                "name_idx);\n                                let profile_started = "
                "std::time::Instant::now();\n                                self.c"
                'heck_declar(declar);\n                                eprintln!("N'
                'ANODA_DECL_END index={} name_id={} seconds={}", idx, profile_name'
                "_idx, profile_started.elapsed().as_secs_f64());"
            ),
        ),
    ),
    "src/lib.rs": (
        (
            ("pub(crate) const STACK_SIZE: usize = 16_777_216;"),
            ("pub(crate) const STACK_SIZE: usize = 268_435_456;"),
        ),
    ),
}


def digest(source: str) -> str:
    return hashlib.sha256(source.encode("utf-8")).hexdigest()


def rewrite_source(
    source: str, expected_digest: str, replacements: tuple[tuple[str, str], ...]
) -> tuple[str, bool]:
    """Only accept the full pinned file or this exact reversible runtime port."""
    source = source.replace("\r\n", "\n")
    if digest(source) == expected_digest:
        result = source
        for before, after in replacements:
            if result.count(before) != 1:
                raise ValueError("NanoDa runtime anchor is not unique")
            result = result.replace(before, after, 1)
        return result, True
    recovered = source
    for before, after in reversed(replacements):
        if recovered.count(after) != 1:
            raise ValueError("NanoDa source differs from the pinned checker/runtime port")
        recovered = recovered.replace(after, before, 1)
    if digest(recovered) != expected_digest:
        raise ValueError("NanoDa source changed beneath the checked runtime port")
    return source, False


def patch(root: Path) -> bool:
    root = root.resolve(strict=True)
    git = shutil.which("git")
    if git is None or not Path(git).is_file():
        raise ValueError("A resolved Git executable is required")
    head = subprocess.check_output([git, "-C", str(root), "rev-parse", "HEAD"], text=True)
    inventory = subprocess.check_output([git, "-C", str(root), "ls-files"], text=True)
    paths = inventory.splitlines()
    if head.strip() != PIN:
        raise ValueError("NanoDa revision differs from the reviewed pin")
    planned: list[tuple[Path, str]] = []
    for relative, expected_digest in SOURCE_SHA256.items():
        if paths.count(relative) != 1:
            raise ValueError(f"NanoDa tracked path is not unique: {relative}")
        path = root / relative
        if not path.is_file() or path.is_symlink():
            raise ValueError(f"NanoDa source must be a regular file: {relative}")
        result, changed = rewrite_source(
            path.read_text(encoding="utf-8"), expected_digest, REPLACEMENTS[relative]
        )
        if changed:
            planned.append((path, result))
    for path, result in planned:
        path.write_text(result, encoding="utf-8", newline="\n")
    return bool(planned)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    args = parser.parse_args()
    changed = patch(args.root)
    print("NanoDa timing and 256 MiB worker stacks " + ("applied" if changed else "verified"))


if __name__ == "__main__":
    main()
