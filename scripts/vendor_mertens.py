#!/usr/bin/env python3
"""Vendor the proved Mertens file while removing documentation attributes."""

from pathlib import Path

SOURCE = Path(
    "/home/ubuntu/research/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/IEANTN/Mertens.lean"
)
TARGET = Path("VendorPrimeNumberTheoremAnd/Mertens.lean")

header = """/-
Ported from the local PrimeNumberTheoremAnd repository (Apache-2.0).
Blueprint-only metadata is removed and the Euler--Maclaurin import is
redirected to the vendored module. Mathematical proof bodies are unchanged.
-/

"""


def strip_blueprint_attributes(source: str) -> str:
    """Remove `@[blueprint ...]` using a small Lean-aware lexical scan.

    Blueprint attributes occur both as short string-only attributes (ending
    in `"]`) and as longer parenthesized attributes (ending in `)]`).  A
    line-oriented remover silently swallowed declarations following the
    former.  Track the outer square bracket while ignoring brackets in Lean
    strings and nested block comments instead.
    """
    out: list[str] = []
    cursor = 0
    while True:
        start = source.find("@[blueprint", cursor)
        if start < 0:
            out.append(source[cursor:])
            return "".join(out)
        out.append(source[cursor:start])
        index = start + 2
        square_depth = 1
        block_depth = 0
        in_string = False
        escaped = False
        while index < len(source) and square_depth:
            pair = source[index : index + 2]
            char = source[index]
            if block_depth:
                if pair == "/-":
                    block_depth += 1
                    index += 2
                    continue
                if pair == "-/":
                    block_depth -= 1
                    index += 2
                    continue
            elif in_string:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
            elif pair == "/-":
                block_depth = 1
                index += 2
                continue
            elif char == '"':
                in_string = True
            elif char == "[":
                square_depth += 1
            elif char == "]":
                square_depth -= 1
            index += 1
        cursor = index


result: list[str] = []
source = strip_blueprint_attributes(SOURCE.read_text())
for line in source.splitlines(keepends=True):
    if line.startswith("blueprint_comment /--"):
        line = line.replace("blueprint_comment /--", "/-!", 1)
    if line == "import Architect\n":
        continue
    if line == "import PrimeNumberTheoremAnd.EulerMaclaurin\n":
        line = "import VendorPrimeNumberTheoremAnd.EulerMaclaurin\n"
    result.append(line)

generated = "".join(result)
# Lean 4.34's `simp` closes this compatibility subgoal outright; in the
# sibling project's older toolchain the following `rfl` was still needed.
generated = generated.replace(
    "    simp\n    rfl\n  · exact fun _ _ ↦ (by positivity)\n",
    "    simp\n  · exact fun _ _ ↦ (by positivity)\n",
)
TARGET.write_text(header + generated)
