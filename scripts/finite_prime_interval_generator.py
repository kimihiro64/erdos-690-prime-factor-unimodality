"""Shared data extraction and certificate formatting for the row generator."""

from __future__ import annotations

import re
import subprocess
from pathlib import Path


def factor_nat(n: int) -> list[int]:
    factors: list[int] = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors


def pocklington_data(n: int) -> str:
    """Emit one compact Pocklington data literal for a witness."""
    factors = factor_nat(n - 1)
    base = next(
        a
        for a in range(2, n)
        if pow(a, n - 1, n) == 1
        and all(pow(a, (n - 1) // q, n) != 1 for q in set(factors))
    )
    inverses = {
        q: pow((pow(base, (n - 1) // q, n) - 1) % n, -1, n)
        for q in set(factors)
    }
    residues = ", ".join(f"({q}, {inverses[q]})" for q in dict.fromkeys(factors))
    return (
        f"{{ n := {n}, F := {n - 1}, R := 1, a := {base}, "
        f"factors := [{', '.join(map(str, factors))}], "
        f"residues := [{residues}] }}"
    )


def prime_certificates(rows: list[str], data_name: str, accessor_name: str) -> str:
    witnesses = sorted({int(q) for row in rows for q in re.findall(r"\(q := (\d+)\)", row)})
    data = ",\n    ".join(pocklington_data(q) for q in witnesses)
    body = [
        "set_option maxRecDepth 1000000 in",
        "set_option maxHeartbeats 20000000 in",
        f"def {data_name} : List PocklingtonData := [",
        f"    {data}",
        "  ]",
        "",
        "set_option maxRecDepth 1000000 in",
        "set_option maxHeartbeats 20000000 in",
        f"theorem {data_name}_valid : PocklingtonRow.Valid {data_name} := by",
        "  apply PocklingtonRow.valid_of_decide_all",
        "  decide",
        "",
        f"theorem {accessor_name} (i : Fin {data_name}.length) :",
        f"    Nat.Prime ({data_name}.get i).n := by",
        f"  exact PocklingtonRow.prime_of_mem {data_name}_valid (List.get_mem _ _)",
        "",
    ]
    return "\n".join(body)


def source_text(repo: Path, revision: str, source_path: str) -> str:
    return subprocess.check_output(
        ["git", "show", f"{revision}:{source_path}"], cwd=repo, text=True
    )


def extract(text: str, start: str, end: str) -> str:
    start_at = text.index(start)
    end_at = text.index(end, start_at)
    return text[start_at:end_at]


def normalize(body: str) -> str:
    """Apply the source repairs required by the split module API."""
    lines = []
    for line in body.splitlines(keepends=True):
        if "dusartPrimeRow_of_explicit_" in line and "(q := " in line:
            count = len(re.findall(r"\(by (?:norm_num|decide|omega)\)", line))
            if count == 4:
                stripped = line.rstrip()
                if stripped.endswith(","):
                    close = line.rfind(",")
                elif stripped.endswith(")]"):
                    close = line.rfind("]")
                elif stripped.endswith("))"):
                    close = line.rfind(")")
                else:
                    close = len(line.rstrip("\n"))
                line = line[:close] + " (by norm_num)" + line[close:]
            line = re.sub(
                r"(\(q := \d+\)) \(by norm_num\)",
                r"\1 (by decide)",
                line,
                count=1,
            )
        lines.append(line)
    body = "".join(lines)
    body = body.replace(
        """  | empty h =>
      intro x hleft hright
      exfalso
      norm_num at h
      linarith""",
        """  | @empty a b h =>
      intro x hleft hright
      exfalso
      have hab : (b : Real) + 1 ≤ a := by
        exact_mod_cast Nat.succ_le_of_lt h
      linarith""",
    )
    body = body.replace(
        "exact DusartPrimeRowsChain.cons row (by omega) hordered ih",
        "exact DusartPrimeRowsChain.cons row (by omega) hordered htail",
    )
    return re.sub(
        r"(?m)^(def dusartPrimeRows_|theorem dusartPrimeRows_)",
        "set_option maxHeartbeats 20000000 in\n\\1",
        body,
    )
