import argparse
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument(
    "--dependency",
    type=Path,
    default=Path(".lake/packages/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/MediumPNT.lean"),
)
parser.add_argument(
    "--output",
    type=Path,
    default=Path("PrimeFactorUnimodality/Helpers/Analytic/ExplicitMediumPNT.lean"),
)
args = parser.parse_args()
dependency = args.dependency
target = args.output
source = dependency.read_text()
start = source.index("theorem MediumPNT :")
body = source[start:]
body = body.replace("theorem MediumPNT :", "theorem explicitMediumPNT :", 1)
body = body.replace(
    "obtain ⟨A, C_bnd, C_bnd_pos, A_in_Ioc, zeta_bnd, holo1⟩ := "
    "LogDerivZetaBoundedAndHolo",
    "obtain ⟨A, C_bnd, C_bnd_pos, A_in_Ioc, zeta_bnd, holo1⟩ := "
    "zetaLogDeriv_explicit_bounded_and_holo",
    1,
)
if "LogDerivZetaBoundedAndHolo" in body:
    raise RuntimeError("the generated proof still uses the package bound")
if "zetaLogDeriv_explicit_bounded_and_holo" not in body:
    raise RuntimeError("explicit zeta input was not inserted")
header = """import PrimeFactorUnimodality.Helpers.Analytic.ZetaExplicitBounds
import PrimeNumberTheoremAnd.MediumPNT

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace PrimeFactorUnimodality

noncomputable section

open Set Function Filter Complex Real
open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin
local notation "Λ" => vonMangoldt
local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ

"""
footer = "\nend\nend PrimeFactorUnimodality\n"
target.write_text(header + body + footer)
