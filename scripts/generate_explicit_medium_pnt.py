from pathlib import Path

dependency = Path(
    "/home/ubuntu/research/erdos-690-prime-factor-unimodality/.lake/packages/"
    "PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/MediumPNT.lean"
)
target = Path(
    "PrimeFactorUnimodality/Helpers/Analytic/ExplicitMediumPNT.lean"
)
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
