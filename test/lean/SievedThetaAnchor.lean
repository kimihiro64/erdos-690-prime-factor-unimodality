import PrimeFactorUnimodality.Helpers.Analytic.SievedThetaAnchor

/-! # A complete sieve-to-theta anchor with no numerical hypotheses -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

open PrimeCert.Sieve ThetaPrimeCheckpoint

private theorem sieve30 : IsSieve 30 766 :=
  isSieve_of_sieveK_eq (sqrtN := 6) (by decide +kernel) (by decide) (by decide)

private def rows : List SieveProductRow := [⟨4, 2, 5005⟩, ⟨5, 3, 215441⟩]
private def config : SharedTaylorIntervals := SharedTaylorIntervals.prepare 40
private def atThirty : ThetaPrimeCheckpoint :=
  ⟨30, 10, ⟨22590 / 1000, 22591 / 1000, by norm_num⟩,
    ⟨3401 / 1000, 3402 / 1000, by norm_num⟩⟩

private theorem anchor : atThirty.Valid :=
  valid_of_sieve_product_checks sieve30 (SharedTaylorIntervals.prepare_prepared 40)
    (k := 4) (rows := rows) (product := 6469693230) (by decide)
    (by decide +kernel) (by decide +kernel) ⟨6469693230, 6469693231, 0⟩
    (by decide +kernel) (by decide +kernel)

example : Nat.primeCounting 30 = 10 := anchor.2.1
example : Chebyshev.theta 30 ∈ atThirty.theta := anchor.2.2.1
example : Real.log 30 ∈ atThirty.log := anchor.2.2.2

end PrimeFactorUnimodality.Tests
