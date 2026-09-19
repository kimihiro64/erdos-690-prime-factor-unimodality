import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-!
# Closed explicit short-interval estimate

Implementation owner: Luna.

This module must prove and export
`PrimeFactorUnimodality.wangCrapis_shortInterval : HasDusartShortIntervalPrime`.
Use the compact, kernel-checked prefix through `89693` and the closed explicit
theta estimate above that point.  Any additional bounded data must use indexed
rows and reusable assemblers, never one generated theorem file per witness.

The exact proof obligations and dependency order are recorded in
`LEAN_COMPLETION_HANDOFF.md`.  The finite prefix below is closed now; the
remaining global provider still needs the independently proved tail estimate.
-/

/-! This is the reusable finite prefix, not the global provider.  Its proof
comes from the compact row assembler in `FinitePrimeIntervalRows`, so it does
not introduce an assumption or a hidden theorem. -/
theorem wangCrapis_shortIntervalPrefix :
    HasDusartShortIntervalPrimeBelow (89693 : Real) := by
  exact hasDusartShortIntervalPrimeBelow_3275_89693

/-! Once the log-cubed tail is proved directly, this is the exact final
short-interval assembly.  Keeping the tail as an explicit argument makes the
remaining analytic obligation visible rather than smuggling it in through a
Dusart theorem with hidden axioms. -/
theorem wangCrapis_shortInterval_of_logCubedTail
    (tail : HasLogCubedShortIntervalPrime) :
    HasDusartShortIntervalPrime := by
  exact hasDusartShortIntervalPrime_of_below_and_logCubed
    wangCrapis_shortIntervalPrefix tail

/-! Closed analytic tail adapter.  The remaining fixed-cutoff work is to
construct its `HasThetaLogFourthError` input and the explicit endpoint
coverage; this theorem records the exact conversion without importing
Dusart's proposition. -/
theorem wangCrapis_logCubedTail_of_thetaLogFourthError
    {A X : Real} (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hlogX : (10 : Real) < Real.log X) (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    ∀ x : Real, X ≤ x →
      ∃ q : Nat, q.Prime ∧ x < q ∧
        (q : Real) ≤ x + x / (Real.log x) ^ 3 := by
  intro x hx
  obtain ⟨q, hq, hxq, hupper⟩ :=
    dusartPrimeInInterval_of_logFourthError_from
      hXpos h2X hlogX hA_nonneg hA thetaError x hx
  refine ⟨q, hq, hxq, ?_⟩
  calc
    (q : Real) ≤ x * (1 + 1 / (Real.log x) ^ 3) := hupper
    _ = x + x / (Real.log x) ^ 3 := by ring

end

end PrimeFactorUnimodality
