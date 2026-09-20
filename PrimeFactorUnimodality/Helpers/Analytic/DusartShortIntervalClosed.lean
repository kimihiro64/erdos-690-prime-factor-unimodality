import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows
import PrimeFactorUnimodality.Helpers.Analytic.MediumPNT

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

/-! The first log-cubed rows extend the finite prefix through `89890`. -/
theorem wangCrapis_logCubedPrefix :
    HasLogCubedShortIntervalPrimeBelow (89890 : Real) := by
  exact hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows
    finitePrimeGapLogRows_89693_89890_cover

theorem wangCrapis_shortIntervalPrefix_89890 :
    HasDusartShortIntervalPrimeBelow (89890 : Real) := by
  exact hasDusartShortIntervalPrimeBelow_of_finite_gap_log_rows
    (by norm_num) wangCrapis_shortIntervalPrefix
    finitePrimeGapLogRows_89693_89890_cover

/-! Once the log-cubed tail is proved directly, this is the exact final
short-interval assembly.  Keeping the tail as an explicit argument makes the
remaining analytic obligation visible rather than smuggling it in through a
Dusart theorem with hidden axioms. -/
theorem wangCrapis_shortInterval_of_logCubedTail
    (tail : HasLogCubedShortIntervalPrime) :
    HasDusartShortIntervalPrime := by
  exact hasDusartShortIntervalPrime_of_below_and_logCubed
    wangCrapis_shortIntervalPrefix tail

/-! Selected-cutoff form used by the split all-`k` assembly. -/
theorem wangCrapis_shortInterval_of_selected_cutoff
    {A X : Real} (hXcutoff : (89693 : Real) ≤ X)
    (finite : HasLogCubedShortIntervalPrimeBelow X)
    (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hlogX : (10 : Real) < Real.log X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A X) :
    HasDusartShortIntervalPrime := by
  apply wangCrapis_shortInterval_of_logCubedTail
  apply hasLogCubedShortIntervalPrime_of_below_and_above hXcutoff finite
  apply wangCrapis_logCubedTail_of_thetaLogFourthError
    hXpos h2X hlogX hA_nonneg hA
  intro x hx
  exact thetaError x hx

/-! Source-level all-range assembly.  The finite argument is intentionally
quantified over the eventual cutoff selected by the medium-PNT proof; this
keeps the analytic theorem honest while allowing the compact certificate
provider to choose its own reusable row partition. -/
theorem wangCrapis_shortInterval_of_mediumPNT
    (finite : ∀ X : Real, (89693 : Real) ≤ X →
      HasLogCubedShortIntervalPrimeBelow X) :
    HasDusartShortIntervalPrime := by
  apply wangCrapis_shortInterval_of_logCubedTail
  exact hasLogCubedShortIntervalPrime_of_finite_and_mediumPNT
    (X₀ := (89693 : Real)) (by norm_num) finite

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
