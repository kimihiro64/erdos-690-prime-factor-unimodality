import PrimeFactorUnimodality.Helpers.Analytic.XiZeroExhaustion

/-! # Missing divisor labels persist and force an integral discrepancy

Subtract a fixed finite witness set from the actual closed positive-height
divisor. The missing count is a nondecreasing integer-valued function, so
one omitted label at the lower cutoff contributes at least the full interval
width to its integral. This is the completeness implication used in Turing's
method; no quantitative integral bound or numerical witness is asserted.
See Trudgian, https://arxiv.org/abs/0903.1885, Section 1.1.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Finset MeasureTheory

local instance xiMissingCountDecidableEq : DecidableEq RiemannXiDivisorZeroIndex := Classical.decEq _

/-- Omitted positive-height labels, including all multiplicities at the closed cutoff. -/
def xiMissingCount (S : Finset RiemannXiDivisorZeroIndex) (t : ℝ) : ℕ :=
  (xiPositiveHeightIndices t \ S).card

/-- An omitted label remains omitted at every higher cutoff. -/
theorem xiMissingCount_mono (S : Finset RiemannXiDivisorZeroIndex) :
    Monotone (xiMissingCount S) := by
  intro t u htu
  apply card_le_card
  intro p hp
  rw [mem_sdiff] at hp ⊢
  exact ⟨xiPositiveHeightIndices_mono htu hp.1, hp.2⟩

/-- Observed and missing labels partition the full multiplicity count exactly. -/
theorem xiMissingCount_add_observed (S : Finset RiemannXiDivisorZeroIndex) (t : ℝ) :
    xiMissingCount S t + ((xiPositiveHeightIndices t) ∩ S).card = xiZeroCount t :=
  card_sdiff_add_card_inter (xiPositiveHeightIndices t) S

/-- The actual closed counting function is integrable on every finite interval. -/
theorem intervalIntegrable_xiZeroCount (a b : ℝ) :
    IntervalIntegrable (fun t => (xiZeroCount t : ℝ)) volume a b := by
  have h : Monotone (fun t => (xiZeroCount t : ℝ)) := by
    intro t u htu
    change ((xiPositiveHeightIndices t).card : ℝ) ≤ (xiPositiveHeightIndices u).card
    exact_mod_cast card_le_card (xiPositiveHeightIndices_mono htu)
  exact h.intervalIntegrable

/-- Monotonicity gives finite-interval integrability without choosing zero-free endpoints. -/
theorem xiMissingCount_intervalIntegrable (S : Finset RiemannXiDivisorZeroIndex) (a b : ℝ) :
    IntervalIntegrable (fun t => (xiMissingCount S t : ℝ)) volume a b := by
  have h : Monotone (fun t => (xiMissingCount S t : ℝ)) := by
    intro t u htu
    change (xiMissingCount S t : ℝ) ≤ (xiMissingCount S u : ℝ)
    exact_mod_cast xiMissingCount_mono S htu
  exact h.intervalIntegrable

/-- An integral smaller than the interval width excludes every omitted lower-cutoff label. -/
theorem xiMissingCount_zero_of_integral_lt (S : Finset RiemannXiDivisorZeroIndex)
    {a b : ℝ} (hab : a ≤ b)
    (hbudget : (∫ t in a..b, (xiMissingCount S t : ℝ)) < b - a) : xiMissingCount S a = 0 := by
  by_contra hn
  have hpos : 1 ≤ xiMissingCount S a := Nat.one_le_iff_ne_zero.mpr hn
  have hcomp := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b)
    (xiMissingCount_intervalIntegrable S a b) (fun t ht => show (1 : ℝ) ≤ xiMissingCount S t from
      by exact_mod_cast hpos.trans (xiMissingCount_mono S ht.1))
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hcomp
  exact hbudget.not_ge hcomp

/-- A vanishing missing count is precisely complete coverage at the closed cutoff. -/
theorem xiMissingCount_eq_zero_iff (S : Finset RiemannXiDivisorZeroIndex) (t : ℝ) :
    xiMissingCount S t = 0 ↔ xiPositiveHeightIndices t ⊆ S := by
  simp only [xiMissingCount, card_eq_zero, sdiff_eq_empty_iff_subset]

/-- Integral verification of critical witnesses supplies the strict low-height condition. -/
theorem xiLow_criticalLine_of_missing_integral {S : Finset RiemannXiDivisorZeroIndex}
    {a b : ℝ} (hab : a ≤ b)
    (hline : ∀ p ∈ S, (riemannXiDivisorZeroValue p).re = 1 / 2)
    (hbudget : (∫ t in a..b, (xiMissingCount S t : ℝ)) < b - a) :
    ∀ p ∈ xiLowHeightIndices a, (riemannXiDivisorZeroValue p).re = 1 / 2 := by
  have hcover := (xiMissingCount_eq_zero_iff S a).mp
    (xiMissingCount_zero_of_integral_lt S hab hbudget)
  apply xiLow_criticalLine_of_positive
  intro p hp
  have hm := (mem_xiStrictPositiveHeightIndices a p).mp hp
  exact hline p (hcover ((mem_xiPositiveHeightIndices a p).mpr ⟨hm.1, hm.2.le⟩))

end

end PrimeFactorUnimodality
