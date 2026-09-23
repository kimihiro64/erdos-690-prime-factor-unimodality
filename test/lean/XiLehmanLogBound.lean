import PrimeFactorUnimodality.Helpers.Analytic.XiLehmanAffine

/-! # Moderate-height Lehman bounds and exact cutoff handling

Exercise positive, negative, zero and arbitrary natural harmonics below the
former cutoff. No regular-height or critical-line hypothesis is supplied.
-/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real Set MeasureTheory

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H) (c : ℝ) :
    (∫ x in Ioi (t + H), (Real.log x - c) * reciprocalSquarePairSlope t x) =
      (Real.log (t + H) - c) * reciprocalSquarePair t (t + H) +
        ∫ x in Ioi (t + H), reciprocalSquarePair t x / x :=
  integral_log_sub_mul_reciprocalSquarePairSlope ht hH c

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H) :
    (∫ x in Ioi (t + H), (Real.log x + 17) * reciprocalSquarePairSlope t x) =
      (Real.log (t + H) + 17) * reciprocalSquarePair t (t + H) +
        ∫ x in Ioi (t + H), reciprocalSquarePair t x / x := by
  simpa only [sub_neg_eq_add] using
    integral_log_sub_mul_reciprocalSquarePairSlope ht hH (-17)

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H) (hA : 10 < t + H) :
    xiHeightTail t H ≤ xiLehmanLogBound t H := xiHeightTail_le_logBound ht hH hA

example : xiHeightTail 1 10 ≤ xiLehmanLogBound 1 10 :=
  xiHeightTail_le_logBound (by norm_num) (by norm_num) (by norm_num)

example : xiHeightTail 10 1 ≤ xiLehmanLogBound 10 1 :=
  xiHeightTail_le_logBound (by norm_num) (by norm_num) (by norm_num)

example : xiHeightTail (1 / 2) 10 ≤ xiLehmanLogBound (1 / 2) 10 :=
  xiHeightTail_le_logBound (by norm_num) (by norm_num) (by norm_num)

example : xiHeightTail (-1) 10 ≤ xiLehmanTailMajorant (-1) 10 :=
  xiHeightTail_le_lehmanMajorant (by norm_num) (fun _ => by norm_num)

example : xiHeightTail 0 1 ≤ xiLehmanTailMajorant 0 1 :=
  xiHeightTail_le_lehmanMajorant (by norm_num) (fun h => (h rfl).elim)

example {H : ℝ} (hH : 0 < H) :
    xiHeightTail 10 H ≤ xiLehmanTailMajorant 10 H := by
  apply xiHeightTail_le_lehmanMajorant hH
  intro _
  norm_num
  linarith

example (n : ℕ) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) :
    (∑ i ∈ Finset.range (n + 1), a i * xiHeightTail ((i : ℝ) * 10) 1) ≤
      ∑ i ∈ Finset.range (n + 1), a i * xiLehmanTailMajorant ((i : ℝ) * 10) 1 :=
  sum_xiHeightTail_nat_harmonics_le _ a ha (by norm_num) (by norm_num)

example {T t H : ℝ} (hT : 2 ≤ T) (ht : T ≤ t) (hH : 4 ≤ H) :
    xiLehmanLogBound t H ≤ xiLehmanLogCoefficient T H * Real.log t +
      xiLehmanAffineConstant T H := xiLehmanLogBound_le_affine hT ht hH

example : xiLehmanLogBound 10 4 ≤ xiLehmanLogCoefficient 10 4 * Real.log 10 +
    xiLehmanAffineConstant 10 4 := xiLehmanLogBound_le_affine (by norm_num) le_rfl le_rfl

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H) (hA : 1 ≤ t + H) :
    xiLehmanLogBound t H ≤ xiLehmanHighBound t H + 68 / H ^ 2 :=
  xiLehmanLogBound_le_highBound_add ht hH hA

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H) (hlog : 17 ≤ Real.log (t + H)) :
    xiLehmanLogBound t H ≤ xiLehmanHighBound t H :=
  xiLehmanLogBound_le_highBound ht hH hlog

example {t H : ℝ} (ht : 0 < t) (hH : 0 < H) (hA : 10 ^ 9 ≤ t + H) :
    xiLehmanLogBound t H ≤ xiLehmanHighBound t H :=
  xiLehmanLogBound_le_highBound ht hH (seventeen_le_log_of_billion_le hA)

end

end PrimeFactorUnimodality.Tests
