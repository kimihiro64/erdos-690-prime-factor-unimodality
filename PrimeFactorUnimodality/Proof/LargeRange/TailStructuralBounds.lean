import PrimeFactorUnimodality.Helpers.Analytic.PrimorialLogBounds
import PrimeFactorUnimodality.Proof.LargeRange.TailErrorBounds

set_option autoImplicit false

/-! # Discrete side conditions for the optimized uniform tail -/

namespace PrimeFactorUnimodality

noncomputable section

/-- Integer upper bound used for the later average prime gap. -/
def tailGapBound (q : Nat) : Nat := q + q / 100 + 1

theorem tailGapBound_pos (q : Nat) : 1 ≤ tailGapBound q := by
  unfold tailGapBound
  omega

theorem one_hundredth_lt_tailGapBound_remainder (q : Nat) :
    (q : Real) / 100 < ((q / 100 + 1 : Nat) : Real) := by
  have remainder : q % 100 < 100 := Nat.mod_lt q (by omega)
  have decomposition : q % 100 + 100 * (q / 100) = q :=
    Nat.mod_add_div q 100
  have division : q < 100 * (q / 100 + 1) := by omega
  have castDivision : (q : Real) < 100 * ((q / 100 + 1 : Nat) : Real) := by
    exact_mod_cast division
  norm_num at castDivision ⊢
  exact (div_lt_iff₀ (by norm_num : (0 : Real) < 100)).2 (by
    simpa only [mul_comm] using castDivision)

theorem tailGapBound_gt_onePointZeroOne (q : Nat) :
    (101 / 100 : Real) * q < tailGapBound q := by
  have remainder := one_hundredth_lt_tailGapBound_remainder q
  unfold tailGapBound
  push_cast
  norm_num at remainder ⊢
  linarith

theorem tailGapBound_le_onePointZeroTwo {q : Nat} (hq : 100 ≤ q) :
    (tailGapBound q : Real) ≤ (102 / 100 : Real) * q := by
  have quotientSharp : ((q / 100 : Nat) : Real) ≤ (q : Real) / 100 := by
    exact Nat.cast_div_le
  have oneSmall : (1 : Real) ≤ (q : Real) / 100 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast hq
  unfold tailGapBound
  push_cast
  linarith

/-- At the optimized cutoff the prime prefix is automatically beyond the
threshold in the sharp reciprocal-prime estimate. -/
theorem tail_prefixThreshold {k : Nat} (hk : 38000 ≤ k) :
    10372 ≤ primeAt (k - 2) - 1 := by
  have indexEq : k - 2 + 2 = k := by omega
  have lower := Nat.add_two_le_nth_prime (k - 2)
  rw [indexEq] at lower
  change k ≤ primeAt (k - 2) at lower
  omega

/-- Any prime selected above the tail scale is well beyond the fixed small
primorial thresholds used by the average-gap construction. -/
theorem tail_selected_prime_ge_3501 {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    3501 ≤ q := by
  have scaleGt := tailScale_gt_3500 hr
  have : (3500 : Real) < q := scaleGt.trans scaleLtQ
  exact_mod_cast this

theorem tail_primorial_large {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    599 ≤ 9 * primorial q := by
  have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
  have primorialLower : primorial 11 ≤ primorial q :=
    primorial_mono (by omega)
  have primorialEleven : primorial 11 = 2310 := by decide
  rw [primorialEleven] at primorialLower
  omega

theorem tail_ascentThreshold {r q : Nat} (hr : 38000 ≤ r)
    (scaleLtQ : (491 / 500 : Real) * r / Real.log r < q) :
    10372 ≤ 9 * primorial q := by
  have qLarge := tail_selected_prime_ge_3501 hr scaleLtQ
  have primorialLower : primorial 11 ≤ primorial q :=
    primorial_mono (by omega)
  have primorialEleven : primorial 11 = 2310 := by decide
  rw [primorialEleven] at primorialLower
  omega

theorem tail_predecessor_gt_two {qPrev : Nat} (h : 3301 ≤ qPrev) :
    2 < qPrev := by omega

end

end PrimeFactorUnimodality
