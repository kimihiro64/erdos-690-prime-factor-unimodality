import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxDampedHighTail

/-! # An explicit split bound for the damped high-zero tail

Below an auxiliary cutoff the exponential factor is bounded by its endpoint
value. Beyond that cutoff it is at most one. The two unconditional Lehman
bounds then give a real-logarithmic majorant for the entire damped series,
including all cutoff zeros and multiplicities. No numerical zero locations
are assumed in this estimate.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- The damping factor is monotone in absolute height below a fixed upper cutoff. -/
theorem xiInitialDampedHeightKernel_le_cutoff {x T B : ℝ}
    (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T) (p : RiemannXiDivisorZeroIndex)
    (hp : T ≤ |(riemannXiDivisorZeroValue p).im|)
    (hb : |(riemannXiDivisorZeroValue p).im| ≤ B) :
    xiInitialDampedHeightKernel x p ≤
      Real.exp (-(1 / (56 * Real.log B)) * Real.log x) *
        (1 / (riemannXiDivisorZeroValue p).im ^ 2) := by
  have hl : 0 < Real.log |(riemannXiDivisorZeroValue p).im| := Real.log_pos (by linarith)
  have hlog := Real.log_le_log (by linarith : 0 < |(riemannXiDivisorZeroValue p).im|) hb
  have hinv := one_div_le_one_div_of_le (by positivity :
    0 < 56 * Real.log |(riemannXiDivisorZeroValue p).im|)
    (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 56))
  have he := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg hinv) (Real.log_nonneg hx))
  exact (div_le_div_of_nonneg_right he (sq_nonneg _)).trans_eq (by ring)

/-- A split into two closed-tail majorants controls the entire damped series. -/
theorem xiInitialDampedHeightTail_le_split {x T B : ℝ}
    (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T) (hTB : T ≤ B) :
    xiInitialDampedHeightTail x T ≤
      Real.exp (-(1 / (56 * Real.log B)) * Real.log x) * xiHeightTail 0 T +
        xiHeightTail 0 B := by
  classical
  let S : Set RiemannXiDivisorZeroIndex := {p | T ≤ |(riemannXiDivisorZeroValue p).im|}
  let Q : Set RiemannXiDivisorZeroIndex := {p | B ≤ |(riemannXiDivisorZeroValue p).im|}
  let f : RiemannXiDivisorZeroIndex → ℝ := fun p => 1 / (riemannXiDivisorZeroValue p).im ^ 2
  let c := Real.exp (-(1 / (56 * Real.log B)) * Real.log x)
  have hST : Summable (fun p : S => f p.1) := by
    have hs := summable_xiHeightTail (by linarith : 0 < T) 0
    have he : (fun p : RiemannXiDivisorZeroIndex => |(0 : ℝ)| + T ≤
        |(riemannXiDivisorZeroValue p).im|) = (fun p => p ∈ S) := by
      funext p
      simp [S]
    rw [he] at hs
    simpa only [zero_sub, neg_sq] using hs
  have hQB : Summable (fun p : Q => f p.1) := by
    have hs := summable_xiHeightTail (by linarith : 0 < B) 0
    have he : (fun p : RiemannXiDivisorZeroIndex => |(0 : ℝ)| + B ≤
        |(riemannXiDivisorZeroValue p).im|) = (fun p => p ∈ Q) := by
      funext p
      simp [Q]
    rw [he] at hs
    simpa only [zero_sub, neg_sq] using hs
  have hS : Summable (S.indicator f) := summable_subtype_iff_indicator.mp hST
  have hQ : Summable (Q.indicator f) := summable_subtype_iff_indicator.mp hQB
  have hG : Summable (S.indicator (xiInitialDampedHeightKernel x)) :=
    summable_subtype_iff_indicator.mp (summable_xiInitialDampedHeightKernel hx hT)
  have hcmp (p : RiemannXiDivisorZeroIndex) :
      S.indicator (xiInitialDampedHeightKernel x) p ≤ c * S.indicator f p + Q.indicator f p := by
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      by_cases hq : p ∈ Q
      · rw [Set.indicator_of_mem hq]
        exact (xiInitialDampedHeightKernel_le_inv_sq hx hT p hp).trans
          (le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (by dsimp [f]; positivity)))
      · rw [Set.indicator_of_notMem hq, add_zero]
        change ¬ B ≤ |(riemannXiDivisorZeroValue p).im| at hq
        exact xiInitialDampedHeightKernel_le_cutoff hx hT p hp (lt_of_not_ge hq).le
    · have hq : p ∉ Q := fun h => hp (hTB.trans h)
      simp only [Set.indicator_of_notMem hp, Set.indicator_of_notMem hq,
        mul_zero, add_zero, le_refl]
  have hs := hG.tsum_le_tsum hcmp ((hS.mul_left c).add hQ)
  rw [(hS.mul_left c).tsum_add hQ, tsum_mul_left,
    ← tsum_subtype S (xiInitialDampedHeightKernel x), ← tsum_subtype S f, ← tsum_subtype Q f] at hs
  rw [xiInitialDampedHeightTail, xiHeightTail_zero_eq_tsum, xiHeightTail_zero_eq_tsum]
  convert! hs using 1

/-- The proved counting estimates make both terms of the split bound explicit. -/
theorem xiInitialDampedHeightTail_le_split_highBound {x T B : ℝ}
    (hx : 1 ≤ x) (hT : 10 ^ 9 ≤ T) (hTB : T ≤ B) :
    xiInitialDampedHeightTail x T ≤
      Real.exp (-(1 / (56 * Real.log B)) * Real.log x) *
        (4 * xiLehmanHighBound (T / 2) (T / 2)) +
      4 * xiLehmanHighBound (B / 2) (B / 2) :=
  (xiInitialDampedHeightTail_le_split hx hT hTB).trans (add_le_add
    (mul_le_mul_of_nonneg_left (xiHeightTail_zero_le_highBound hT) (Real.exp_pos _).le)
    (xiHeightTail_zero_le_highBound (hT.trans hTB)))

/-- The actual high box sum has a fully explicit bound retaining zero-free damping. -/
theorem norm_dusartBoxXiHighSum_le_split_highBound (m : ℕ) {h x T B : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hT : 10 ^ 9 ≤ T) (hTB : T ≤ B) :
    ‖dusartBoxXiHighSum m h x T‖ ≤ dusartBoxTailFactor m h x T *
      (Real.exp (-(1 / (56 * Real.log B)) * Real.log x) *
        (4 * xiLehmanHighBound (T / 2) (T / 2)) +
      4 * xiLehmanHighBound (B / 2) (B / 2)) :=
  (norm_dusartBoxXiHighSum_le_initialDampedTail m hh hx hT).trans
    (mul_le_mul_of_nonneg_left (xiInitialDampedHeightTail_le_split_highBound hx.le hT hTB)
      (dusartBoxTailFactor_nonneg m hh hx (by linarith)))

end

end PrimeFactorUnimodality
