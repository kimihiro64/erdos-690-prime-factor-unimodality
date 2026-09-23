import PrimeFactorUnimodality.Helpers.Analytic.ThetaSquaredCheckpoints

/-! # Rational checkpoint tests for the two exact Dusart Abel anchors

The theta enclosure is shared with the lower-band checkpoints. A lower log
enclosure and prime-counting bounds reduce each real anchor inequality to
a rational polynomial comparison. No numerical value is supplied or assumed
without its corresponding enclosure premise.
-/

set_option autoImplicit false

namespace PrimeFactorUnimodality

namespace ThetaSquaredCheckpoint

/-- A rational margin supplies the exact lower prime-counting anchor at this checkpoint. -/
theorem lower_anchor {p : ThetaSquaredCheckpoint} (hp : p.Valid)
    {L : ℚ} (hL0 : 0 ≤ L) (hL : (L : ℝ) ≤ Real.log p.point)
    {k : ℕ} (hk : k ≤ Nat.primeCounting p.point)
    (hmargin : p.upper * p.logUpper ^ 2 + (p.point : ℚ) * p.logUpper +
      (1 / 5 : ℚ) * p.point ≤ (k : ℚ) * L ^ 3) :
    Chebyshev.theta p.point * Real.log p.point ^ 2 +
      (p.point : ℝ) * Real.log p.point + (1 / 5 : ℝ) * p.point ≤
        (Nat.primeCounting p.point : ℝ) * Real.log p.point ^ 3 := by
  have hL0' : (0 : ℝ) ≤ L := by exact_mod_cast hL0
  have hlog0 : 0 ≤ Real.log p.point := hL0'.trans hL
  have hU : 0 ≤ (p.upper : ℝ) := (Chebyshev.theta_nonneg _).trans hp.2.2.2.1
  have hsq := pow_le_pow_left₀ hlog0 hp.2.2.2.2 2
  have hcube := pow_le_pow_left₀ hL0' hL 3
  have hk' : (k : ℝ) ≤ Nat.primeCounting p.point := by exact_mod_cast hk
  have hm := (Rat.cast_le (K := ℝ)).2 hmargin
  push_cast at hm
  have ht := mul_le_mul hp.2.2.2.1 hsq (sq_nonneg _) hU
  have hl := mul_le_mul_of_nonneg_left hp.2.2.2.2 (Nat.cast_nonneg (α := ℝ) p.point)
  have hr := mul_le_mul hk' hcube (pow_nonneg hL0' 3)
    (Nat.cast_nonneg (α := ℝ) (Nat.primeCounting p.point))
  linarith

/-- A rational margin supplies the exact upper prime-counting anchor at this checkpoint. -/
theorem upper_anchor {p : ThetaSquaredCheckpoint} (hp : p.Valid)
    {L : ℚ} (hL0 : 0 ≤ L)
    (hL : (L : ℝ) ≤ Real.log p.point) {k : ℕ} (hk : Nat.primeCounting p.point ≤ k)
    (hmargin : (k : ℚ) * p.logUpper ^ 3 ≤ p.lower * L ^ 2 +
      (6381 / 5000 : ℚ) * p.point * L - (1 / 5 : ℚ) * p.point) :
    (Nat.primeCounting p.point : ℝ) * Real.log p.point ^ 3 ≤
      Chebyshev.theta p.point * Real.log p.point ^ 2 +
        (6381 / 5000 : ℝ) * p.point * Real.log p.point - (1 / 5 : ℝ) * p.point := by
  have hL0' : (0 : ℝ) ≤ L := by exact_mod_cast hL0
  have hlog0 : 0 ≤ Real.log p.point := hL0'.trans hL
  have hsq := pow_le_pow_left₀ hL0' hL 2
  have hcube := pow_le_pow_left₀ hlog0 hp.2.2.2.2 3
  have hk' : (Nat.primeCounting p.point : ℝ) ≤ k := by exact_mod_cast hk
  have hm := (Rat.cast_le (K := ℝ)).2 hmargin
  push_cast at hm
  have ht := mul_le_mul hp.2.2.1 hsq (sq_nonneg _) (Chebyshev.theta_nonneg _)
  have hl := mul_le_mul_of_nonneg_left hL
    (show (0 : ℝ) ≤ (6381 / 5000 : ℝ) * p.point by positivity)
  have hr := mul_le_mul hk' hcube (pow_nonneg hlog0 3) (Nat.cast_nonneg (α := ℝ) k)
  linarith

end ThetaSquaredCheckpoint

end PrimeFactorUnimodality
