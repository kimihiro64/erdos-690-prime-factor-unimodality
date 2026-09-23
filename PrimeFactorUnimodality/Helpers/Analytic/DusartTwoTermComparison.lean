import PrimeFactorUnimodality.Helpers.Analytic.DusartJComparison
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCountingPart01

/-! # Direct comparison with the two prime-counting models actually required

Apply Dusart's anchored differential comparison at logarithmic order two.
The lower model uses coefficient one and the upper uses 1.2762. Their
comparison with J needs no log-cubed theta estimate or three-term model.
Both endpoint checks are exact polynomial inequalities in the logarithm.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Derivative of the requested two-term lower comparison function. -/
theorem hasDerivAt_dusartPiLower {x : ℝ} (hx : 1 < x) :
    HasDerivAt dusartPiLower (1 / Real.log x - 2 / Real.log x ^ 3) x := by
  convert hasDerivAt_dusartM (c := 0) hx using 1
  · funext y
    simp only [dusartPiLower, dusartM]
    ring
  · ring

/-- Derivative of the requested two-term upper comparison function. -/
theorem hasDerivAt_dusartPiUpper {x : ℝ} (hx : 1 < x) :
    HasDerivAt dusartPiUpper
      (1 / Real.log x + (1381 / 5000 : ℝ) / Real.log x ^ 2 -
        (6381 / 2500 : ℝ) / Real.log x ^ 3) x := by
  have hd := (Real.hasDerivAt_id_div_log_pow_succ (n := 0) hx).add
    ((Real.hasDerivAt_id_div_log_pow_succ (n := 1) hx).const_mul (6381 / 5000))
  convert hd using 1
  · funext y
    simp only [dusartPiUpper, Pi.add_apply, zero_add, pow_one]
    ring
  · norm_num
    ring

/-- The lower anchor involves just the actual prime count, theta and a logarithm. -/
theorem dusartPiLower_le_dusartJ_two_anchor_iff {η x₀ : ℝ} (h₀ : 1 < x₀) :
    dusartPiLower x₀ ≤ dusartJ 2 (-η) x₀ x₀ ↔
      Chebyshev.theta x₀ * Real.log x₀ ^ 2 + x₀ * Real.log x₀ + η * x₀ ≤
        (Nat.primeCounting ⌊x₀⌋₊ : ℝ) * Real.log x₀ ^ 3 := by
  have hl := Real.log_pos h₀
  have heq : dusartJ 2 (-η) x₀ x₀ - dusartPiLower x₀ =
      ((Nat.primeCounting ⌊x₀⌋₊ : ℝ) * Real.log x₀ ^ 3 -
        (Chebyshev.theta x₀ * Real.log x₀ ^ 2 + x₀ * Real.log x₀ + η * x₀)) /
          Real.log x₀ ^ 3 := by
    rw [dusartJ_self]
    unfold dusartPiLower
    norm_num
    field_simp
    ring
  rw [← sub_nonneg, heq, le_div_iff₀ (pow_pos hl 3), zero_mul, sub_nonneg]

/-- The upper anchor is likewise an exact polynomial inequality. -/
theorem dusartJ_two_le_dusartPiUpper_anchor_iff {η x₀ : ℝ} (h₀ : 1 < x₀) :
    dusartJ 2 η x₀ x₀ ≤ dusartPiUpper x₀ ↔
      (Nat.primeCounting ⌊x₀⌋₊ : ℝ) * Real.log x₀ ^ 3 ≤
        Chebyshev.theta x₀ * Real.log x₀ ^ 2 +
          (6381 / 5000 : ℝ) * x₀ * Real.log x₀ - η * x₀ := by
  have hl := Real.log_pos h₀
  have heq : dusartPiUpper x₀ - dusartJ 2 η x₀ x₀ =
      (Chebyshev.theta x₀ * Real.log x₀ ^ 2 +
        (6381 / 5000 : ℝ) * x₀ * Real.log x₀ - η * x₀ -
          (Nat.primeCounting ⌊x₀⌋₊ : ℝ) * Real.log x₀ ^ 3) / Real.log x₀ ^ 3 := by
    rw [dusartJ_self]
    unfold dusartPiUpper
    norm_num
    field_simp
    ring
  rw [← sub_nonneg, heq, le_div_iff₀ (pow_pos hl 3), zero_mul, sub_nonneg]

/-- A log-square theta coefficient at most two propagates the lower anchor forever. -/
theorem dusartPiLower_le_dusartJ_two {η x₀ x : ℝ}
    (h₀ : 1 < x₀) (hx : x₀ ≤ x) (hη : 0 ≤ η) (hη2 : η ≤ 2)
    (hanchor : dusartPiLower x₀ ≤ dusartJ 2 (-η) x₀ x₀) :
    dusartPiLower x ≤ dusartJ 2 (-η) x₀ x := by
  have hd : ∀ t ∈ Set.Ici x₀, HasDerivAt
      (fun y => dusartJ 2 (-η) x₀ y - dusartPiLower y)
      ((2 - η) / Real.log t ^ 3 + 2 * η / Real.log t ^ 4) t := by
    intro t ht
    convert (hasDerivAt_dusartJ (k := 2) (η := -η) h₀ ht).sub
      (hasDerivAt_dusartPiLower (h₀.trans_le ht)) using 1
    norm_num
    ring
  have hm : MonotoneOn (fun y => dusartJ 2 (-η) x₀ y - dusartPiLower y) (Set.Ici x₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici x₀)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht₀ : x₀ ≤ t := interior_subset ht
      rw [(hd t ht₀).deriv]
      have hp := Real.log_pos (h₀.trans_le ht₀)
      exact add_nonneg (div_nonneg (sub_nonneg.mpr hη2) (by positivity)) (by positivity)
  have h := hm (by simp : x₀ ∈ Set.Ici x₀) hx hx
  linarith

/-- One affine logarithmic margin propagates the upper anchor forever. -/
theorem dusartJ_two_le_dusartPiUpper {η x₀ x : ℝ}
    (h₀ : 1 < x₀) (hx : x₀ ≤ x) (hη : 0 ≤ η)
    (hmargin : (6381 / 2500 : ℝ) + η ≤ (1381 / 5000 : ℝ) * Real.log x₀)
    (hanchor : dusartJ 2 η x₀ x₀ ≤ dusartPiUpper x₀) :
    dusartJ 2 η x₀ x ≤ dusartPiUpper x := by
  have hd : ∀ t ∈ Set.Ici x₀, HasDerivAt
      (fun y => dusartPiUpper y - dusartJ 2 η x₀ y)
      ((1381 / 5000 : ℝ) / Real.log t ^ 2 -
        ((6381 / 2500 : ℝ) + η) / Real.log t ^ 3 + 2 * η / Real.log t ^ 4) t := by
    intro t ht
    convert (hasDerivAt_dusartPiUpper (h₀.trans_le ht)).sub
      (hasDerivAt_dusartJ (k := 2) (η := η) h₀ ht) using 1
    norm_num
    ring
  have hm : MonotoneOn (fun y => dusartPiUpper y - dusartJ 2 η x₀ y) (Set.Ici x₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici x₀)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht₀ : x₀ ≤ t := interior_subset ht
      rw [(hd t ht₀).deriv]
      have hp := Real.log_pos (h₀.trans_le ht₀)
      have hlog := Real.log_le_log (by linarith : 0 < x₀) ht₀
      have heq : (1381 / 5000 : ℝ) / Real.log t ^ 2 -
          ((6381 / 2500 : ℝ) + η) / Real.log t ^ 3 =
          ((1381 / 5000 : ℝ) * Real.log t - ((6381 / 2500 : ℝ) + η)) /
            Real.log t ^ 3 := by field_simp
      rw [heq]
      exact add_nonneg (div_nonneg (by linarith) (by positivity)) (by positivity)
  have h := hm (by simp : x₀ ∈ Set.Ici x₀) hx hx
  linarith

end

end PrimeFactorUnimodality
