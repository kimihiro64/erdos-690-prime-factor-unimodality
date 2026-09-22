import PrimeFactorUnimodality.Helpers.Analytic.DusartJBounds
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

/-! # Differential comparison in Dusart's prime-counting proof

The derivatives of the anchored `J` function and the three-term model `M`
reduce the unbounded comparison to a numerical inequality at the anchor
and an elementary inequality in its logarithm. This implements the
calculus step of Dusart's Section 6.2, without a finite-replay dependency.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Dusart's three-term prime-counting model, in expanded form. -/
def dusartM (c x : Real) : Real :=
  x / Real.log x + x / Real.log x ^ 2 + c * x / Real.log x ^ 3

/-- The upper anchor check is a polynomial inequality in the logarithm. -/
theorem dusartJ_two_anchor_iff {η c x₀ : Real} (h₀ : 1 < x₀) :
    dusartJ 2 η x₀ x₀ ≤ dusartM c x₀ ↔
      (Nat.primeCounting ⌊x₀⌋₊ : Real) * Real.log x₀ ^ 3 ≤
        Chebyshev.theta x₀ * Real.log x₀ ^ 2 + x₀ * Real.log x₀ + (c - η) * x₀ := by
  have hl := Real.log_pos h₀
  have heq : dusartM c x₀ - dusartJ 2 η x₀ x₀ =
      (Chebyshev.theta x₀ * Real.log x₀ ^ 2 + x₀ * Real.log x₀ + (c - η) * x₀ -
        (Nat.primeCounting ⌊x₀⌋₊ : Real) * Real.log x₀ ^ 3) / Real.log x₀ ^ 3 := by
    rw [dusartJ_self]
    unfold dusartM
    norm_num
    field_simp
    ring
  rw [← sub_nonneg, heq, le_div_iff₀ (pow_pos hl 3), zero_mul, sub_nonneg]

/-- The lower anchor check likewise has no integrals or variable denominators. -/
theorem dusartJ_three_anchor_iff {η c x₀ : Real} (h₀ : 1 < x₀) :
    dusartM c x₀ ≤ dusartJ 3 η x₀ x₀ ↔
      Chebyshev.theta x₀ * Real.log x₀ ^ 3 + x₀ * Real.log x₀ ^ 2 +
        c * x₀ * Real.log x₀ - η * x₀ ≤
          (Nat.primeCounting ⌊x₀⌋₊ : Real) * Real.log x₀ ^ 4 := by
  have hl := Real.log_pos h₀
  have heq : dusartJ 3 η x₀ x₀ - dusartM c x₀ =
      ((Nat.primeCounting ⌊x₀⌋₊ : Real) * Real.log x₀ ^ 4 -
        (Chebyshev.theta x₀ * Real.log x₀ ^ 3 + x₀ * Real.log x₀ ^ 2 +
          c * x₀ * Real.log x₀ - η * x₀)) / Real.log x₀ ^ 4 := by
    rw [dusartJ_self]
    unfold dusartM
    norm_num
    field_simp
    ring
  rw [← sub_nonneg, heq, le_div_iff₀ (pow_pos hl 4), zero_mul, sub_nonneg]

/-- The cancellation of the logarithm-square terms in `J'`. -/
theorem hasDerivAt_dusartJ {k : Nat} {η x₀ x : Real}
    (h₀ : 1 < x₀) (hx : x₀ ≤ x) :
    HasDerivAt (dusartJ k η x₀)
      (1 / Real.log x + η / Real.log x ^ (k + 1) -
        k * η / Real.log x ^ (k + 2)) x := by
  have hx1 := h₀.trans_le hx
  have hc : ∀ t ∈ Set.Ioi (1 : Real), ContinuousAt
      (fun y : Real => 1 / Real.log y ^ 2 + η / Real.log y ^ (k + 2)) t := by
    intro t ht
    have hlog := Real.continuousAt_log (ne_of_gt (lt_trans zero_lt_one ht))
    exact (continuousAt_const.div (hlog.pow 2) (pow_ne_zero _ (Real.log_pos ht).ne')).add
      (continuousAt_const.div (hlog.pow (k + 2)) (pow_ne_zero _ (Real.log_pos ht).ne'))
  have hi : IntervalIntegrable (fun t : Real => 1 / Real.log t ^ 2 +
      η / Real.log t ^ (k + 2)) MeasureTheory.volume x₀ x := by
    apply ContinuousOn.intervalIntegrable
    exact (continuousOn_dusartJ_integrand k η h₀).mono
      (by rw [Set.uIcc_of_le hx]; exact fun _ ht => ht.1)
  have hdint := intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hc x hx1) (hc x hx1)
  have hd₁ := Real.hasDerivAt_id_div_log_pow_succ (n := 0) hx1
  have hd₂ := (Real.hasDerivAt_id_div_log_pow_succ (n := k) hx1).const_mul η
  have hd := ((hd₁.const_add
    ((Nat.primeCounting ⌊x₀⌋₊ : Real) - Chebyshev.theta x₀ / Real.log x₀)).add hd₂).add hdint
  convert hd using 1
  · funext y
    simp only [dusartJ, Pi.add_apply, zero_add, pow_one]
    ring
  · simp only [Nat.cast_zero, zero_add, pow_one]
    ring

/-- The derivative printed for `M` in the paper. -/
theorem hasDerivAt_dusartM {c x : Real} (hx : 1 < x) :
    HasDerivAt (dusartM c)
      (1 / Real.log x + (c - 2) / Real.log x ^ 3 - 3 * c / Real.log x ^ 4) x := by
  have hd := ((Real.hasDerivAt_id_div_log_pow_succ (n := 0) hx).add
    (Real.hasDerivAt_id_div_log_pow_succ (n := 1) hx)).add
    ((Real.hasDerivAt_id_div_log_pow_succ (n := 2) hx).const_mul c)
  convert hd using 1
  · funext y
    simp only [dusartM, Pi.add_apply, zero_add, pow_one]
    ring
  · norm_num
    ring

/-- The upper derivative comparison needs a single affine inequality in `log x₀`. -/
theorem dusartJ_two_le_dusartM {η c x₀ x : Real}
    (h₀ : 1 < x₀) (hx : x₀ ≤ x)
    (hslope : 0 ≤ c - 2 - η)
    (hmargin : 3 * c - 2 * η ≤ (c - 2 - η) * Real.log x₀)
    (hanchor : dusartJ 2 η x₀ x₀ ≤ dusartM c x₀) :
    dusartJ 2 η x₀ x ≤ dusartM c x := by
  have hd : ∀ t ∈ Set.Ici x₀, HasDerivAt
      (fun y => dusartM c y - dusartJ 2 η x₀ y)
      ((c - 2 - η) / Real.log t ^ 3 - (3 * c - 2 * η) / Real.log t ^ 4) t := by
    intro t ht
    convert (hasDerivAt_dusartM (h₀.trans_le ht)).sub (hasDerivAt_dusartJ h₀ ht) using 1
    norm_num
    ring
  have hm : MonotoneOn (fun y => dusartM c y - dusartJ 2 η x₀ y) (Set.Ici x₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici x₀)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht₀ : x₀ ≤ t := interior_subset ht
      rw [(hd t ht₀).deriv]
      have hlogpos := Real.log_pos (h₀.trans_le ht₀)
      have hscale := mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith : 0 < x₀) ht₀) hslope
      have heq : (c - 2 - η) / Real.log t ^ 3 - (3 * c - 2 * η) / Real.log t ^ 4 =
          ((c - 2 - η) * Real.log t - (3 * c - 2 * η)) / Real.log t ^ 4 := by
        field_simp
      rw [heq]
      exact div_nonneg (by linarith) (by positivity)
  have h := hm (by simp : x₀ ∈ Set.Ici x₀) hx hx
  linarith

/-- For the lower model with coefficient 2, Dusart uses a log-cubed theta error. -/
theorem dusartM_two_le_dusartJ_three {η x₀ x : Real}
    (h₀ : 1 < x₀) (hx : x₀ ≤ x) (hη : 0 ≤ η) (hη6 : η ≤ 6)
    (hanchor : dusartM 2 x₀ ≤ dusartJ 3 (-η) x₀ x₀) :
    dusartM 2 x ≤ dusartJ 3 (-η) x₀ x := by
  have hd : ∀ t ∈ Set.Ici x₀, HasDerivAt
      (fun y => dusartJ 3 (-η) x₀ y - dusartM 2 y)
      ((6 - η) / Real.log t ^ 4 + 3 * η / Real.log t ^ 5) t := by
    intro t ht
    convert (hasDerivAt_dusartJ (k := 3) (η := -η) h₀ ht).sub
      (hasDerivAt_dusartM (c := 2) (h₀.trans_le ht)) using 1
    norm_num
    ring
  have hm : MonotoneOn (fun y => dusartJ 3 (-η) x₀ y - dusartM 2 y) (Set.Ici x₀) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici x₀)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht₀ : x₀ ≤ t := interior_subset ht
      rw [(hd t ht₀).deriv]
      have hp := Real.log_pos (h₀.trans_le ht₀)
      exact add_nonneg (div_nonneg (sub_nonneg.mpr hη6) (by positivity)) (by positivity)
  have h := hm (by simp : x₀ ∈ Set.Ici x₀) hx hx
  linarith

end

end PrimeFactorUnimodality
