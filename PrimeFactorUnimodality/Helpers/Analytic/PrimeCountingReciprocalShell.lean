import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.PrimeReciprocalAbel

set_option autoImplicit false

/-! # A finite reciprocal-prime shell from prime counting

Abel summation cancels the first-order endpoint errors. A unit allowance
extends the natural prime-counting lower bound to real integration points.
Its integrated cost is at most the reciprocal of the lower endpoint.
-/

namespace PrimeFactorUnimodality

open MeasureTheory

noncomputable section

theorem log_ge_two_of_ge_six_hundred {t : Real} (ht : 600 ≤ t) :
    2 ≤ Real.log t := by
  have h := Real.log_le_log (by norm_num : (0 : Real) < 2 ^ 4)
    (show (2 : Real) ^ 4 ≤ t by norm_num; linarith)
  rw [Real.log_pow] at h
  norm_num at h
  nlinarith [Real.log_two_gt_d9]

theorem primeCounting_floor_lower (bounds : HasDusartPrimeCountingBounds)
    {t : Real} (ht : 600 ≤ t) :
    dusartPiLower t - 1 ≤ (Nat.primeCounting ⌊t⌋₊ : Real) := by
  let n := ⌊t⌋₊
  have hn : 600 ≤ n := Nat.le_floor ht
  have hnpos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hnle : (n : Real) ≤ t := Nat.floor_le (by linarith)
  have htn : t - 1 ≤ (n : Real) := by
    have h := Nat.lt_floor_add_one t
    dsimp only [n]
    linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogt : 2 ≤ Real.log t := log_ge_two_of_ge_six_hundred ht
  have hlog : Real.log n ≤ Real.log t := Real.log_le_log hnpos hnle
  have hi := one_div_le_one_div_of_le hlogn hlog
  have hi2 := one_div_le_one_div_of_le (sq_pos_of_pos hlogn)
    (pow_le_pow_left₀ hlogn.le hlog 2)
  have hsmall : 1 / Real.log t + 1 / (Real.log t) ^ 2 ≤ (1 : Real) := by
    have h1 := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2) hlogt
    have h2 := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 4)
      (show (4 : Real) ≤ (Real.log t) ^ 2 by nlinarith)
    norm_num at h1 h2
    simpa only [one_div] using
      (show (Real.log t)⁻¹ + ((Real.log t) ^ 2)⁻¹ ≤ (1 : Real) by linarith)
  have hweight : 0 ≤ 1 / Real.log t + 1 / (Real.log t) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add hi hi2) hnpos.le
  have hfloor := mul_le_mul_of_nonneg_right htn hweight
  have hlower := bounds.1 n (by omega)
  have expand (x : Real) : dusartPiLower x = x * (1 / Real.log x + 1 / (Real.log x) ^ 2) := by
    unfold dusartPiLower
    ring
  rw [expand] at hlower ⊢
  nlinarith

private def shellIntegrand (t : Real) : Real :=
  1 / (t * Real.log t) + 1 / (t * (Real.log t) ^ 2) - 1 / t ^ 2

private def shellPrimitive (t : Real) : Real :=
  Real.log (Real.log t) - 1 / Real.log t + 1 / t

private theorem shellPrimitive_hasDerivAt {t : Real} (ht : 1 < t) :
    HasDerivAt shellPrimitive (shellIntegrand t) t := by
  have tne : t ≠ 0 := by linarith
  have lne : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have h := ((Real.hasDerivAt_log lne).comp t (Real.hasDerivAt_log tne)).sub
    ((hasDerivAt_const t (1 : Real)).div (Real.hasDerivAt_log tne) lne)
  have h' := h.add ((hasDerivAt_const t (1 : Real)).div (hasDerivAt_id t) tne)
  convert h' using 1
  · rfl
  · dsimp only [shellIntegrand, id_eq]
    field_simp
    ring

private theorem shellIntegrand_continuousOn {a b : Real} (ha : 1 < a) :
    ContinuousOn shellIntegrand (Set.Icc a b) := by
  have hn (t : Real) (ht : t ∈ Set.Icc a b) : t ≠ 0 := by linarith [ht.1]
  have hl (t : Real) (ht : t ∈ Set.Icc a b) : Real.log t ≠ 0 :=
    (Real.log_pos (by linarith [ht.1])).ne'
  have hc : ContinuousOn Real.log (Set.Icc a b) := continuousOn_id.log hn
  exact ((continuousOn_const.div (continuousOn_id.mul hc) (by
    intro t ht; exact mul_ne_zero (hn t ht) (hl t ht))).add
    (continuousOn_const.div (continuousOn_id.mul (hc.pow 2)) (by
      intro t ht; exact mul_ne_zero (hn t ht) (pow_ne_zero _ (hl t ht))))).sub
    (continuousOn_const.div (continuousOn_id.pow 2) (by
      intro t ht; exact pow_ne_zero _ (hn t ht)))

theorem reciprocalPrimeSumBelow_sub_lower_of_primeCounting
    (bounds : HasDusartPrimeCountingBounds) {x y : Nat}
    (hx : 600 ≤ x) (hxy : x ≤ y) :
    Real.log (Real.log y) - Real.log (Real.log x) -
        (6381 / 5000 : Real) / (Real.log x) ^ 2 - 1 / x ≤
      reciprocalPrimeSumBelow (y + 1) - reciprocalPrimeSumBelow (x + 1) := by
  have xp : (1 : Real) < x := by exact_mod_cast (show 1 < x by omega)
  have yp : (1 : Real) < y := by exact_mod_cast (show 1 < y by omega)
  have xy : (x : Real) ≤ y := by exact_mod_cast hxy
  have lx : 0 < Real.log x := Real.log_pos xp
  have ly : 0 < Real.log y := Real.log_pos yp
  have hc := shellIntegrand_continuousOn (b := (y : Real)) xp
  have heq : (∫ t in Set.Ioc (x : Real) y, shellIntegrand t) =
      shellPrimitive y - shellPrimitive x := by
    rw [← intervalIntegral.integral_of_le xy]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le xy] at ht
      exact shellPrimitive_hasDerivAt (xp.trans_le ht.1)
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le xy).mpr hc.integrableOn_Icc
  have hle : (∫ t in Set.Ioc (x : Real) y, shellIntegrand t) ≤
      ∫ t in Set.Ioc (x : Real) y, (Nat.primeCounting ⌊t⌋₊ : Real) / t ^ 2 := by
    apply setIntegral_mono_on (hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      ((primeCounting_div_square_integrable (by linarith : (0 : Real) < x)).mono_set
        Set.Ioc_subset_Icc_self) measurableSet_Ioc
    intro t ht
    have th : 600 ≤ t := by
      have xx : (600 : Real) ≤ x := by exact_mod_cast hx
      linarith [ht.1]
    have h := div_le_div_of_nonneg_right (primeCounting_floor_lower bounds th)
      (sq_nonneg t)
    have tn : t ≠ 0 := by linarith
    have ln : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
    convert h using 1
    unfold shellIntegrand dusartPiLower
    field_simp [tn, ln]
  rw [heq] at hle
  have lower := div_le_div_of_nonneg_right (bounds.1 y (by omega))
    (show (0 : Real) ≤ y by positivity)
  have upper := div_le_div_of_nonneg_right (bounds.2 x (by omega))
    (show (0 : Real) ≤ x by positivity)
  have lexpand : dusartPiLower y / y = 1 / Real.log y + 1 / (Real.log y) ^ 2 := by
    unfold dusartPiLower
    field_simp
  have uexpand : dusartPiUpper x / x =
      1 / Real.log x + (6381 / 5000 : Real) / (Real.log x) ^ 2 := by
    unfold dusartPiUpper
    field_simp
  rw [lexpand] at lower
  rw [uexpand] at upper
  rw [reciprocalPrimeSumBelow_sub_eq_integral (by omega) hxy]
  dsimp only [shellPrimitive] at hle
  have hpositive : 0 ≤ 1 / (Real.log (y : Real)) ^ 2 + 1 / (y : Real) := by positivity
  linarith

theorem primeWeightSumBelow_sub_lower_of_primeCounting
    (bounds : HasDusartPrimeCountingBounds) {x y : Nat}
    (hx : 600 ≤ x) (hxy : x ≤ y) :
    Real.log (Real.log y) - Real.log (Real.log x) -
        (6381 / 5000 : Real) / (Real.log x) ^ 2 - 1 / x ≤
      primeWeightSumBelow (y + 1) - primeWeightSumBelow (x + 1) :=
  (reciprocalPrimeSumBelow_sub_lower_of_primeCounting bounds hx hxy).trans
    (reciprocal_sub_le_primeWeight_sub (Nat.add_le_add_right hxy 1))

end

end PrimeFactorUnimodality
