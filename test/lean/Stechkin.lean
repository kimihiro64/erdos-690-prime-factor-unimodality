import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiStechkinZero

set_option autoImplicit false

/-! # Regression checks for shifted positivity and paired zero kernels

The kernel tests include the boundary of the critical strip and a retained
aligned pole. The nonzero compact weight test deliberately uses `σ = 1/2`:
compact smoothing must not inherit the unweighted convergence restriction.
-/

open Complex
open scoped BigOperators

namespace PrimeFactorUnimodality.Tests

example (s : ℂ) : riemannXi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannXi s) :=
  riemannXi_conj s

example (σ : ℝ) (hσ : 1 < σ) (ρ : ℂ) (hρ : riemannXi ρ = 0)
    (hβ : (1 / 2 : ℝ) < ρ.re) :
    1 / (σ - ρ.re) ≤ (logDeriv riemannXi ((σ : ℂ) + ρ.im * I)).re -
      (1 / Real.sqrt 5) *
        (logDeriv riemannXi ((Real.stechkinShift σ : ℂ) + ρ.im * I)).re :=
  re_logDeriv_riemannXi_stechkin_zero_le hσ hρ hβ

example (σ t : ℝ) (hσ : 1 < σ) :
    2 * (logDeriv riemannXi ((σ : ℂ) + t * I)).re =
      ∑' p : RiemannXiDivisorZeroIndex,
        stechkinZeroPair ((σ : ℂ) + t * I) (riemannXiDivisorZeroValue p) :=
  two_re_logDeriv_riemannXi_eq_tsum_pair (by simpa using hσ)

example (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ (logDeriv riemannXi ((σ : ℂ) + t * I)).re -
      (1 / Real.sqrt 5) *
        (logDeriv riemannXi ((Real.stechkinShift σ : ℂ) + t * I)).re :=
  re_logDeriv_riemannXi_stechkin_nonneg hσ t

example (β t : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    (1 / Real.sqrt 5) * Real.stechkinPair (Real.stechkinShift (3 / 2)) β t ≤
      Real.stechkinPair (3 / 2) β t := by
  have hσ : (1 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨hτ, hrel⟩ := Real.stechkinShift_spec hσ
  exact Real.stechkinPair_le hσ hτ hrel hβ₀ hβ₁ t

example : 2 + (1 / Real.sqrt 5) *
    Real.stechkinPair (Real.stechkinShift (3 / 2)) 1 0 ≤
      Real.stechkinPair (3 / 2) 1 0 := by
  have hσ : (1 : ℝ) < 3 / 2 := by norm_num
  obtain ⟨hτ, hrel⟩ := Real.stechkinShift_spec hσ
  have h := Real.stechkinPair_aligned_le hσ hτ hrel
    (by norm_num : (0 : ℝ) ≤ 1) le_rfl
  norm_num only at h
  exact h

example (ρ : ℂ) (hρ : riemannXi ρ = 0) :
    1 / ((3 / 2 : ℝ) - ρ.re) ≤
      stechkinZeroPair ((3 / 2 : ℂ) + ρ.im * I) ρ -
        (1 / Real.sqrt 5) *
          stechkinZeroPair ((Real.stechkinShift (3 / 2) : ℂ) + ρ.im * I) ρ := by
  simpa only [ofReal_div, ofReal_ofNat] using
    stechkinZeroPair_aligned_le (σ := 3 / 2) (by norm_num) hρ

noncomputable def compactTestWeight (x : ℝ) : ℝ := if x ≤ 1 then 1 else 0

example : compactTestWeight 0 = 1 := by norm_num [compactTestWeight]

example : (fun n : ℕ => compactTestWeight (Real.log n)).HasFiniteSupport :=
  hasFiniteSupport_log_weight (d := 1) (by
    intro x hx
    simp [compactTestWeight, not_le.mpr hx])

example (t : ℝ) :
    0 ≤ ∑ i : Fin 3, (![3, 4, 1] : Fin 3 → ℝ) i *
      ((smoothedVonMangoldt compactTestWeight
        ((1 / 2 : ℂ) + ((i.val : ℝ) * t : ℝ) * I)).re -
        (1 / 2 : ℝ) * (smoothedVonMangoldt compactTestWeight
          ((3 / 2 : ℂ) + ((i.val : ℝ) * t : ℝ) * I)).re) := by
  have hf (x : ℝ) (hx : 1 < x) : compactTestWeight x = 0 := by
    simp [compactTestWeight, not_le.mpr hx]
  have hf₀ (x : ℝ) (_hx : 0 ≤ x) : 0 ≤ compactTestWeight x := by
    unfold compactTestWeight
    split_ifs <;> norm_num
  have hpoly (u : ℝ) :
      0 ≤ ∑ i : Fin 3, (![3, 4, 1] : Fin 3 → ℝ) i * Real.cos (i.val * u) := by
    norm_num [Fin.sum_univ_succ]
    rw [Real.cos_two_mul]
    nlinarith [sq_nonneg (1 + Real.cos u)]
  have h := sum_mul_re_shifted_smoothedVonMangoldt_nonneg
    Finset.univ (![3, 4, 1] : Fin 3 → ℝ) (fun i : Fin 3 => (i.val : ℝ))
    (f := compactTestWeight) (d := 1) (σ := 1 / 2) (τ := 3 / 2) (κ := 1 / 2)
    hf hf₀ (by norm_num) (by norm_num) t hpoly
  simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using h

end PrimeFactorUnimodality.Tests
