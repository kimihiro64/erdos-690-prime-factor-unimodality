import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiStechkin

set_option autoImplicit false

/-! # Retaining a zero in the full Stechkin sum

A zero strictly right of the critical line and its reflected zero have
distinct divisor indices. Retaining both equal paired-kernel terms cancels
the factor two in the symmetrized Hadamard identity and retains the full
pole `1/(sigma-beta)`. No simplicity assumption is made about either zero.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

/-- Reflection exchanges the two summands of the paired kernel. -/
theorem stechkinZeroPair_reflect (s ρ : ℂ) :
    stechkinZeroPair s (1 - conj ρ) = stechkinZeroPair s ρ := by
  have h₁ : s - (1 - conj ρ) = s - 1 + conj ρ := by ring
  have h₂ : s - 1 + conj (1 - conj ρ) = s - ρ := by
    simp only [map_sub, map_one, conj_conj]
    ring
  simp only [stechkinZeroPair, h₁, h₂, add_re]
  ring

/-- The full single-zero pole survives Stechkin subtraction for zeros right of the midline. -/
theorem re_logDeriv_riemannXi_stechkin_zero_le {σ : ℝ} (hσ : 1 < σ)
    {ρ : ℂ} (hρ : riemannXi ρ = 0) (hβ : (1 / 2 : ℝ) < ρ.re) :
    1 / (σ - ρ.re) ≤ (logDeriv riemannXi ((σ : ℂ) + ρ.im * I)).re -
      (1 / Real.sqrt 5) *
        (logDeriv riemannXi ((Real.stechkinShift σ : ℂ) + ρ.im * I)).re := by
  classical
  obtain ⟨p, hp⟩ := exists_xi_divisor_index_of_zero hρ
  obtain ⟨q, hq⟩ := exists_xi_divisor_index_of_zero (riemannXi_reflected_zero hρ)
  have hpq : p ≠ q := by
    intro h
    have heq : ρ = 1 - conj ρ :=
      hp.symm.trans ((congrArg riemannXiDivisorZeroValue h).trans hq)
    have hre := congrArg Complex.re heq
    simp only [sub_re, one_re, conj_re] at hre
    linarith
  let s : ℂ := (σ : ℂ) + ρ.im * I
  let s₁ : ℂ := (Real.stechkinShift σ : ℂ) + ρ.im * I
  let F : RiemannXiDivisorZeroIndex → ℝ := fun r =>
    stechkinZeroPair s (riemannXiDivisorZeroValue r) -
      (1 / Real.sqrt 5) * stechkinZeroPair s₁ (riemannXiDivisorZeroValue r)
  have hs : 1 < s.re := by simpa [s] using hσ
  have hs₁ : 1 < s₁.re := by simpa [s₁] using (Real.stechkinShift_spec hσ).1
  have hsum : Summable F := (summable_stechkinZeroPair hs).sub
    ((summable_stechkinZeroPair hs₁).mul_left (1 / Real.sqrt 5))
  have hnonneg (r : RiemannXiDivisorZeroIndex) : 0 ≤ F r :=
    stechkinZeroPair_sub_nonneg hσ (riemannXiDivisorZeroValue_eq_zero r) ρ.im
  have htwo := hsum.sum_le_tsum {p, q} (fun r _ => hnonneg r)
  rw [Finset.sum_pair hpq] at htwo
  have hFq : F q = F p := by simp only [F, hq, hp, stechkinZeroPair_reflect]
  have hpole : 1 / (σ - ρ.re) ≤ F p := by
    simpa only [F, s, s₁, hp] using stechkinZeroPair_aligned_le hσ hρ
  have heq : (∑' r, F r) =
      2 * (logDeriv riemannXi s).re -
        (1 / Real.sqrt 5) * (2 * (logDeriv riemannXi s₁).re) := by
    dsimp only [F]
    rw [(summable_stechkinZeroPair hs).tsum_sub
      ((summable_stechkinZeroPair hs₁).mul_left (1 / Real.sqrt 5)), tsum_mul_left,
      ← two_re_logDeriv_riemannXi_eq_tsum_pair hs,
      ← two_re_logDeriv_riemannXi_eq_tsum_pair hs₁]
  rw [hFq, heq] at htwo
  change 1 / (σ - ρ.re) ≤
    (logDeriv riemannXi s).re - (1 / Real.sqrt 5) * (logDeriv riemannXi s₁).re
  linarith

end

end PrimeFactorUnimodality
