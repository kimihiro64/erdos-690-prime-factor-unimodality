import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set

/-! A fixed real-axis estimate used when making the numerical zeta constants
    in the explicit formula chain concrete. -/
theorem riemannZeta_norm_real_le_three_div_sub_one
    {σ : Real} (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖riemannZeta (σ : Complex)‖ ≤ 3 / (σ - 1) := by
  have hσne : (σ : Complex) ≠ 1 := by
    intro h
    have : σ = 1 := by exact_mod_cast congrArg Complex.re h
    linarith
  have hσdom : (σ : Complex) ∈ zetaAbelContinuationDomain :=
    mem_zetaAbelContinuationDomain_of_re hσne (by
      change (1 / 10 : Real) < σ
      linarith)
  have hbound := norm_riemannZeta_le (σ : Complex) hσdom
  have hσpos : 0 < σ := by linarith
  have hsubpos : 0 < σ - 1 := by linarith
  have hnorm : ‖(σ : Complex)‖ = σ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσpos]
  have hnormsub : ‖(σ : Complex) - 1‖ = σ - 1 := by
    rw [show (σ : Complex) - 1 = (σ - 1 : Real) by norm_num,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsubpos]
  have hre : (σ : Complex).re = σ := by rfl
  rw [hnormsub, hnorm, hre] at hbound
  have hσne0 : σ ≠ 0 := ne_of_gt hσpos
  have hratio : σ / σ = (1 : Real) := by field_simp
  rw [hratio] at hbound
  apply le_trans hbound
  apply (div_le_div_iff₀ hsubpos).2
  nlinarith [hσ₂]

theorem riemannZeta_near_one_explicit :
    ∀ (σ : Real), σ ∈ Ioc 1 2 →
      ‖riemannZeta (σ : Complex)‖ ≤ 3 / (σ - 1) := by
  intro σ hσ
  exact riemannZeta_norm_real_le_three_div_sub_one hσ.1 hσ.2

theorem zetaNear1BndExact_explicit :
    ∃ (c : Real), 0 < c ∧ ∀ (σ : Real), σ ∈ Ioc 1 2 →
      ‖riemannZeta (σ : Complex)‖ ≤ c / (σ - 1) := by
  refine ⟨3, by norm_num, ?_⟩
  exact riemannZeta_near_one_explicit

end
end PrimeFactorUnimodality
