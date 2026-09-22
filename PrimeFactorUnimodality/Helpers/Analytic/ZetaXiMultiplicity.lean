import PrimeFactorUnimodality.Helpers.Analytic.ZetaXiZeros
import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannXiDivisorZeros

/-! # Matching xi multiplicity to the zeta-order count

The shifted gamma prefactor is analytic and nonzero on the right half-plane
away from one, so xi and zeta have the same analytic order there. This
identifies the actual xi divisor weight with the integer order used in
the pinned PNT counting API. No zero-count estimate is imported or assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Filter
open scoped Topology

private def xiCountingFactor (s : ℂ) : ℂ :=
  (s - 1) * Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) * Gamma (s / 2 + 1)

private theorem xiCountingFactor_analyticAt {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ xiCountingFactor s := by
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
  have hΓ : ∀ n : ℕ, z / 2 + 1 ≠ -(n : ℂ) := by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [add_re, div_ofNat_re, one_re, neg_re, natCast_re] at h
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact ((by fun_prop : DifferentiableAt ℂ
    (fun w : ℂ => (w - 1) * Complex.exp (-(w / 2) * (Real.log Real.pi : ℂ))) z).mul
      ((differentiableAt_Gamma _ hΓ).comp z (by fun_prop)))

private theorem xiCountingFactor_ne_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    xiCountingFactor s ≠ 0 := by
  have hΓ : Gamma (s / 2 + 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp only [add_re, div_ofNat_re, one_re]
    linarith)
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hs1) (exp_ne_zero _)) hΓ

/-- The nonvanishing analytic prefactor preserves the complete analytic order. -/
theorem analyticOrderAt_riemannXi_eq_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt riemannXi s = analyticOrderAt riemannZeta s := by
  have heq : riemannXi =ᶠ[𝓝 s] xiCountingFactor * riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs,
      isOpen_compl_singleton.mem_nhds hs1] with z hz hz1
    exact riemannXi_eq_shifted_gamma_product_of_re_pos hz hz1
  have hf := xiCountingFactor_analyticAt hs
  rw [analyticOrderAt_congr heq,
    analyticOrderAt_mul hf (riemannZeta_analyticOn_compl_one s hs1),
    hf.analyticOrderAt_eq_zero.mpr (xiCountingFactor_ne_zero hs hs1), zero_add]

/-- The integer divisor of xi is exactly PNT's zeta-order weight. -/
theorem xi_divisor_eq_zeta_order {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    MeromorphicOn.divisor riemannXi Set.univ s = riemannZeta.order s := by
  rw [Hadamard.divisor_univ_eq_analyticOrderNatAt_int differentiable_riemannXi]
  have hz := riemannZeta_analyticOn_compl_one s hs1
  unfold analyticOrderNatAt riemannZeta.order
  rw [analyticOrderAt_riemannXi_eq_zeta hs hs1, hz.meromorphicOrderAt_eq]
  cases analyticOrderAt riemannZeta s with
  | top => simp
  | coe n =>
      rw [ENat.toNat_natCast, ENat.map_natCast, WithTop.untopD_coe]

/-- The line `Re(s)=1` is excluded as well as the open right half-plane. -/
theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  by_cases hs1 : s = 1
  · have h1 : riemannXi 1 = 1 / 2 := by
      simpa using (riemannXi_one_sub 0).trans riemannXi_zero
    rw [hs1, h1]
    norm_num
  exact fun hz => riemannZeta_ne_zero_of_one_le_re hs
    ((riemannXi_eq_zero_iff_riemannZeta_eq_zero (by linarith) hs1).mp hz)

/-- Every xi zero lies in the open critical strip, by nonvanishing on its boundary. -/
theorem riemannXi_zero_mem_open_critical_strip {s : ℂ} (hs : riemannXi s = 0) :
    0 < s.re ∧ s.re < 1 := by
  have hu {z : ℂ} (hz : riemannXi z = 0) : z.re < 1 :=
    lt_of_not_ge (fun h => riemannXi_ne_zero_of_one_le_re h hz)
  have hl := hu (show riemannXi (1 - s) = 0 by rw [riemannXi_one_sub, hs])
  simp only [sub_re, one_re] at hl
  exact ⟨by linarith, hu hs⟩

/-- Off the real axis every zeta zero is a zero of xi, with no half-plane assumption. -/
theorem riemannXi_eq_zero_of_zeta_zero_of_im_ne_zero {s : ℂ}
    (hi : s.im ≠ 0) (hs : riemannZeta s = 0) : riemannXi s = 0 := by
  have hs0 : s ≠ 0 := by intro h; exact hi (by simp [h])
  have hs1 : s ≠ 1 := by intro h; exact hi (by simp [h])
  have hΓ : Gamma (s / 2) ≠ 0 := Gamma_ne_zero (by
    intro n hn
    have h := congrArg Complex.im hn
    simp only [div_ofNat_im, neg_im, natCast_im, neg_zero] at h
    exact hi (by linarith))
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    completedRiemannZeta_eq_cpow_mul_Gamma_mul_riemannZeta hs0 hΓ, hs]
  simp

end

end PrimeFactorUnimodality
