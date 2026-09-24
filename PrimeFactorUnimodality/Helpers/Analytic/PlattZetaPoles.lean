import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaResidue
import PrimeNumberTheoremAnd.IEANTN.KadiriEq12Helpers

set_option autoImplicit false

/-! # The complete pole set in the rightward zeta strip

Gamma has no poles in this window half-plane. Zeta's meromorphicity is the
proved `meromorphicAt_riemannZeta` from the Apache-2.0 PNT dependency at
`f6147e7572ab3abe5428101bc0b13627bcb005df`, `IEANTN.KadiriEq12Helpers`; its only
possible pole here has the nonzero residue already computed. Thus the
rectangle theorem's pole and order hypotheses follow for the actual integrand.
-/

namespace PrimeFactorUnimodality

/-- The Gamma-window and pi-phase factor is analytic throughout the downward half-plane. -/
theorem analyticAt_plattZetaRegularFactor (k : ℕ) (t₀ h x : ℝ) {z : ℂ} (hz : z.im ≤ 0) :
    AnalyticAt ℂ (fun w => plattContourIntegrand k t₀ h x w * plattPiPhase t₀ w) z := by
  have hg := analyticAt_plattContourIntegrand_of_not_pole k t₀ h x (z := z) (by
    intro n he
    have hi := congrArg Complex.im he
    rw [plattGammaPole_im] at hi
    linarith [Nat.cast_nonneg (α := ℝ) n])
  apply hg.mul
  unfold plattPiPhase
  simp only [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')]
  fun_prop

/-- The actual zeta-window integrand is meromorphic on the whole contour strip. -/
theorem meromorphicAt_plattZetaContourIntegrand (k : ℕ) (t₀ h x : ℝ) {z : ℂ}
    (hz : z.im ≤ 0) : MeromorphicAt (plattZetaContourIntegrand k t₀ h x) z := by
  have hζ : MeromorphicAt (fun w => riemannZeta (plattZetaArgument t₀ w)) z :=
    (meromorphicAt_riemannZeta _).comp_analyticAt (by unfold plattZetaArgument; fun_prop)
  exact (analyticAt_plattZetaRegularFactor k t₀ h x hz).meromorphicAt.mul hζ

/-- Away from the single zeta pole, the full integrand is analytic in the strip. -/
theorem analyticAt_plattZetaContourIntegrand (k : ℕ) (t₀ h x : ℝ) {z : ℂ}
    (hz : z.im ≤ 0) (hp : z ≠ plattZetaPole t₀) :
    AnalyticAt ℂ (plattZetaContourIntegrand k t₀ h x) z := by
  have hζ : AnalyticAt ℂ (fun w => riemannZeta (plattZetaArgument t₀ w)) z :=
    (analyticOn_riemannZeta _ (fun he => hp ((plattZetaArgument_eq_one_iff t₀ z).mp he))).comp
      (by unfold plattZetaArgument; fun_prop)
  exact (analyticAt_plattZetaRegularFactor k t₀ h x hz).mul hζ

/-- The nonzero residue makes the crossed pole simple, for every kernel order. -/
theorem meromorphicOrderAt_plattZetaContourIntegrand_pole (k : ℕ) (t₀ h x : ℝ) :
    meromorphicOrderAt (plattZetaContourIntegrand k t₀ h x) (plattZetaPole t₀) = (-1 : ℤ) :=
  (meromorphicAt_plattZetaContourIntegrand k t₀ h x (by simp)).order_eq_neg_one_of_tendsto
    (plattZetaContourResidueValue_ne_zero k t₀ h x) (tendsto_plattZetaContour_residue k t₀ h x)

/-- There are no additional poles or canceled poles in the downward half-plane. -/
theorem meromorphicOrderAt_plattZetaContourIntegrand_neg_iff (k : ℕ) (t₀ h x : ℝ) {z : ℂ}
    (hz : z.im ≤ 0) :
    meromorphicOrderAt (plattZetaContourIntegrand k t₀ h x) z < 0 ↔ z = plattZetaPole t₀ := by
  constructor
  · intro ho
    by_contra hp
    have ha := analyticAt_plattZetaContourIntegrand k t₀ h x hz hp
    exact (not_lt_of_ge ha.meromorphicOrderAt_nonneg) ho
  · rintro rfl
    rw [meromorphicOrderAt_plattZetaContourIntegrand_pole]
    exact_mod_cast (show (-1 : ℤ) < 0 by omega)

/-- Every subset of the contour half-plane satisfies the simple-pole condition. -/
theorem hasSimplePolesOn_plattZetaContourIntegrand (k : ℕ) (t₀ h x : ℝ) (S : Set ℂ)
    (hS : ∀ z ∈ S, z.im ≤ 0) : HasSimplePolesOn (plattZetaContourIntegrand k t₀ h x) S := by
  intro z hz
  by_cases hp : z = plattZetaPole t₀
  · subst z
    rw [meromorphicOrderAt_plattZetaContourIntegrand_pole]
  · exact le_trans (WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by omega))
      (analyticAt_plattZetaContourIntegrand k t₀ h x (hS z hz) hp).meromorphicOrderAt_nonneg

end PrimeFactorUnimodality
