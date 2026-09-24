import PrimeFactorUnimodality.Helpers.Analytic.PlattContourResidues

set_option autoImplicit false

/-! # The exact pole set and pole orders of the contour integrand

Meromorphicity comes from the entire reciprocal of Gamma. The previously
proved nonzero residue limits give order exactly `-1` at every listed point;
the integrand is analytic everywhere else. Thus the simple-pole hypotheses
of the rectangle residue theorem are discharged, not assumed.
-/

namespace PrimeFactorUnimodality

theorem meromorphicAt_plattContourIntegrand (k : ℕ) (t₀ h u : ℝ) (z : ℂ) :
    MeromorphicAt (plattContourIntegrand k t₀ h u) z := by
  have hg : MeromorphicAt (fun z : ℂ => Complex.Gamma (plattGammaArgument t₀ z)) z :=
    (Complex.meromorphicAt_Gamma _).comp_analyticAt (by unfold plattGammaArgument; fun_prop)
  have hp : MeromorphicAt (fun z : ℂ => Complex.Gamma (plattGammaArgument t₀ z) *
      plattContourWeight k t₀ h u z) z :=
    hg.mul (analyticAt_plattContourWeight k t₀ h u z).meromorphicAt
  simpa only [← plattContourIntegrand_eq_gamma_mul_weight] using hp

theorem analyticAt_plattContourIntegrand_of_not_pole (k : ℕ) (t₀ h u : ℝ) {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ plattGammaPole n t₀) :
    AnalyticAt ℂ (plattContourIntegrand k t₀ h u) z := by
  have hg : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (plattGammaArgument t₀ z)) z :=
    (Complex.analyticAt_Gamma_of_not_pole (fun n hn =>
      hz n ((plattGammaArgument_eq_neg_nat_iff n t₀ z).mp hn))).comp
        (by unfold plattGammaArgument; fun_prop)
  have hp : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (plattGammaArgument t₀ z) *
      plattContourWeight k t₀ h u z) z := hg.mul (analyticAt_plattContourWeight k t₀ h u z)
  simpa only [← plattContourIntegrand_eq_gamma_mul_weight] using hp

/-- Each listed pole has exactly order one, for every natural polynomial order. -/
theorem meromorphicOrderAt_plattContourIntegrand_pole (n k : ℕ) (t₀ h u : ℝ) :
    meromorphicOrderAt (plattContourIntegrand k t₀ h u) (plattGammaPole n t₀) = (-1 : ℤ) :=
  (meromorphicAt_plattContourIntegrand k t₀ h u _).order_eq_neg_one_of_tendsto
    (plattContourResidueValue_ne_zero n k t₀ h u) (tendsto_plattContour_residue n k t₀ h u)

/-- No additional or canceled poles occur in the actual integrand. -/
theorem meromorphicOrderAt_plattContourIntegrand_neg_iff (k : ℕ) (t₀ h u : ℝ) (z : ℂ) :
    meromorphicOrderAt (plattContourIntegrand k t₀ h u) z < 0 ↔
      ∃ n : ℕ, z = plattGammaPole n t₀ := by
  constructor
  · intro ho
    by_contra hz
    have ha := analyticAt_plattContourIntegrand_of_not_pole k t₀ h u
      (fun n hn => hz ⟨n, hn⟩)
    exact (not_lt_of_ge ha.meromorphicOrderAt_nonneg) ho
  · rintro ⟨n, rfl⟩
    rw [meromorphicOrderAt_plattContourIntegrand_pole]
    exact_mod_cast (show (-1 : ℤ) < 0 by omega)

/-- The residue theorem's simple-pole condition holds on every region. -/
theorem hasSimplePolesOn_plattContourIntegrand (k : ℕ) (t₀ h u : ℝ) (S : Set ℂ) :
    HasSimplePolesOn (plattContourIntegrand k t₀ h u) S := by
  intro z hz
  by_cases hp : ∃ n : ℕ, z = plattGammaPole n t₀
  · obtain ⟨n, rfl⟩ := hp
    rw [meromorphicOrderAt_plattContourIntegrand_pole]
  · exact le_trans (WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by omega))
      (analyticAt_plattContourIntegrand_of_not_pole k t₀ h u
        (fun n hn => hp ⟨n, hn⟩)).meromorphicOrderAt_nonneg

end PrimeFactorUnimodality
