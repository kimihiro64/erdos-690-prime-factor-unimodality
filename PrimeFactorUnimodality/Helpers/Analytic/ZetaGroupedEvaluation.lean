import PrimeFactorUnimodality.Helpers.Analytic.ZetaGroupedData

/-! # Complete zeta error from shared frequency-group moments

The same checked block supports every valid point in its window. Combine
the actual finite Dirichlet error, the short Euler correction and the full
analytic remainder without assuming an approximation of the long sum.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset

/-- All finite-evaluation errors bound the actual arbitrary-order Euler approximation. -/
theorem ZetaGroupedPoint.Valid.norm_euler_sub_value_le {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) :
    ‖zetaEulerApproxOrder d.cutoff ((1 / 2 : ℂ) + p.height d * I) d.order - p.value d‖ ≤
      p.roundingBudget d := by
  have hprefix := norm_dirichlet_sum_sub_rounded_with_centers_le (Icc 1 d.cutoff)
    (fun n hn => (mem_Icc.mp hn).1) (s := d.center) (by norm_num [ZetaGroupedBlock.center])
    d.radius d.groups d.bin (fun b : ℤ => b) hd.covers (by norm_num) hp.window hd.residual
    d.degree d.coefficient p.phase d.coefficientError p.phaseError hd.moments hp.phases
  have he : d.center + (d.radius * p.coordinate : ℝ) * I =
      (1 / 2 : ℂ) + p.height d * I := by
    simp only [ZetaGroupedBlock.center, ZetaGroupedPoint.height, ofReal_add, ofReal_mul]
    ring
  rw [he] at hprefix
  have hcard : (Icc 1 d.cutoff).card = d.cutoff := by simp
  rw [hcard] at hprefix
  rw [zetaEulerApproxOrder_eq_prefix_add_correction _ _ (by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr)]
  unfold ZetaGroupedPoint.value ZetaGroupedPoint.roundingBudget
  rw [add_sub_add_comm]
  exact (norm_add_le _ _).trans (add_le_add hprefix hp.correction)

/-- The shared block evaluator encloses actual zeta at every valid sample point. -/
theorem ZetaGroupedPoint.Valid.norm_zeta_sub_value_le {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) :
    ‖riemannZeta ((1 / 2 : ℂ) + p.height d * I) - p.value d‖ ≤ p.error d := by
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (zetaEulerApproxOrder d.cutoff ((1 / 2 : ℂ) + p.height d * I) d.order) _).trans
    (add_le_add (norm_riemannZeta_sub_eulerApproxOrder_le hd.cutoff_pos (by norm_num)
      (by intro he; have hr := congrArg Complex.re he; norm_num at hr) d.order)
      (hp.norm_euler_sub_value_le hd))

/-- A checked shared block has a nonnegative complete error at every valid point. -/
theorem ZetaGroupedPoint.Valid.error_nonneg {d : ZetaGroupedBlock}
    (hd : d.Valid) {p : ZetaGroupedPoint} (hp : p.Valid d) : 0 ≤ p.error d :=
  (norm_nonneg _).trans (hp.norm_zeta_sub_value_le hd)

end

end PrimeFactorUnimodality
