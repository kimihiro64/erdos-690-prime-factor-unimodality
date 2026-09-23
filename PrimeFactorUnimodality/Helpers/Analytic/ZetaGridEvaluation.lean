import PrimeFactorUnimodality.Helpers.Analytic.ZetaGridData

/-! # Actual zeta bounds from a shared checked Fourier block

The grouped approximation error and the complete recursive transform
error are added before deriving any value or sign of actual zeta.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Fourier

/-- One checked transform family bounds every grid sample without recomputing its moments. -/
theorem ZetaGridBlock.Valid.norm_grouped_sub_value_le {d : ZetaGridBlock} (hd : d.Valid)
    (p : ZetaGridPoint) :
    ‖(p.asGrouped d).value d.shared - p.value d‖ ≤ p.transformError d := by
  have h := norm_exp_polynomial_grid_sub_traces_le d.levels d.shared.degree d.shared.groups
    d.shared.coefficient d.trace hd.2 p.index
  simpa only [ZetaGridPoint.asGrouped, ZetaGroupedPoint.value, ZetaGridPoint.value,
    ZetaGridPoint.transformError, ZetaGridPoint.coordinate, add_sub_add_right_eq_sub] using h

/-- The actual zeta value is enclosed with every analytic and numerical error retained. -/
theorem ZetaGridPoint.Valid.norm_zeta_sub_value_le {d : ZetaGridBlock} (hd : d.Valid)
    {p : ZetaGridPoint} (hp : p.Valid d) :
    ‖riemannZeta ((1 / 2 : ℂ) + p.height d * I) - p.value d‖ ≤ p.error d := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ ((p.asGrouped d).value d.shared) _).trans
    (add_le_add (hp.asGrouped.norm_zeta_sub_value_le hd.1) (hd.norm_grouped_sub_value_le p))

/-- Valid data cannot claim a negative complete error budget. -/
theorem ZetaGridPoint.Valid.error_nonneg {d : ZetaGridBlock} (hd : d.Valid)
    {p : ZetaGridPoint} (hp : p.Valid d) : 0 ≤ p.error d :=
  (norm_nonneg _).trans (hp.norm_zeta_sub_value_le hd)

/-- Choosing the block scale this way gives exact arithmetic-progression heights. -/
theorem ZetaGridPoint.height_of_radius {d : ZetaGridBlock} (p : ZetaGridPoint) {h : ℝ}
    (hr : d.shared.radius = h * (2 ^ d.levels) / (2 * Real.pi)) :
    p.height d = d.shared.base + h * p.index := by
  unfold ZetaGridPoint.height ZetaGridPoint.coordinate
  rw [hr]
  congr 1
  field_simp

end

end PrimeFactorUnimodality
