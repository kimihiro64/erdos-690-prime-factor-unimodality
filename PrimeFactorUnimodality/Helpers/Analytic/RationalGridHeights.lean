import PrimeFactorUnimodality.Helpers.Analytic.XiGridEvaluation

/-! # Exact rational ordinate grids for the existing xi sign rows

Choosing radius `span/(2*pi)` cancels the Fourier coordinate's pi factor.
This is an exact identity, not rational rounding of a sample height. Positive
spans preserve the order of every signed grid index, including negative ones.
-/

namespace PrimeFactorUnimodality

/-- A real radius chosen to make Fourier sample heights exactly rational. -/
noncomputable def rationalGridRadius (span : ℚ) : ℝ := (span : ℝ) / (2 * Real.pi)

/-- The rational ordinate represented by a signed Fourier-grid index. -/
def rationalGridHeight (base span : ℚ) (levels : ℕ) (index : ℤ) : ℚ :=
  base + span * index / (2 : ℚ) ^ levels

/-- The original Fourier height is exactly the stored rational ordinate. -/
theorem ZetaGridPoint.height_eq_rational (p : ZetaGridPoint) (g : ZetaGridBlock)
    (base span : ℚ) (hb : g.shared.base = (base : ℝ))
    (hr : g.shared.radius = rationalGridRadius span) :
    p.height g = (rationalGridHeight base span g.levels p.index : ℝ) := by
  have hscale : g.shared.radius = ((span : ℝ) / (2 : ℝ) ^ g.levels) *
      (2 : ℝ) ^ g.levels / (2 * Real.pi) := by
    rw [hr, rationalGridRadius]
    field_simp
  rw [p.height_of_radius hscale, hb]
  unfold rationalGridHeight
  push_cast
  ring

/-- Positive spans give strictly increasing rational heights at all signed indices. -/
theorem rationalGridHeight_strictMono (base span : ℚ) (levels : ℕ) (hs : 0 < span) :
    StrictMono (rationalGridHeight base span levels) := by
  intro i j hij
  unfold rationalGridHeight
  apply add_lt_add_of_le_of_lt le_rfl
  apply div_lt_div_of_pos_right _ (by positivity)
  exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) hs

/-- Increasing grid indices give a rational sign-row interval with the exact sampled endpoints. -/
def rationalGridSignRow (base span : ℚ) (levels : ℕ) (i j : ℤ) : XiSignRow :=
  ⟨rationalGridHeight base span levels i, rationalGridHeight base span levels j⟩

/-- The existing xi sign-row verifier consumes these exact grid heights without an equality gap. -/
theorem XiSignRow.valid_of_rational_grid {g : ZetaGridBlock} (hg : g.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : g.shared.base = (base : ℝ))
    (hr : g.shared.radius = rationalGridRadius span) {p q : ZetaGridPoint}
    (hp : p.Valid g) (hq : q.Valid g) (hij : p.index < q.index) {θ φ δ ε : ℝ}
    (hθ : |turingStirlingPhase (p.height g) - θ| ≤ δ)
    (hφ : |turingStirlingPhase (q.height g) - φ| ≤ ε)
    (hmargin : (p.xiError g δ < p.xiApprox g θ ∧ q.xiApprox g φ < -q.xiError g ε) ∨
      (p.xiApprox g θ < -p.xiError g δ ∧ q.xiError g ε < q.xiApprox g φ)) :
    (rationalGridSignRow base span g.levels p.index q.index).Valid := by
  exact XiSignRow.valid_of_grid_endpoints (rationalGridHeight_strictMono base span g.levels hs hij)
    hg hg hp hq (p.height_eq_rational g base span hb hr) (q.height_eq_rational g base span hb hr)
    hθ hφ hmargin

end PrimeFactorUnimodality
