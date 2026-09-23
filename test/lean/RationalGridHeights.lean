import PrimeFactorUnimodality.Helpers.Analytic.RationalGridHeights

/-! # Real-radius moments and exact rational-grid regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset
open PrimeFactorUnimodality

example (p : ZetaGridPoint) (g : ZetaGridBlock)
    (base span : ℚ) (hb : g.shared.base = (base : ℝ))
    (hr : g.shared.radius = rationalGridRadius span) :
    p.height g = (rationalGridHeight base span g.levels p.index : ℝ) := by
  exact PrimeFactorUnimodality.ZetaGridPoint.height_eq_rational p g base span hb hr

example (base span : ℚ) (levels : ℕ) (hs : 0 < span) :
    StrictMono (rationalGridHeight base span levels) := by
  exact PrimeFactorUnimodality.rationalGridHeight_strictMono base span levels hs

example {g : ZetaGridBlock} (hg : g.Valid)
    (base span : ℚ) (hs : 0 < span) (hb : g.shared.base = (base : ℝ))
    (hr : g.shared.radius = rationalGridRadius span) {p q : ZetaGridPoint}
    (hp : p.Valid g) (hq : q.Valid g) (hij : p.index < q.index) {θ φ δ ε : ℝ}
    (hθ : |turingStirlingPhase (p.height g) - θ| ≤ δ)
    (hφ : |turingStirlingPhase (q.height g) - φ| ≤ ε)
    (hmargin : (p.xiError g δ < p.xiApprox g θ ∧ q.xiApprox g φ < -q.xiError g ε) ∨
      (p.xiApprox g θ < -p.xiError g δ ∧ q.xiError g ε < q.xiApprox g φ)) :
    (rationalGridSignRow base span g.levels p.index q.index).Valid := by
  exact PrimeFactorUnimodality.XiSignRow.valid_of_rational_grid hg base span hs hb hr hp hq hij hθ hφ hmargin

example : rationalGridHeight 100 1 3 (-2) = 399 / 4 := by decide +kernel
example : rationalGridHeight 100 1 3 2 = 401 / 4 := by decide +kernel
example : rationalGridSignRow 100 1 3 (-2) 2 = ⟨399 / 4, 401 / 4⟩ := by decide +kernel
example : StrictMono (rationalGridHeight 100 1 3) := rationalGridHeight_strictMono 100 1 3 (by norm_num)
def rationalBase : ZetaGroupedBlock :=
  ⟨1, 0, 0, 100, rationalGridRadius 1, {0}, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩
def zeroTrace : (levels : ℕ) → Fourier.RadixTrace levels
  | 0 => .leaf 0 0
  | n + 1 => let h := zeroTrace n
    .node h h (Vector.replicate (2 ^ (n + 1)) 0) (Vector.replicate (2 ^ (n + 1)) 0) 0 0 0
def rationalGrid : ZetaGridBlock := ⟨rationalBase, 3, fun _ => zeroTrace 3⟩
example : (ZetaGridPoint.mk (-2) 0 0).height rationalGrid = (399 / 4 : ℝ) := by
  rw [ZetaGridPoint.height_eq_rational _ _ 100 1 rfl rfl]
  norm_num [rationalGridHeight, rationalGrid]

end

end PrimeFactorUnimodality.Tests
