import PrimeFactorUnimodality.Helpers.Analytic.PackedXiGridMargins

/-! # Packed margin checks preserve every input and completeness obligation -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

example {n : ℕ} {p : PackedXiGridMargins n} {sample : Fin n → XiGridSignData}
    {c : SharedXiGridCheck} (hp : p.Valid sample c) (h : p.check = true) (i : Fin n) :
    (sample i).checkCardinalMargin c.rows c.model.degree c.pi c.errors.cap = true :=
  p.margins_of_check hp h i

example {n : ℕ} (s : XiGridSignBlock n) (c : SharedXiGridCheck)
    {p : PackedXiGridMargins (n + 1)} (hp : p.Valid (fun i => s.sample[i.val]) c)
    (hm : p.check = true) (hi : s.checkInputs c = true) : s.check c = true :=
  s.check_of_packedMargins c hp hm hi

example {n : ℕ} (s : XiGridSignBlock n)
    {c : SharedXiGridCheck} (hc : c.Valid) (base span : ℚ) (hs : 0 < span)
    (hb : c.model.base = (base : ℝ)) (hr : c.model.radius = rationalGridRadius span)
    {p : PackedXiGridMargins (n + 1)} (hp : p.Valid (fun i => s.sample[i.val]) c)
    (hm : p.check = true) (hi : s.checkInputs c = true) {a b : ℚ}
    (hplace : s.checkPlacement base span c.rows.levels 0 b = true)
    {d : TuringMarginIntervals} (hd : d.Valid)
    (hmargin : d.check c.scalar a b
      (XiSignRows.completedAreaRat (s.rows base span c.rows.levels) a b) = true) :
    ∀ q ∈ xiLowHeightIndices (a : ℝ), (riemannXiDivisorZeroValue q).re = 1 / 2 :=
  s.low_criticalLine_of_packedChecks hc base span hs hb hr hp hm hi hplace hd hmargin

end PrimeFactorUnimodality.Tests
