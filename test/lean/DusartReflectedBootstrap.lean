import PrimeFactorUnimodality.Helpers.FiniteCertificates.DusartReflectedBootstrap

/-! # Shared geometry, invalid heights, and complete reflected-provider regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

private def reflectedTestRow : DusartFrozenThetaRow :=
  ⟨1320, 1330, 6, 10976271349328789 / 500000000000000000000000,
    9280000000000001 / 1000000000000000⟩

example : reflectedTestRow.Geometry :=
  DusartFrozenThetaRow.geometry_of_checkGeometry (by decide +kernel)

set_option maxRecDepth 100000 in
private theorem reflectedTestRow_checked :
    reflectedTestRow.checkReflected 170000000 (-50) 10 = true := by decide +kernel

example : reflectedTestRow.ReflectedValid 170000000 :=
  reflectedTestRow.reflectedValid_of_check 170000000 (-50) 10 (by norm_num) reflectedTestRow_checked

example : reflectedTestRow.checkReflected 0 (-50) 10 = false := by decide +kernel

example : reflectedTestRow.checkReflected (-1) (-50) 10 = false := by decide +kernel

example : (DusartFrozenThetaRow.mk 1320 1330 6 0 (232 / 25)).checkReflected
    170000000 (-50) 10 = false := by decide +kernel

example {row : DusartFrozenThetaRow} {H : ℚ} {precision : ℤ} {depth : ℕ}
    (hp : precision ≤ 0) (hc : row.checkReflected H precision depth = true) : row.ReflectedValid H :=
  row.reflectedValid_of_check H precision depth hp hc

example {a b c : ℚ} {left right : List DusartFrozenThetaRow}
    (hl : DusartFrozenThetaRow.Covers a b left) (hr : DusartFrozenThetaRow.Covers b c right) :
    DusartFrozenThetaRow.Covers a c (left ++ right) := hl.append hr

example {c : SharedTaylorIntervals} (hc : c.Prepared)
    {start p q : ThetaPrimeCheckpoint} (hs : start.Valid)
    {points : List ThetaPrimeCheckpoint}
    (hcounts : ∀ s ∈ p :: points, Nat.primeCounting s.point = s.count)
    (htrace : ThetaPrimeCheckpoint.checkTrace c start (p :: points) = true)
    (hpositive : ∀ s ∈ p :: points, 2 ≤ s.point ∧ 0 < s.log.hi)
    (hcoverage : ThetaSquaredCheckpoint.checkFrom (1 / 5) p.squared q.squared
      (points.map ThetaPrimeCheckpoint.squared) = true)
    (hp : p.point ≤ 3594641) (hq : 3000000000 ≤ q.point)
    {rows : List DusartFrozenThetaRow} {n : ℕ} {zeros : Fin n → XiSignRow} {b : ℚ}
    (hchecks : ∀ row ∈ rows, row.checkReflected 170000000 (-50) 10 = true)
    (hscalarCoverage : DusartFrozenThetaRow.checkCoverage 25 5000 rows = true)
    (hzeros : XiSignRows.Valid zeros 0 b) (hb : 170000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 170000000 +
      turingCountErrorBudget 170000000 b <
        (b : ℝ) - 170000000 + (XiSignRows.completedAreaRat zeros 170000000 b : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_checked_prime_reflected_turing_rows hc hs hcounts htrace
    hpositive hcoverage hp hq (by norm_num) (by norm_num) (-50) 10 (by norm_num)
    hchecks hscalarCoverage hzeros hb hmargin

end

end PrimeFactorUnimodality.Tests
