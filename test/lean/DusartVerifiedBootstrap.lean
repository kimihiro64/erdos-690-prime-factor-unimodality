import PrimeFactorUnimodality.Helpers.FiniteCertificates.DusartVerifiedBootstrap

/-! # Earlier analytic cutoff interfaces and seam regressions -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Real ThetaPrimeCheckpoint

private def frozenTestRow (lo hi : ℚ) : DusartFrozenThetaRow := ⟨lo, hi, 3, 1 / 50000000, 157 / 25⟩

example : DusartFrozenThetaRow.checkCoverage 25 5000 [] = false := by decide

example : DusartFrozenThetaRow.checkCoverage 25 5000
    [frozenTestRow 25 100, frozenTestRow 100 5000] = true := by decide

example : DusartFrozenThetaRow.checkCoverage 25 5000
    [frozenTestRow 25 100, frozenTestRow 101 5000] = false := by decide

example : DusartFrozenThetaRow.checkCoverage 25 5000
    [frozenTestRow 25 100, frozenTestRow 99 5000] = false := by decide

example : DusartFrozenThetaRow.checkCoverage 25 5000
    [frozenTestRow 25 100, frozenTestRow 100 99, frozenTestRow 99 5000] = false := by decide

example {a b c : ℚ} {left right : List DusartFrozenThetaRow}
    (hl : DusartFrozenThetaRow.Covers a b left) (hr : DusartFrozenThetaRow.Covers b c right) :
    DusartFrozenThetaRow.Covers a c (left ++ right) := hl.append hr

example {rows : List DusartFrozenThetaRow}
    (hvalid : ∀ row ∈ rows, row.Valid 200000000)
    (hcoverage : DusartFrozenThetaRow.checkCoverage 25 5000 rows = true)
    (hlow : ∀ z ∈ xiLowHeightIndices 200000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3000000000 :=
  hasThetaLogSquaredError_above_earlier_cutoff_of_frozen_rows
    (by norm_num) (by norm_num) hvalid hcoverage hlow

example {rows : List DusartFrozenThetaRow} {n : ℕ} {zeros : Fin n → XiSignRow} {b : ℚ}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 3000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / log x ^ 2)
    (hvalid : ∀ row ∈ rows, row.Valid 200000000)
    (hcoverage : DusartFrozenThetaRow.checkCoverage 25 5000 rows = true)
    (hzeros : XiSignRows.Valid zeros 0 b) (hb : 200000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 200000000 +
      turingCountErrorBudget 200000000 b <
        (b : ℝ) - 200000000 + (XiSignRows.completedAreaRat zeros 200000000 b : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_frozen_and_turing_rows (H := 200000000) finite
    (by norm_num) (by norm_num) (by simpa using hvalid) hcoverage hzeros hb hmargin

example {H : ℝ} (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hlow : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) (exp 5000) :=
  hasThetaLogSquaredError_far_of_verified_height hH hH₁ hlow

example
    (hlow : ∀ z ∈ xiLowHeightIndices 200000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) (exp 5000) :=
  hasThetaLogSquaredError_far_of_verified_height (by norm_num) (by norm_num) hlow

example
    (hlow : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) (exp 5000) :=
  hasThetaLogSquaredError_far_of_verified_height le_rfl (by norm_num) hlow

example
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) : KadiriHighRegion 6 1000000000 := by
  exact PrimeFactorUnimodality.xi_zero_gap_six_of_verified_low hlow

example
    (hlow : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) : KadiriHighRegion 6 25000000 := by
  exact PrimeFactorUnimodality.xi_zero_gap_six_of_verified_reduced_low hlow

example
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_above_endpoint_of_verified_low hlow

example
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3000000000 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_above_earlier_cutoff_of_verified_low hlow

example
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 3000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_of_lower_band_and_verified_low finite hlow

example
    {c : SharedTaylorIntervals} (hc : c.Prepared)
    {start p q : ThetaPrimeCheckpoint} (hs : start.Valid)
    {points : List ThetaPrimeCheckpoint}
    (hcounts : ∀ s ∈ p :: points, Nat.primeCounting s.point = s.count)
    (htrace : ThetaPrimeCheckpoint.checkTrace c start (p :: points) = true)
    (hpositive : ∀ s ∈ p :: points, 2 ≤ s.point ∧ 0 < s.log.hi)
    (hcoverage : ThetaSquaredCheckpoint.checkFrom (1 / 5) p.squared q.squared
      (points.map ThetaPrimeCheckpoint.squared) = true)
    (hp : p.point ≤ 3594641) (hq : 3000000000 ≤ q.point)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_of_early_prime_trace_and_verified_low hc hs hcounts htrace hpositive hcoverage hp hq hlow

example {n : ℕ}
    {rows : Fin n → XiSignRow} {b : ℚ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_above_endpoint_of_verified_turing_rows hrows hb hmargin

example
    {p q : ThetaSquaredCheckpoint} {points : List ThetaSquaredCheckpoint}
    (hpoints : ∀ r ∈ points, r.Valid)
    (hsteps : ThetaSquaredCheckpoint.Chain (1 / 5) p q points)
    (hp : p.point ≤ 3594641) (hq : 3000000000 ≤ q.point)
    {n : ℕ} {rows : Fin n → XiSignRow} {b : ℚ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  exact PrimeFactorUnimodality.hasThetaLogSquaredError_of_verified_checkpoints_and_turing_rows hpoints hsteps hp hq hrows hb hmargin

example (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 1441000000000 →
    |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_lower_band_and_verified_low
    (fun x hx hX => finite x hx (hX.trans (by norm_num))) hlow

end

end PrimeFactorUnimodality.Tests
