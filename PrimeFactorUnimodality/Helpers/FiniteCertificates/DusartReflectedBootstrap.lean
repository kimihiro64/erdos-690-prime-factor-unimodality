import PrimeFactorUnimodality.Helpers.Analytic.DusartReflectedThetaChecks
import PrimeFactorUnimodality.Helpers.FiniteCertificates.DusartVerifiedBootstrap

/-! # Reflected scalar rows feed the exact reduced-height Dusart provider

The shared bridge and unbounded-tail theorem are unchanged. Reflected rows
replace only the middle-band estimate. The final consumer accepts actual
prime traces, checked scalar rows, and complete Turing data at the selected
height, with no additional high-region or middle-band premise.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Reflected rows join the earlier bridge and the complete far ray at any admissible height. -/
theorem hasThetaLogSquaredError_above_earlier_cutoff_of_reflected_rows {H : ℝ}
    {rows : List DusartFrozenThetaRow}
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hvalid : ∀ row ∈ rows, row.ReflectedValid H)
    (hcoverage : DusartFrozenThetaRow.checkCoverage 25 5000 rows = true)
    (hlow : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3000000000 := by
  have hcover := DusartFrozenThetaRow.covers_of_checkCoverage hcoverage
  have hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (6 * Real.log |(riemannXiDivisorZeroValue z).im|) := by
    intro z hz
    linarith [xi_zero_gap_six_of_verified_height hH hlow z hz]
  apply hasThetaLogSquaredError_above_earlier_cutoff_of_log_band hH hH₁ _ hlow
  intro x hx hlo hhi
  exact hcover.reflected_bound hvalid hH hH₁ hlow hreg hx
    (by simpa using hlo) (by simpa using hhi)

/-- Lower finite data and reflected rows give the published cutoff with the same coefficient. -/
theorem hasThetaLogSquaredError_of_lower_band_and_reflected_rows {H : ℝ}
    {rows : List DusartFrozenThetaRow}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 3000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hvalid : ∀ row ∈ rows, row.ReflectedValid H)
    (hcoverage : DusartFrozenThetaRow.checkCoverage 25 5000 rows = true)
    (hlow : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  intro x hx
  by_cases h : x ≤ 3000000000
  · exact finite x hx h
  · exact hasThetaLogSquaredError_above_earlier_cutoff_of_reflected_rows
      hH hH₁ hvalid hcoverage hlow x (le_of_not_ge h)

/-- Prime traces, checked reflected caps and complete Turing data give the full theta ray. -/
theorem hasThetaLogSquaredError_of_checked_prime_reflected_turing_rows
    {c : SharedTaylorIntervals} (hc : c.Prepared)
    {start p q : ThetaPrimeCheckpoint} (hs : start.Valid)
    {points : List ThetaPrimeCheckpoint}
    (hcounts : ∀ s ∈ p :: points, Nat.primeCounting s.point = s.count)
    (htrace : ThetaPrimeCheckpoint.checkTrace c start (p :: points) = true)
    (hpositive : ∀ s ∈ p :: points, 2 ≤ s.point ∧ 0 < s.log.hi)
    (hcoverage : ThetaSquaredCheckpoint.checkFrom (1 / 5) p.squared q.squared
      (points.map ThetaPrimeCheckpoint.squared) = true)
    (hp : p.point ≤ 3594641) (hq : 3000000000 ≤ q.point)
    {H b : ℚ} {rows : List DusartFrozenThetaRow} {n : ℕ} {zeros : Fin n → XiSignRow}
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (precision : ℤ) (depth : ℕ) (hprecision : precision ≤ 0)
    (hchecks : ∀ row ∈ rows, row.checkReflected H precision depth = true)
    (hscalarCoverage : DusartFrozenThetaRow.checkCoverage 25 5000 rows = true)
    (hzeros : XiSignRows.Valid zeros 0 b) (hb : H ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral H +
      turingCountErrorBudget H b < (b : ℝ) - H + (XiSignRows.completedAreaRat zeros H b : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  have hlow := hzeros.low_criticalLine_of_turing_margin (by linarith : 32 ≤ H) hb hmargin
  exact hasThetaLogSquaredError_of_lower_band_and_reflected_rows
    (thetaLogSquared_on_band_of_checked_prime_trace hc hs hcounts htrace hpositive hcoverage hp hq)
    (by exact_mod_cast hH) (by exact_mod_cast hH₁)
    (DusartFrozenThetaRow.reflectedValid_of_checks H precision depth hprecision hchecks)
    hscalarCoverage (fun z hz => (hlow z hz).le)

end

end PrimeFactorUnimodality
