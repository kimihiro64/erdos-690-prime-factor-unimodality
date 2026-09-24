import PrimeFactorUnimodality.Helpers.Analytic.DusartCheckedThetaTrace
import PrimeFactorUnimodality.Helpers.Analytic.DusartCheckpointVerification
import PrimeFactorUnimodality.Helpers.Analytic.DusartEarlierCutoff
import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenThetaChecks
import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenThetaCoverage
import PrimeFactorUnimodality.Helpers.Analytic.DusartReducedZeroVerification
import PrimeFactorUnimodality.Helpers.FiniteCertificates.KadiriTransformNumerical

/-! # Dusart consumers with the R6 scalar bootstrap discharged

Only low-height verification and lower-band data remain explicit. The
certified four-point transforms supply the endpoint chain in every consumer.
The early analytic bridge reduces the lower-band endpoint to three billion.
The original full-ray consumer retains its billion-height interface. New
consumers accept a smaller verified height together with valid scalar rows
covering the bounded logarithmic band. The unbounded tail and the early
bridge then require no additional numerical data.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Actual billion-height low-zero data now suffices for the improved high region. -/
theorem xi_zero_gap_six_of_verified_low
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) : KadiriHighRegion 6 1000000000 :=
  xi_zero_gap_six_of_endpoint_chain kadiriSix_endpoint_chain hlow

/-- The reduced high-region theorem retains its precise smaller low-zero hypothesis. -/
theorem xi_zero_gap_six_of_verified_reduced_low
    (hlow : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) : KadiriHighRegion 6 25000000 :=
  xi_zero_gap_six_of_reduced_endpoint_chain kadiriSix_reduced_endpoint_chain hlow

/-- Verification above the reduced cutoff includes its bootstrap premise. -/
theorem xi_zero_gap_six_of_verified_height {H : ℝ} (hH : 25000000 ≤ H)
    (hlow : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) : KadiriHighRegion 6 H := by
  have hsmall : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ) := by
    intro z hz
    apply hlow z
    rw [mem_xiLowHeightIndices] at hz ⊢
    exact hz.trans_le hH
  intro z hz
  exact xi_zero_gap_six_of_verified_reduced_low hsmall z (hH.trans hz)

/-- The whole far ray needs low-zero verification only at the selected smaller height. -/
theorem hasThetaLogSquaredError_far_of_verified_height {H : ℝ}
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hlow : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) (Real.exp 5000) := by
  apply hasThetaLogSquaredError_far_of_height_le (by linarith) hH₁ hlow
  intro z hz
  linarith [xi_zero_gap_six_of_verified_height hH hlow z hz]

/-- Any proved logarithmic middle band joins the earlier bridge and the whole far ray. -/
theorem hasThetaLogSquaredError_above_earlier_cutoff_of_log_band {H : ℝ}
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hband : ∀ x : ℝ, 0 < x → 25 ≤ Real.log x → Real.log x ≤ 5000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hlow : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3000000000 := by
  have hsmall : ∀ z ∈ xiLowHeightIndices 25000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ) := by
    intro z hz
    apply hlow z
    rw [mem_xiLowHeightIndices] at hz ⊢
    exact hz.trans_le hH
  have hjoin : Real.exp (25 : ℝ) ≤ 1441000000000 := by
    calc
      _ = Real.exp (1 : ℝ) ^ 25 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ (3 : ℝ) ^ 25 := pow_le_pow_left₀ (Real.exp_pos 1).le
        (by linarith [Real.exp_one_lt_d9]) 25
      _ ≤ _ := by norm_num
  intro x hx
  by_cases hearly : x ≤ 1441000000000
  · exact abs_theta_sub_le_logSquared_billion_bridge hx hearly hsmall
  by_cases hfar : Real.exp (5000 : ℝ) ≤ x
  · exact hasThetaLogSquaredError_far_of_verified_height hH hH₁ hlow x hfar
  · have hxpos : 0 < x := by linarith
    have hlo := Real.log_le_log (Real.exp_pos 25) (hjoin.trans (le_of_not_ge hearly))
    have hhi := Real.log_le_log hxpos (le_of_not_ge hfar)
    rw [Real.log_exp] at hlo hhi
    exact hband x hxpos hlo hhi

/-- Scalar rows replace the whole middle-band obligation at the selected verified height. -/
theorem hasThetaLogSquaredError_above_earlier_cutoff_of_frozen_rows {H : ℝ}
    {rows : List DusartFrozenThetaRow}
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hvalid : ∀ row ∈ rows, row.Valid H)
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
  exact hcover.bound hvalid hH hH₁ hlow hreg hx (by simpa using hlo) (by simpa using hhi)

/-- The published cutoff follows from lower finite data and the reduced-height row certificate. -/
theorem hasThetaLogSquaredError_of_lower_band_and_frozen_rows {H : ℝ}
    {rows : List DusartFrozenThetaRow}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 3000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hvalid : ∀ row ∈ rows, row.Valid H)
    (hcoverage : DusartFrozenThetaRow.checkCoverage 25 5000 rows = true)
    (hlow : ∀ z ∈ xiLowHeightIndices H,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  intro x hx
  by_cases h : x ≤ 3000000000
  · exact finite x hx h
  · exact hasThetaLogSquaredError_above_earlier_cutoff_of_frozen_rows
      hH hH₁ hvalid hcoverage hlow x (le_of_not_ge h)

/-- Complete zero-sign data and scalar rows feed the exact reduced-height Dusart provider. -/
theorem hasThetaLogSquaredError_of_frozen_and_turing_rows {H b : ℚ}
    {rows : List DusartFrozenThetaRow} {n : ℕ} {zeros : Fin n → XiSignRow}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 3000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (hvalid : ∀ row ∈ rows, row.Valid H)
    (hcoverage : DusartFrozenThetaRow.checkCoverage 25 5000 rows = true)
    (hzeros : XiSignRows.Valid zeros 0 b) (hb : H ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral H +
      turingCountErrorBudget H b < (b : ℝ) - H + (XiSignRows.completedAreaRat zeros H b : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  have hlow := hzeros.low_criticalLine_of_turing_margin (by linarith : 32 ≤ H) hb hmargin
  exact hasThetaLogSquaredError_of_lower_band_and_frozen_rows finite
    (by exact_mod_cast hH) (by exact_mod_cast hH₁) hvalid hcoverage (fun z hz => (hlow z hz).le)

/-- Kernel-checked scalar expressions and complete Turing rows supply the reduced-height provider. -/
theorem hasThetaLogSquaredError_of_checked_frozen_and_turing_rows {H b : ℚ}
    {rows : List DusartFrozenThetaRow} {n : ℕ} {zeros : Fin n → XiSignRow}
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 3000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hH : 25000000 ≤ H) (hH₁ : H ≤ 1000000000)
    (precision : ℤ) (depth : ℕ) (hprecision : precision ≤ 0)
    (hchecks : ∀ row ∈ rows, row.check H precision depth = true)
    (hcoverage : DusartFrozenThetaRow.checkCoverage 25 5000 rows = true)
    (hzeros : XiSignRows.Valid zeros 0 b) (hb : H ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral H +
      turingCountErrorBudget H b < (b : ℝ) - H + (XiSignRows.completedAreaRat zeros H b : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_frozen_and_turing_rows finite hH hH₁
    (DusartFrozenThetaRow.valid_of_checks H precision depth hprecision hchecks)
    hcoverage hzeros hb hmargin

/-- The complete upper theta ray has no numerical transform or high-region assumption. -/
theorem hasThetaLogSquaredError_above_endpoint_of_verified_low
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 :=
  hasThetaLogSquaredError_above_endpoint_of_bootstrap kadiriSix_endpoint_chain hlow

/-- The full ray starts at three billion with the same low-zero obligation. -/
theorem hasThetaLogSquaredError_above_earlier_cutoff_of_verified_low
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3000000000 := by
  apply hasThetaLogSquaredError_above_earlier_cutoff hlow
  intro z hz
  linarith [xi_zero_gap_six_of_verified_low hlow z hz]

/-- The exact published theta cutoff needs finite data only through three billion. -/
theorem hasThetaLogSquaredError_of_lower_band_and_verified_low
    (finite : ∀ x : ℝ, (3594641 : ℝ) ≤ x → x ≤ 3000000000 →
      |Chebyshev.theta x - x| ≤ (1 / 5 : ℝ) * x / Real.log x ^ 2)
    (hlow : ∀ z ∈ xiLowHeightIndices 1000000000,
      (riemannXiDivisorZeroValue z).re ≤ (1 / 2 : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 := by
  apply hasThetaLogSquaredError_of_earlier_band_and_zero_data finite hlow
  intro z hz
  linarith [xi_zero_gap_six_of_verified_low hlow z hz]

/-- Checked count/log transitions to three billion feed the published global theta theorem. -/
theorem hasThetaLogSquaredError_of_early_prime_trace_and_verified_low
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
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_lower_band_and_verified_low
    (thetaLogSquared_on_band_of_checked_prime_trace hc hs hcounts htrace hpositive hcoverage hp hq)
    hlow

/-- Finite prime traces, scalar checks and Turing data assemble the reduced-height theorem. -/
theorem hasThetaLogSquaredError_of_checked_prime_frozen_turing_rows
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
    (hchecks : ∀ row ∈ rows, row.check H precision depth = true)
    (hscalarCoverage : DusartFrozenThetaRow.checkCoverage 25 5000 rows = true)
    (hzeros : XiSignRows.Valid zeros 0 b) (hb : H ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral H +
      turingCountErrorBudget H b < (b : ℝ) - H + (XiSignRows.completedAreaRat zeros H b : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 3594641 :=
  hasThetaLogSquaredError_of_checked_frozen_and_turing_rows
    (thetaLogSquared_on_band_of_checked_prime_trace hc hs hcounts htrace hpositive hcoverage hp hq)
    hH hH₁ precision depth hprecision hchecks hscalarCoverage hzeros hb hmargin

/-- Turing signs and the complete counting margin give the entire upper theta ray. -/
theorem hasThetaLogSquaredError_above_endpoint_of_verified_turing_rows {n : ℕ}
    {rows : Fin n → XiSignRow} {b : ℚ}
    (hrows : XiSignRows.Valid rows 0 b) (hb : 1000000000 ≤ b)
    (hmargin : xiZeroCountingMainIntegral b - xiZeroCountingMainIntegral 1000000000 +
      turingCountErrorBudget 1000000000 b <
        (b : ℝ) - 1000000000 + (XiSignRows.completedAreaRat rows 1000000000 b : ℝ)) :
    HasThetaLogSquaredError (1 / 5) 1441000000000 :=
  hasThetaLogSquaredError_above_endpoint_of_turing_rows hrows hb hmargin kadiriSix_endpoint_chain

/-- Checkpoint and Turing data feed the published theta provider with no bootstrap assumption. -/
theorem hasThetaLogSquaredError_of_verified_checkpoints_and_turing_rows
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
  have hlow := hrows.low_criticalLine_of_turing_margin (by norm_num) hb hmargin
  apply hasThetaLogSquaredError_of_lower_band_and_verified_low _ (fun z hz => (hlow z hz).le)
  intro x hx hX
  have hp' : (p.point : ℝ) ≤ 3594641 := by exact_mod_cast hp
  have hq' : (3000000000 : ℝ) ≤ q.point := by exact_mod_cast hq
  simpa using hsteps.bound (by norm_num) hpoints (hp'.trans hx) (hX.trans hq')

end

end PrimeFactorUnimodality
