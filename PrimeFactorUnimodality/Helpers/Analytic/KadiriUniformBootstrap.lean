import PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapMaster
import PrimeFactorUnimodality.Helpers.Analytic.KadiriBootstrapParameters

/-! # A uniform bootstrap from fixed endpoint inputs

The selected real coordinate, scale interval, harmonic cutoff, and transform
interval are derived here for every actual zero above the starting height.
The conclusion covers both signs of the ordinate and the entire critical
strip. Numerical admissibility, moment bounds, low-height locations, and
the two endpoint budgets remain explicit inputs.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Fixed endpoint inputs improve the previous actual region on the complete height ray. -/
theorem xi_zero_gap_of_uniform_moment_budget
    {θ R r T H η₀ σ₀ δ κ y B₀ B₁ B₂ B₃ : ℝ} {n : ℕ}
    (hR : 0 < R) (hr : 0 < r) (hT : 10 ^ 9 ≤ T) (hH : 4 ≤ H) (hn : 1 ≤ n)
    (hθ : π / 2 < θ ∧ θ < π)
    (hηdef : η₀ = 1 / (r * log T)) (hηhalf : η₀ ≤ 1 / 2)
    (hσdef : σ₀ = kadiriBootstrapSigma R n H T) (hσ₀ : 1 / 2 < σ₀)
    (hδ : 1 / 2 ≤ δ) (hκ : 0 ≤ κ) (hκ₁ : κ < 1)
    (hκ₂ : κ ≤ kadiriKappa₂ θ η₀ (2 * σ₀ - 1) δ)
    (hκ₃ : κ ≤ kadiriKappa₃ θ η₀ (2 * σ₀ - 1) δ)
    (hc : 0 < σ₀ - η₀ + δ)
    (hgap : 0 ≤ 2 * σ₀ - 1 - κ * (1 + 2 * δ))
    (hcut : κ * (1 + 2 * δ) + 1 - σ₀ ≤
      (2 * σ₀ - 1 - κ * (1 + 2 * δ)) * H ^ 2)
    (hy : 0 < y) (hdy : kadiriSupport θ ≤ y)
    (hend : exp y ≤ 1 + y + y ^ 2 / 2 + y ^ 3 / (345 / 100))
    (hB₀ : kadiriDerivativeMoment θ 0 ≤ B₀) (hB₁ : kadiriDerivativeMoment θ 1 ≤ B₁)
    (hB₂ : kadiriDerivativeMoment θ 2 ≤ B₂) (hB₃ : kadiriDerivativeMoment θ 3 ≤ B₃)
    (a : ℕ → ℝ) (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) (ha₁ : 0 < a 1)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ Finset.range (n + 1), a i * Real.cos ((i : ℝ) * u))
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < T → (riemannXiDivisorZeroValue p).re ≤ σ₀)
    (hhigh : ∀ p : RiemannXiDivisorZeroIndex,
      T ≤ |(riemannXiDivisorZeroValue p).im| →
        1 / (R * log |(riemannXiDivisorZeroValue p).im|) ≤
          1 - (riemannXiDivisorZeroValue p).re)
    (hbudget : kadiriMomentCorrectionPolynomial θ η₀ η₀ σ₀ κ δ (-1) H T
      B₀ B₁ B₂ B₃ (1 / r) (Finset.range (n + 1)) a ≤ 0)
    (hmargin : kadiriBootstrapLogCoefficient θ κ (Finset.range (n + 1)) a / r ≤
      a 1 * kadiriKernelExpIntegral θ (kadiriBootstrapLowerArgument R r n H T - 1) -
        a 0 * kadiriKernelExpIntegral θ 1)
    (p : RiemannXiDivisorZeroIndex) (hp : T ≤ |(riemannXiDivisorZeroValue p).im|) :
    1 / (r * log |(riemannXiDivisorZeroValue p).im|) ≤
      1 - (riemannXiDivisorZeroValue p).re := by
  have hTone : 1 < T := by linarith
  have hHpos : 0 < H := by linarith
  have hpositive (q : RiemannXiDivisorZeroIndex)
      (hq : T ≤ (riemannXiDivisorZeroValue q).im) :
      1 / (r * log (riemannXiDivisorZeroValue q).im) ≤
        1 - (riemannXiDivisorZeroValue q).re := by
    let t := (riemannXiDivisorZeroValue q).im
    let η := 1 - (riemannXiDivisorZeroValue q).re
    let σ := kadiriBootstrapSigma R n H t
    have ht : 1 < t := hTone.trans_le hq
    have htpos : 0 < t := by linarith
    have habs : |(riemannXiDivisorZeroValue q).im| = t := abs_of_pos htpos
    have hprior : 1 / (R * log t) ≤ η := by simpa only [habs] using hhigh q (by simpa only [habs])
    have hη : 0 < η := (one_div_pos.mpr (mul_pos hR (log_pos ht))).trans_le hprior
    by_cases hdone : 1 / (r * log t) ≤ η
    · exact hdone
    have hsmall : η ≤ 1 / (r * log t) := (lt_of_not_ge hdone).le
    have hscale : η ≤ η₀ := by
      rw [hηdef]
      exact kadiriBootstrapScale_le_endpoint hr hTone hq hsmall
    by_cases hβ : 1 / 2 < (riemannXiDivisorZeroValue q).re
    swap
    · have hmax : 1 / (r * log t) ≤ η₀ := by
        rw [hηdef]
        exact kadiriBootstrapScale_le_endpoint hr hTone hq le_rfl
      dsimp only [η] at hsmall
      linarith only [hβ, hmax, hηhalf]
    have hσ : σ₀ ≤ σ := by
      rw [hσdef]
      exact kadiriBootstrapSigma_le hR hn hHpos.le hTone hq
    have hσ₁ : σ ≤ 1 := (kadiriBootstrapSigma_lt_one hR hn hHpos.le ht).le
    have hw := kadiriBootstrapArgument_mem_Icc hR hr hn hHpos.le hTone hq hη hprior hsmall
    have hz : (-1 : ℝ) ≤ (σ - 1) / η := by
      have heq : (σ - 1) / η = -((1 - σ) / η) := by ring
      rw [heq]
      linarith only [hw.2]
    exact xi_zero_gap_of_moment_budget hR hTone hθ hη hscale hσ₀ hσ hσ₁ hδ
      hκ hκ₁.le hκ₂ hκ₃ hc hz hHpos hgap hcut
      (Finset.range (n + 1)) (by simp) (by simp; omega) a ha q hβ rfl hpoly
      (show 1 - 1 / (R * log ((n : ℝ) * t + H)) ≤ σ from le_rfl)
      (fun j hj => (hlow j hj).trans hσ) hhigh
      (fun i hi => kadiri_harmonics_le_cutoff hi htpos.le) (hT.trans hq)
      hr hκ₁ ha₁ (by linarith) hq hH hy (by simpa using hdy) hend
      hB₀ hB₁ hB₂ hB₃ hw hbudget hmargin
  by_cases ht : 0 ≤ (riemannXiDivisorZeroValue p).im
  · simpa only [abs_of_nonneg ht] using hpositive p (by simpa only [abs_of_nonneg ht] using hp)
  · have ht' : (riemannXiDivisorZeroValue p).im < 0 := lt_of_not_ge ht
    have hq : T ≤ (riemannXiDivisorZeroValue (riemannXiDivisorConjugation p)).im := by
      simpa only [riemannXiDivisorZeroValue_conjugation, Complex.conj_im, abs_of_neg ht'] using hp
    simpa only [riemannXiDivisorZeroValue_conjugation, Complex.conj_re,
      Complex.conj_im, abs_of_neg ht']
      using hpositive (riemannXiDivisorConjugation p) hq

end

end PrimeFactorUnimodality
