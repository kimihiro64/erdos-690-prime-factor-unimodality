import PrimeFactorUnimodality.Helpers.Analytic.KadiriZeroSums
import PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeInitial

/-! # Outer-zero separation from a numerical region and low-height data

The cutoff strip contains every zero below the cutoff: use the numerical
region at high heights and a separate low-height upper bound. The actual
multiplicity-preserving reflection supplies the other side of the strip.
The initial specialization uses the proved constant `56`, not an assumed
high-height region. The finite low-height input is still explicit.

This implements the separation behind the choice of `sigma` in equation
(2.1) of Mossinghoff--Trudgian, arXiv:1410.3926, for any finite harmonic set.
It does not assert their final numerical constant or low-height verification.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Real
open scoped ComplexConjugate

/-- A right-edge bound below a cutoff also gives the left edge by actual divisor reflection. -/
theorem kadiriCentralStrip_of_upper_below {A σ : ℝ}
    (hupper : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < A → (riemannXiDivisorZeroValue p).re ≤ σ)
    {p : RiemannXiDivisorZeroIndex} (hp : |(riemannXiDivisorZeroValue p).im| < A) :
    kadiriCentralStrip σ (riemannXiDivisorZeroValue p) := by
  have hr := hupper (riemannXiDivisorSameHeightReflection p) (by simpa using hp)
  simp only [riemannXiDivisorZeroValue_sameHeightReflection, sub_re, one_re, conj_re] at hr
  exact ⟨by linarith, hupper p hp⟩

/-- The high region and low data give absolute-height separation by logarithmic monotonicity. -/
theorem kadiri_outer_separation_of_region {R T A σ : ℝ} (hR : 0 < R) (hT : 1 < T)
    (hσ : 1 - 1 / (R * Real.log A) ≤ σ)
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < T → (riemannXiDivisorZeroValue p).re ≤ σ)
    (hhigh : ∀ p : RiemannXiDivisorZeroIndex,
      T ≤ |(riemannXiDivisorZeroValue p).im| →
        1 / (R * Real.log |(riemannXiDivisorZeroValue p).im|) ≤
          1 - (riemannXiDivisorZeroValue p).re)
    (p : RiemannXiDivisorZeroIndex) (hp : ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p)) :
    A ≤ |(riemannXiDivisorZeroValue p).im| := by
  apply le_of_not_gt
  intro hheight
  apply hp
  apply kadiriCentralStrip_of_upper_below (A := A) _ hheight
  intro q hq
  by_cases hqT : |(riemannXiDivisorZeroValue q).im| < T
  · exact hlow q hqT
  have hTq := le_of_not_gt hqT
  have hqone := hT.trans_le hTq
  have hlog := Real.log_le_log (by linarith : 0 < |(riemannXiDivisorZeroValue q).im|) hq.le
  have hrecip := one_div_le_one_div_of_le (mul_pos hR (Real.log_pos hqone))
    (mul_le_mul_of_nonneg_left hlog hR.le)
  linarith [hhigh q hTq]

/-- The proved initial region removes the high-height hypothesis from the separation theorem. -/
theorem kadiri_outer_separation_initial {A σ : ℝ}
    (hσ : 1 - 1 / (56 * Real.log A) ≤ σ)
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < 10 ^ 9 → (riemannXiDivisorZeroValue p).re ≤ σ)
    (p : RiemannXiDivisorZeroIndex) (hp : ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p)) :
    A ≤ |(riemannXiDivisorZeroValue p).im| :=
  kadiri_outer_separation_of_region (by norm_num) (by norm_num) hσ hlow
    (fun q hq => xi_zero_gap_initial (riemannXiDivisorZeroValue_eq_zero q) hq) p hp

/-- The initial separation supplies exactly the `hfar` shape for any finite set of harmonics. -/
theorem kadiri_outer_separation_initial_harmonics {A σ t H : ℝ}
    (hσ : 1 - 1 / (56 * Real.log A) ≤ σ)
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < 10 ^ 9 → (riemannXiDivisorZeroValue p).re ≤ σ)
    {ι : Type*} (S : Finset ι) (k : ι → ℝ)
    (hk : ∀ i ∈ S, |k i * t| + H ≤ A) :
    ∀ i ∈ S, ∀ p : RiemannXiDivisorZeroIndex,
      ¬ kadiriCentralStrip σ (riemannXiDivisorZeroValue p) →
        |k i * t| + H ≤ |(riemannXiDivisorZeroValue p).im| := by
  intro i hi p hp
  exact (hk i hi).trans (kadiri_outer_separation_initial hσ hlow p hp)

end

end PrimeFactorUnimodality
