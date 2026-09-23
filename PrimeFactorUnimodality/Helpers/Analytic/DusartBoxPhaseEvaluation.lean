import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPhaseBudget
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.ExponentialStability
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Complex.GroupedRounding

/-! # Shared evaluation and interval coverage for the actual low-zero phase sum

Reuse the frequency-generic grouped evaluator with zero ordinates in place
of logarithmic Dirichlet frequencies. Rounded moments, phases, coefficients,
and ordinates retain their separate error bounds. Sample interpolation feeds
the actual psi budget, not a replacement abstract zero sum.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Finset

/-- Rescaling a logarithmic window changes frequencies, not its stored coefficients. -/
theorem dusartBoxLowPhaseSum_scaled (m : ℕ) (s u T R v : ℝ) :
    dusartBoxLowPhaseSum m s u T (R * v) =
      ∑ z ∈ xiLowHeightIndices T, dusartBoxZeroCoefficient m s u z *
        exp (I * ((v * (R * (riemannXiDivisorZeroValue z).im) : ℝ) : ℂ)) := by
  unfold dusartBoxLowPhaseSum
  apply sum_congr rfl
  intro z hz
  rw [show R * v * (riemannXiDivisorZeroValue z).im =
    v * (R * (riemannXiDivisorZeroValue z).im) by ring]

/-- Explicit frequency bins reuse the existing rounded-moment evaluator. -/
theorem norm_dusartBoxLowPhaseSum_sub_grouped_le {κ : Type*} [DecidableEq κ]
    (m : ℕ) (s u T R : ℝ) (B : Finset κ)
    (bin : RiemannXiDivisorZeroIndex → κ) (c : κ → ℝ)
    (hbin : ∀ z ∈ xiLowHeightIndices T, bin z ∈ B)
    {A v : ℝ} (hA : 0 ≤ A)
    (hres : ∀ z ∈ xiLowHeightIndices T,
      |v * (R * (riemannXiDivisorZeroValue z).im - c (bin z))| ≤ A)
    (k : ℕ) (a : κ → ℕ → ℂ) (p : κ → ℂ) (ε : κ → ℕ → ℝ) (δ : κ → ℝ)
    (ha : ∀ b ∈ B, ∀ j ∈ range k,
      ‖expSumMoment ((xiLowHeightIndices T).filter (fun z => bin z = b))
        (dusartBoxZeroCoefficient m s u) (fun z => R * (riemannXiDivisorZeroValue z).im - c b)
        j - a b j‖ ≤ ε b j)
    (hp : ∀ b ∈ B, ‖exp (I * ((v * c b : ℝ) : ℂ)) - p b‖ ≤ δ b) :
    ‖dusartBoxLowPhaseSum m s u T (R * v) -
      ∑ b ∈ B, p b * ∑ j ∈ range k, a b j * (v : ℂ) ^ j‖ ≤
      (∑ z ∈ xiLowHeightIndices T, ‖dusartBoxZeroCoefficient m s u z‖) *
        (A ^ k * Real.exp A) +
      ∑ b ∈ B, ((∑ j ∈ range k, ε b j * |v| ^ j) +
        ‖∑ j ∈ range k, a b j * (v : ℂ) ^ j‖ * δ b) := by
  rw [dusartBoxLowPhaseSum_scaled]
  exact norm_expSum_sub_roundedGrouped_le _ _ _ _ _ _ hbin hA hres k a p ε δ ha hp

/-- Independently enclosed coefficients and ordinates approximate the actual sum uniformly. -/
theorem norm_dusartBoxLowPhaseSum_sub_enclosures_le (m : ℕ) (s u T : ℝ)
    (a : RiemannXiDivisorZeroIndex → ℂ) (g ε δ : RiemannXiDivisorZeroIndex → ℝ)
    {v V : ℝ} (hv : |v| ≤ V)
    (ha : ∀ z ∈ xiLowHeightIndices T, ‖dusartBoxZeroCoefficient m s u z - a z‖ ≤ ε z)
    (hg : ∀ z ∈ xiLowHeightIndices T, |(riemannXiDivisorZeroValue z).im - g z| ≤ δ z) :
    ‖dusartBoxLowPhaseSum m s u T v -
      ∑ z ∈ xiLowHeightIndices T, a z * exp (I * ((v * g z : ℝ) : ℂ))‖ ≤
      ∑ z ∈ xiLowHeightIndices T, (ε z + ‖a z‖ * (V * δ z)) :=
  norm_expSum_sub_expSum_le_of_enclosures _ _ _ _ _ _ _ hv ha hg

/-- The finite frequency mass controls interpolation without any zero-spacing premise. -/
def dusartBoxPhaseFrequencyMass (m : ℕ) (s u T : ℝ) : ℝ :=
  ∑ z ∈ xiLowHeightIndices T,
    ‖dusartBoxZeroCoefficient m s u z‖ * |(riemannXiDivisorZeroValue z).im|

/-- A single checked sample controls every point within its certified distance. -/
theorem norm_dusartBoxLowPhaseSum_le_of_sample (m : ℕ) (s u T : ℝ)
    {v w d e : ℝ} {z : ℂ} (hd : |v - w| ≤ d)
    (hz : ‖dusartBoxLowPhaseSum m s u T w - z‖ ≤ e) :
    ‖dusartBoxLowPhaseSum m s u T v‖ ≤
      ‖z‖ + e + d * dusartBoxPhaseFrequencyMass m s u T :=
  norm_expSum_le_of_sample _ _ _ hd hz

/-- Certified sample interpolation supplies the full actual psi-average estimate. -/
theorem abs_dusartPsiAverageError_div_le_phase_sample (m : ℕ) {s x T : ℝ} (u : ℝ)
    (hs : 0 < s) (hx : 1 < x) (hT : 10 < T)
    (hline : ∀ p ∈ xiLowHeightIndices T, (riemannXiDivisorZeroValue p).re = 1 / 2)
    {v d e : ℝ} {z : ℂ} (hd : |(Real.log x - u) - v| ≤ d)
    (hz : ‖dusartBoxLowPhaseSum m s u T v - z‖ ≤ e) :
    |dusartPsiAverageError (m + 3) (s * x) x| / x ≤
      dusartBoxPhaseBudget m s x T (‖z‖ + e + d * dusartBoxPhaseFrequencyMass m s u T) :=
  abs_dusartPsiAverageError_div_le_phase m u hs hx hT hline
    (norm_dusartBoxLowPhaseSum_le_of_sample m s u T hd hz)

end

end PrimeFactorUnimodality
