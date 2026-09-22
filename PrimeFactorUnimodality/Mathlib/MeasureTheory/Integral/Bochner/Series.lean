/-
Copyright (c) 2026 Jonas Whidden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas Whidden
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Integrability of a series with summable integrated norms

The same absolute bound that justifies interchanging a series and an
integral also proves that its pointwise sum is integrable. Generalized
from `Robin1984.integrable_complex_series_of_integral_norm`, Apache-2.0
revision `bfa72aec0c25c8ee29cefe4449d778ff30412bee`,
`Robin1984.NicolasLandau.WeightedGammaPairing`. Only Mathlib is imported.
-/

namespace MeasureTheory

/-- A summable family of integrated norms gives an integrable pointwise sum. -/
theorem integrable_tsum_of_summable_integral_norm
    {α ι E : Type*} [MeasurableSpace α] [Countable ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {F : ι → α → E}
    (hF : ∀ i, Integrable (F i) μ) (hSum : Summable (fun i => ∫ t, ‖F i t‖ ∂μ)) :
    Integrable (fun t => ∑' i, F i t) μ := by
  have hm : AEMeasurable (fun t => ∑' i, F i t) μ :=
    AEMeasurable.tsum (fun i => (hF i).aestronglyMeasurable.aemeasurable)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ t, ‖∑' i, F i t‖ₑ ∂μ) ≤ ∫⁻ t, ∑' i, ‖F i t‖ₑ ∂μ :=
      lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' i, ∫⁻ t, ‖F i t‖ₑ ∂μ :=
      lintegral_tsum (fun i => (hF i).aestronglyMeasurable.enorm)
    _ = ∑' i, ENNReal.ofReal (∫ t, ‖F i t‖ ∂μ) :=
      tsum_congr fun i => (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
    _ < ⊤ := hSum.tsum_ofReal_lt_top

end MeasureTheory
