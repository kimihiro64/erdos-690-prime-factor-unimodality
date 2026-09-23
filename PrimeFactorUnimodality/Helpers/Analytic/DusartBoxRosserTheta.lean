import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxRosserMixed
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds

/-! # Direct transfer to the theta statements used by Wang--Crapis

Dusart's Proposition 5.1 and the logarithmic lower bound need their stated
relative margins, not a prescribed fourth-power error with coefficient
`0.648`. This module connects the selected actual psi estimates directly
to those margins. The finite theta prefix remains a separate input; no
small-point absolute psi bound is silently imposed on that prefix.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev Real

/-- The already proved elementary prime-power correction, relative to the base point. -/
def dusartThetaRootRelativeCorrection (x : ℝ) : ℝ :=
  (Real.log 4 + 4) * (exp (-Real.log x / 2) +
    exp (-2 * Real.log x / 3) + exp (-4 * Real.log x / 5))

/-- The normalized psi error and the existing root correction control the absolute theta error. -/
theorem abs_theta_sub_div_le_psi_relative_error {x ε : ℝ} (hx : 0 < x)
    (hpsi : |ψ x - x| / x ≤ ε) :
    |θ x - x| / x ≤ ε + dusartThetaRootRelativeCorrection x := by
  have hp : |ψ x - x| ≤ ε * x := (div_le_iff₀ hx).mp hpsi
  have hu := theta_upper_of_psi_relative_error hp
  have hl := theta_lower_of_psi_relative_error_elementary
    (b := Real.log x) (by rw [Real.exp_log hx]) hp
  have hc : 0 ≤ dusartThetaRootRelativeCorrection x := by
    unfold dusartThetaRootRelativeCorrection
    positivity
  have hl' : (1 - ε - dusartThetaRootRelativeCorrection x) * x ≤ θ x := hl
  have ha : |θ x - x| ≤ (ε + dusartThetaRootRelativeCorrection x) * x := by
    apply abs_le.mpr
    constructor
    · linarith only [hl']
    · have hcx := mul_nonneg hc hx.le
      nlinarith only [hu, hcx]
  exact (div_le_iff₀ hx).mpr ha

/-- A normalized actual psi estimate transfers directly to the two requested theta margins. -/
theorem dusartTheta_margins_of_normalized_psi {x ε : ℝ} (hx : 0 < x)
    (hpsi : |ψ x - x| / x ≤ ε)
    (hupper : ε < 1 / 36260)
    (hlower : ε + dusartThetaRootRelativeCorrection x < (12323 / 10000 : ℝ) / Real.log x) :
    θ x - x < x / 36260 ∧
      |θ x - x| < (12323 / 10000 : ℝ) * x / Real.log x := by
  have hu := theta_upper_of_psi_relative_error ((div_le_iff₀ hx).mp hpsi)
  have ha := (div_le_iff₀ hx).mp (abs_theta_sub_div_le_psi_relative_error hx hpsi)
  constructor
  · have hm := mul_lt_mul_of_pos_right hupper hx
    linarith only [hu, hm]
  · exact ha.trans_lt ((mul_lt_mul_of_pos_right hlower hx).trans_eq (by ring))

/-- Any verified selected relative envelope supplies the exact global theta provider. -/
theorem hasDusartThetaBounds_of_rosserMixed {X R a H δ : ℝ} {ε : ℝ → ℝ}
    (hX : 3 ≤ X) (hR : 0 < R) (ha : 10 ≤ a) (haH : a < H) (hH : 10 ^ 9 ≤ H) (hδ : 0 < δ)
    (finite : HasDusartSymmetricThetaBoundsBelow X)
    (hgap : ∀ z ∈ xiLowHeightIndices H, (riemannXiDivisorZeroValue z).re ≤ 1 - δ)
    (hreg : ∀ z : RiemannXiDivisorZeroIndex, H ≤ |(riemannXiDivisorZeroValue z).im| →
      (riemannXiDivisorZeroValue z).re ≤
        1 - 1 / (R * Real.log |(riemannXiDivisorZeroValue z).im|))
    (hscalar : ∀ x : ℝ, X ≤ x → ∃ (m : ℕ) (s ν : ℝ),
      0 < s ∧ 1 < x * (1 - (m + 3 : ℕ) * s) ∧
      0 < ν ∧ ν ≤ 1 ∧ 1 < (m + 3 : ℕ) * ν ^ 2 ∧
      max ((1 - (m + 3 : ℕ) * s) *
        dusartBoxRosserMixedBudget m (s / (1 - (m + 3 : ℕ) * s))
          (x * (1 - (m + 3 : ℕ) * s)) R ν a H δ)
        (dusartBoxRosserMixedBudget m s x R ν a H δ) + (m + 3 : ℕ) * s / 2 ≤ ε x)
    (hupper : ∀ x : ℝ, X ≤ x → ε x < 1 / 36260)
    (hlower : ∀ x : ℝ, X ≤ x →
      ε x + dusartThetaRootRelativeCorrection x < (12323 / 10000 : ℝ) / Real.log x) :
    HasDusartThetaBounds := by
  have htail (x : ℝ) (hx : X ≤ x) : θ x - x < x / 36260 ∧
      |θ x - x| < (12323 / 10000 : ℝ) * x / Real.log x := by
    obtain ⟨m, s, ν, hs, hl, hν, hν1, hm, hb⟩ := hscalar x hx
    have hx0 : 0 < x := by linarith
    exact dusartTheta_margins_of_normalized_psi hx0
      ((abs_psi_sub_div_le_dusartBoxRosserMixed m hs hx0 hl hR hν hν1 hm
        ha haH hH hδ hgap hreg).trans hb) (hupper x hx) (hlower x hx)
  exact hasDusartThetaBounds_of_below_and_above finite
    ⟨fun x hx => (htail x hx).1, fun x _ hx => (htail x hx).2⟩

end

end PrimeFactorUnimodality
