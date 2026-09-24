import PrimeFactorUnimodality.Helpers.Analytic.PlattZetaReality

set_option autoImplicit false

/-! # Reuse the shared zeta grid for narrow interpolation windows

The base window depends on its center and width only through a positive
Gaussian factor once the actual ordinate is fixed. Thus recentering and
narrowing need no new zeta or Gamma evaluations. Uncertainty in the scaling
factor and the final multiplication is explicitly propagated.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Positive scale from the original window to a new center and width. -/
def plattRewindowScale (t₀ t₁ h H v : ℝ) : ℝ :=
  Real.exp ((v + t₁ - t₀) ^ 2 / (2 * h ^ 2) - v ^ 2 / (2 * H ^ 2))

theorem plattRewindowScale_pos (t₀ t₁ h H v : ℝ) :
    0 < plattRewindowScale t₀ t₁ h H v := Real.exp_pos _

/-- The same genuine zeta value supplies any centered base window at the same ordinate. -/
theorem plattZetaWindow_rewindow (t₀ t₁ h H v : ℝ) :
    plattZetaWindow 0 t₁ H v = (plattRewindowScale t₀ t₁ h H v : ℂ) *
      plattZetaWindow 0 t₀ h (v + t₁ - t₀) := by
  have hv : v + t₁ - t₀ + t₀ = v + t₁ := by ring
  have he : plattRewindowScale t₀ t₁ h H v *
      (Real.pi ^ (1 / 4 : ℝ) *
        Real.exp (Real.pi * (v + t₁) / 4 - (v + t₁ - t₀) ^ 2 / (2 * h ^ 2))) =
      Real.pi ^ (1 / 4 : ℝ) * Real.exp (Real.pi * (v + t₁) / 4 - v ^ 2 / (2 * H ^ 2)) := by
    unfold plattRewindowScale
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  simp only [plattZetaWindow_eq_completed, pow_zero, mul_one, hv]
  rw [← mul_assoc, ← Complex.ofReal_mul, he]

/-- A new center at a shared grid point reuses the old sample at the sum of the two indices. -/
theorem plattZetaWindow_rewindow_grid (t₀ h H A : ℝ) (j n : ℤ) :
    plattZetaWindow 0 (t₀ + (j : ℝ) / A) H ((n : ℝ) / A) =
      (plattRewindowScale t₀ (t₀ + (j : ℝ) / A) h H ((n : ℝ) / A) : ℂ) *
        plattZetaWindow 0 t₀ h (((n + j : ℤ) : ℝ) / A) := by
  rw [plattZetaWindow_rewindow t₀]
  congr 2
  push_cast
  ring

/-- Enclosed samples and enclosed real scaling factors bound the new genuine window. -/
theorem norm_plattZetaWindow_rewindow_sub_le (t₀ t₁ h H v : ℝ)
    {q : ℂ} {ε s σ : ℝ}
    (hq : ‖plattZetaWindow 0 t₀ h (v + t₁ - t₀) - q‖ ≤ ε)
    (hs : |plattRewindowScale t₀ t₁ h H v - s| ≤ σ) :
    ‖plattZetaWindow 0 t₁ H v - (s : ℂ) * q‖ ≤
      plattRewindowScale t₀ t₁ h H v * ε + σ * ‖q‖ := by
  rw [plattZetaWindow_rewindow t₀ t₁ h H v]
  have h₁ : ‖(plattRewindowScale t₀ t₁ h H v : ℂ) *
      plattZetaWindow 0 t₀ h (v + t₁ - t₀) -
      (plattRewindowScale t₀ t₁ h H v : ℂ) * q‖ ≤
      plattRewindowScale t₀ t₁ h H v * ε := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (plattRewindowScale_pos t₀ t₁ h H v)]
    exact mul_le_mul_of_nonneg_left hq (plattRewindowScale_pos t₀ t₁ h H v).le
  have h₂ : ‖(plattRewindowScale t₀ t₁ h H v : ℂ) * q - (s : ℂ) * q‖ ≤ σ * ‖q‖ := by
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hs (norm_nonneg q)
  exact (norm_sub_le_norm_sub_add_norm_sub _
    ((plattRewindowScale t₀ t₁ h H v : ℂ) * q) _).trans (add_le_add h₁ h₂)

/-- Final rounded multiplication contributes its own error, independently of the scale enclosure. -/
theorem norm_plattZetaWindow_rewindow_sub_rounded_le (t₀ t₁ h H v : ℝ)
    {q z : ℂ} {ε s σ δ : ℝ}
    (hq : ‖plattZetaWindow 0 t₀ h (v + t₁ - t₀) - q‖ ≤ ε)
    (hs : |plattRewindowScale t₀ t₁ h H v - s| ≤ σ)
    (hz : ‖(s : ℂ) * q - z‖ ≤ δ) :
    ‖plattZetaWindow 0 t₁ H v - z‖ ≤
      plattRewindowScale t₀ t₁ h H v * ε + σ * ‖q‖ + δ :=
  (norm_sub_le_norm_sub_add_norm_sub _ ((s : ℂ) * q) _).trans
    (add_le_add (norm_plattZetaWindow_rewindow_sub_le t₀ t₁ h H v hq hs) hz)

end

end PrimeFactorUnimodality
