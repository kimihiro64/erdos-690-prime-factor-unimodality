import PrimeFactorUnimodality.Helpers.Analytic.PlattRewindow

/-! Recentered narrow windows reuse genuine shared-grid values without new special functions. -/

open PrimeFactorUnimodality

example (t₀ h v : ℝ) : plattRewindowScale t₀ t₀ h h v = 1 := by
  simp [plattRewindowScale]

example (t₀ h H A : ℝ) (j n : ℤ) :
    plattZetaWindow 0 (t₀ + (j : ℝ) / A) H ((n : ℝ) / A) =
      (plattRewindowScale t₀ (t₀ + (j : ℝ) / A) h H ((n : ℝ) / A) : ℂ) *
        plattZetaWindow 0 t₀ h (((n + j : ℤ) : ℝ) / A) :=
  plattZetaWindow_rewindow_grid t₀ h H A j n

example (t₀ t₁ h H v : ℝ) {q z : ℂ} {ε s σ δ : ℝ}
    (hq : ‖plattZetaWindow 0 t₀ h (v + t₁ - t₀) - q‖ ≤ ε)
    (hs : |plattRewindowScale t₀ t₁ h H v - s| ≤ σ)
    (hz : ‖(s : ℂ) * q - z‖ ≤ δ) :
    ‖plattZetaWindow 0 t₁ H v - z‖ ≤
      plattRewindowScale t₀ t₁ h H v * ε + σ * ‖q‖ + δ :=
  norm_plattZetaWindow_rewindow_sub_rounded_le t₀ t₁ h H v hq hs hz
