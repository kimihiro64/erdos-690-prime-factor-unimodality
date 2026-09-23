import PrimeFactorUnimodality.Helpers.Analytic.DusartPsiSmoothing

/-! # Combining independently normalized adjacent psi averages

The two averages may use different estimates and cutoff choices. The
lower average is normalized by its own base point; converting it back
introduces exactly the factor `1-m*s`. This argument includes order zero.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Chebyshev

/-- Independent relative bounds for adjacent averages control the actual pointwise error. -/
theorem dusart_abs_psi_div_le_of_relative_averages (m : ℕ) {s x L U : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hl : 0 < x * (1 - m * s))
    (hleft : |dusartPsiAverageError m (s * x) (x * (1 - m * s))| /
      (x * (1 - m * s)) ≤ L)
    (hright : |dusartPsiAverageError m (s * x) x| / x ≤ U) :
    |ψ x - x| / x ≤ max ((1 - m * s) * L) U + m * s / 2 := by
  have hy : x - m * (s * x) = x * (1 - m * s) := by ring
  have hleft' : |dusartPsiAverageError m (s * x) (x - m * (s * x))| ≤
      x * max ((1 - m * s) * L) U := by
    rw [hy]
    calc
      _ ≤ L * (x * (1 - m * s)) := (div_le_iff₀ hl).mp hleft
      _ = x * ((1 - m * s) * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hx.le
  have hright' : |dusartPsiAverageError m (s * x) x| ≤
      x * max ((1 - m * s) * L) U := by
    calc
      _ ≤ U * x := (div_le_iff₀ hx).mp hright
      _ = x * U := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hx.le
  have he := dusart_abs_psi_error_le_of_averages m (mul_pos hs hx) hleft' hright'
  apply (div_le_iff₀ hx).mpr
  convert he using 1
  ring

end

end PrimeFactorUnimodality
