import PrimeFactorUnimodality.Helpers.Analytic.KadiriEndpointRows
import PrimeFactorUnimodality.Helpers.Analytic.ZetaZeroFreeBounded

/-! # Initial regions at a lower bootstrap cutoff

The proved constant-56 region above one billion and its bounded-strip
extension supply an initial region at any smaller positive logarithmic
cutoff, with an explicitly adjusted constant. This discharges the starting
region of a chain without assuming additional low-height zero locations.
Improving rows still require their actual numerical margins and low input.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- Rescale the proved bounded-strip gap to any starting height with a sufficient logarithm. -/
theorem kadiriHighRegion_of_initial_cutoff {R T : ℝ}
    (hT : 1 < T) (hR : 56 ≤ R)
    (hscale : 56 * log (10 ^ 9 : ℝ) ≤ R * log T) : KadiriHighRegion R T := by
  intro p hp
  have ht : 1 < |(riemannXiDivisorZeroValue p).im| := hT.trans_le hp
  have hlog : 0 < log |(riemannXiDivisorZeroValue p).im| := log_pos ht
  by_cases hhigh : 10 ^ 9 ≤ |(riemannXiDivisorZeroValue p).im|
  · exact (one_div_le_one_div_of_le (by positivity : 0 < 56 *
        log |(riemannXiDivisorZeroValue p).im|)
      (mul_le_mul_of_nonneg_right hR hlog.le)).trans
      (xi_zero_gap_initial (riemannXiDivisorZeroValue_eq_zero p) hhigh)
  · have hden : 56 * log (10 ^ 9 : ℝ) ≤ R * log |(riemannXiDivisorZeroValue p).im| :=
      hscale.trans (mul_le_mul_of_nonneg_left
        (log_le_log (by linarith : 0 < T) hp) (by linarith : 0 ≤ R))
    exact (one_div_le_one_div_of_le (by positivity : 0 < 56 * log (10 ^ 9 : ℝ)) hden).trans
      (xi_zero_gap_bounded le_rfl (riemannXiDivisorZeroValue_eq_zero p) (le_of_not_ge hhigh))

/-- Every decimal cutoff up to a billion has an explicit unconditional initial constant. -/
theorem kadiriHighRegion_decimal_cutoff {n : ℕ} (hn : 1 ≤ n) (hn9 : n ≤ 9) :
    KadiriHighRegion (504 / (n : ℝ)) (10 ^ n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  apply kadiriHighRegion_of_initial_cutoff
  · exact one_lt_pow₀ (by norm_num : (1 : ℝ) < 10) (by omega)
  · apply (le_div_iff₀ hnpos).mpr
    have hn' : (n : ℝ) ≤ 9 := by exact_mod_cast hn9
    linarith
  · rw [log_pow, log_pow]
    norm_num
    field_simp
    norm_num

/-- A lower-cutoff endpoint chain now needs no separately supplied starting region. -/
theorem KadiriEndpointChain.highRegion_of_initial_cutoff
    {n : ℕ} {a : ℕ → ℝ} {T R r : ℝ}
    (h : KadiriEndpointChain n a T R r) (hT : 1 < T) (hR : 56 ≤ R)
    (hscale : 56 * log (10 ^ 9 : ℝ) ≤ R * log T)
    (ha : ∀ i ∈ Finset.range (n + 1), 0 ≤ a i) (ha₀ : 0 < a 0) (ha₁ : 0 < a 1)
    (hpoly : ∀ u : ℝ, 0 ≤ ∑ i ∈ Finset.range (n + 1), a i * cos ((i : ℝ) * u))
    (hlow : ∀ p : RiemannXiDivisorZeroIndex,
      |(riemannXiDivisorZeroValue p).im| < T → (riemannXiDivisorZeroValue p).re ≤ 1 / 2) :
    KadiriHighRegion r T :=
  h.highRegion ha ha₀ ha₁ hpoly hlow (kadiriHighRegion_of_initial_cutoff hT hR hscale)

end

end PrimeFactorUnimodality
