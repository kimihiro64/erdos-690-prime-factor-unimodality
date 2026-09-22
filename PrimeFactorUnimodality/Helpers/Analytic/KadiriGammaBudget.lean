import PrimeFactorUnimodality.Helpers.Analytic.SmoothedGammaFactorBounds

/-! # The leading logarithm and the remaining Gamma budget

For positive base height, isolate `log(t)` from each nonzero natural
harmonic. Its coefficient uses the sum excluding the zero harmonic, as
required in the zero-free improvement. The residual is an explicit sum
of logarithms; the zero harmonic and reciprocal error remain included.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The Gamma budget after extracting the leading logarithm of the base height. -/
def kadiriGammaResidual (κ σ t : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  (1 - κ) / 2 * (a 0 * (Real.log 2 - Real.log π) +
    ∑ i ∈ S.erase 0, a i * (Real.log ((i : ℝ) / 2 + 2 / t) - Real.log π)) +
    (∑ i ∈ S, a i) * ((1 + κ) / (σ + 2))

/-- The height factors out of the elementary logarithm at every natural harmonic. -/
theorem smoothedGammaFactorMajorant_nat_eq (κ σ : ℝ) {t : ℝ} (ht : 0 < t)
    (i : ℕ) :
    smoothedGammaFactorMajorant κ σ ((i : ℝ) * t) =
      (1 - κ) / 2 * Real.log t +
      (1 - κ) / 2 * (Real.log ((i : ℝ) / 2 + 2 / t) - Real.log π) +
      (1 + κ) / (σ + 2) := by
  have hp : 0 < (i : ℝ) / 2 + 2 / t := by positivity
  have he : (i : ℝ) * t / 2 + 2 = t * ((i : ℝ) / 2 + 2 / t) := by
    field_simp
  rw [smoothedGammaFactorMajorant, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg i) ht.le),
    he, Real.log_mul ht.ne' hp.ne']
  ring

/-- The logarithmic coefficient omits the zero harmonic without dropping its actual error. -/
theorem sum_smoothedGammaFactorMajorant_eq (κ σ : ℝ) {t : ℝ} (ht : 0 < t)
    (S : Finset ℕ) (h₀ : 0 ∈ S) (a : ℕ → ℝ) :
    (∑ i ∈ S, a i * smoothedGammaFactorMajorant κ σ ((i : ℝ) * t)) =
      (1 - κ) / 2 * (∑ i ∈ S.erase 0, a i) * Real.log t +
      kadiriGammaResidual κ σ t S a := by
  have hs : (∑ i ∈ S.erase 0, a i * smoothedGammaFactorMajorant κ σ ((i : ℝ) * t)) =
      (1 - κ) / 2 * (∑ i ∈ S.erase 0, a i) * Real.log t +
      (1 - κ) / 2 * (∑ i ∈ S.erase 0,
        a i * (Real.log ((i : ℝ) / 2 + 2 / t) - Real.log π)) +
      (∑ i ∈ S.erase 0, a i) * ((1 + κ) / (σ + 2)) := by
    simp_rw [smoothedGammaFactorMajorant_nat_eq κ σ ht, mul_add, Finset.sum_add_distrib]
    simp only [mul_left_comm (a _) ((1 - κ) / 2), ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [← Finset.add_sum_erase S _ h₀, hs]
  simp only [Nat.cast_zero, zero_mul, smoothedGammaFactorMajorant, abs_zero,
    zero_div, zero_add]
  unfold kadiriGammaResidual
  rw [← Finset.add_sum_erase S a h₀]
  ring

/-! The positive-height residual can be bounded at a single base height. -/

/-- Nonnegative coefficients make the residual decrease with the positive base height. -/
theorem antitoneOn_kadiriGammaResidual {κ : ℝ} (hκ : κ ≤ 1)
    (σ : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ i ∈ S, 0 ≤ a i) :
    AntitoneOn (fun t => kadiriGammaResidual κ σ t S a) (Set.Ioi 0) := by
  intro t ht u hu htu
  have htpos : 0 < t := ht
  have hupos : 0 < u := hu
  have hrecip : 2 / u ≤ 2 / t := div_le_div_of_nonneg_left (by norm_num) htpos htu
  have hs : (∑ i ∈ S.erase 0, a i * (Real.log ((i : ℝ) / 2 + 2 / u) - Real.log π)) ≤
      ∑ i ∈ S.erase 0, a i * (Real.log ((i : ℝ) / 2 + 2 / t) - Real.log π) := by
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (ha i (Finset.mem_of_mem_erase hi))
    exact sub_le_sub_right (Real.log_le_log (by positivity) (by linarith)) _
  unfold kadiriGammaResidual
  exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hs)
    (by linarith : 0 ≤ (1 - κ) / 2)) le_rfl

end

end PrimeFactorUnimodality
