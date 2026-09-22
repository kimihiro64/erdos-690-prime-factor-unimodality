import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Log.AffineRatio

/-! # Uniform parameter domains for a zero-free-region iteration

Choose the real coordinate from the largest harmonic height. An existing
region bounds the normalized transform argument from above; failure of
the target region bounds it from below. The logarithmic-ratio theorem
makes the lower bound uniform over the whole height ray. No numerical
region, low-zero location, or correction-budget sign is assumed proved.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Real

/-- The real coordinate chosen using the previous region at the largest harmonic cutoff. -/
def kadiriBootstrapSigma (R : ℝ) (n : ℕ) (H t : ℝ) : ℝ :=
  1 - 1 / (R * log ((n : ℝ) * t + H))

/-- The endpoint lower bound for the normalized transform argument. -/
def kadiriBootstrapLowerArgument (R r : ℝ) (n : ℕ) (H T : ℝ) : ℝ :=
  (r / R) * (log T / log ((n : ℝ) * T + H))

/-- The largest harmonic cutoff is at least the original nonnegative height. -/
theorem le_kadiri_harmonic_cutoff {n : ℕ} (hn : 1 ≤ n) {H t : ℝ}
    (hH : 0 ≤ H) (ht : 0 ≤ t) : t ≤ (n : ℝ) * t + H := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith only [hn', hH, ht]

/-- Every natural harmonic up to the degree lies inside the selected cutoff. -/
theorem kadiri_harmonics_le_cutoff {n i : ℕ} (hi : i ∈ Finset.range (n + 1))
    {t H : ℝ} (ht : 0 ≤ t) : |(i : ℝ) * t| + H ≤ (n : ℝ) * t + H := by
  have hi' : (i : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ht)]
  exact add_le_add (mul_le_mul_of_nonneg_right hi' ht) le_rfl

/-- The chosen real coordinate increases with height. -/
theorem kadiriBootstrapSigma_le {R H T t : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 1 ≤ n) (hH : 0 ≤ H) (hT : 1 < T) (hTt : T ≤ t) :
    kadiriBootstrapSigma R n H T ≤ kadiriBootstrapSigma R n H t := by
  have hTpos : 0 < T := by linarith
  have hbase := le_kadiri_harmonic_cutoff hn hH hTpos.le
  have hcut : (n : ℝ) * T + H ≤ (n : ℝ) * t + H :=
    add_le_add (mul_le_mul_of_nonneg_left hTt (Nat.cast_nonneg n)) le_rfl
  have hlog := log_le_log (hTpos.trans_le hbase) hcut
  exact sub_le_sub_left (one_div_le_one_div_of_le
    (mul_pos hR (log_pos (hT.trans_le hbase))) (mul_le_mul_of_nonneg_left hlog hR.le)) 1

/-- The chosen real coordinate stays strictly to the left of one. -/
theorem kadiriBootstrapSigma_lt_one {R H t : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 1 ≤ n) (hH : 0 ≤ H) (ht : 1 < t) :
    kadiriBootstrapSigma R n H t < 1 := by
  have hbase := le_kadiri_harmonic_cutoff hn hH (show 0 ≤ t by linarith)
  have h := one_div_pos.mpr (mul_pos hR (log_pos (ht.trans_le hbase)))
  exact sub_lt_self _ h

/-- The previous gap keeps the distinguished zero to the left of the chosen coordinate. -/
theorem le_kadiriBootstrapSigma_of_gap {R H t β : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 1 ≤ n) (hH : 0 ≤ H) (ht : 1 < t)
    (hgap : 1 / (R * log t) ≤ 1 - β) : β ≤ kadiriBootstrapSigma R n H t := by
  have hbase := le_kadiri_harmonic_cutoff hn hH (show 0 ≤ t by linarith)
  have h := one_div_le_one_div_of_le (mul_pos hR (log_pos ht))
    (mul_le_mul_of_nonneg_left (log_le_log (by linarith) hbase) hR.le)
  unfold kadiriBootstrapSigma
  linarith only [hgap, h]

/-- Failure of the target gap bounds the scale by its fixed starting-height value. -/
theorem kadiriBootstrapScale_le_endpoint {r T t η : ℝ}
    (hr : 0 < r) (hT : 1 < T) (hTt : T ≤ t) (hsmall : η ≤ 1 / (r * log t)) :
    η ≤ 1 / (r * log T) :=
  hsmall.trans (one_div_le_one_div_of_le (mul_pos hr (log_pos hT))
    (mul_le_mul_of_nonneg_left (log_le_log (by linarith) hTt) hr.le))

/-- A small actual scale forces a large height through the previous region, not the target one. -/
theorem kadiriBootstrapHeightLower_of_small_scale {R t η η₁ : ℝ}
    (hR : 0 < R) (ht : 1 < t) (hη₁ : 0 < η₁)
    (hprior : 1 / (R * log t) ≤ η) (hsmall : η ≤ η₁) :
    exp (1 / (R * η₁)) ≤ t := by
  have hprod := (div_le_iff₀ (mul_pos hR (log_pos ht))).mp (hprior.trans hsmall)
  have hlog : 1 / (R * η₁) ≤ log t := by
    apply (div_le_iff₀ (mul_pos hR hη₁)).mpr
    nlinarith only [hprod]
  simpa only [exp_log (by linarith : 0 < t)] using exp_le_exp.mpr hlog

/-- Prior and target gaps place the moving transform argument in one fixed interval. -/
theorem kadiriBootstrapArgument_mem_Icc {R r H T t η : ℝ} {n : ℕ}
    (hR : 0 < R) (hr : 0 < r) (hn : 1 ≤ n) (hH : 0 ≤ H) (hT : 1 < T)
    (hTt : T ≤ t) (hη : 0 < η) (hprior : 1 / (R * log t) ≤ η)
    (hsmall : η ≤ 1 / (r * log t)) :
    (1 - kadiriBootstrapSigma R n H t) / η ∈
      Set.Icc (kadiriBootstrapLowerArgument R r n H T) 1 := by
  have ht : 1 < t := hT.trans_le hTt
  have hlogt : 0 < log t := log_pos ht
  have hbase := le_kadiri_harmonic_cutoff hn hH (show 0 ≤ t by linarith)
  have hlogA : 0 < log ((n : ℝ) * t + H) := log_pos (ht.trans_le hbase)
  have hnum : 0 ≤ 1 / (R * log ((n : ℝ) * t + H)) :=
    (one_div_pos.mpr (mul_pos hR hlogA)).le
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hupper := div_le_div_of_nonneg_left hnum (one_div_pos.mpr (mul_pos hR hlogt)) hprior
  have hlower := div_le_div_of_nonneg_left hnum hη hsmall
  have hid (v : ℝ) :
      (1 / (R * log ((n : ℝ) * t + H))) / (1 / (v * log t)) =
        (v / R) * (log t / log ((n : ℝ) * t + H)) := by
    simp only [div_eq_mul_inv, inv_inv, mul_inv_rev]
    ring
  rw [hid R, div_self hR.ne', one_mul] at hupper
  rw [hid r] at hlower
  simp only [kadiriBootstrapSigma, sub_sub_cancel]
  constructor
  · exact (mul_le_mul_of_nonneg_left (log_div_log_affine_le hn' hH hT hTt)
      (div_nonneg hr.le hR.le)).trans hlower
  · exact hupper.trans (log_div_log_affine_le_one hn' hH ht)

end

end PrimeFactorUnimodality
