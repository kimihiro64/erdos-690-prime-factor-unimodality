import PrimeFactorUnimodality.Helpers.Analytic.DusartBoxPowerTransform

/-! # Zero-free damping of the actual averaged spectral atom

Apply the generic BV complex-power bound on the entire averaging support.
The gap damps each atom exponentially, while the upper arithmetic endpoint
controls its linear factor. No RH or numerical zero-free constant is assumed.
-/

namespace PrimeFactorUnimodality

noncomputable section

open Complex Set intervalIntegral

theorem norm_dusartBox_paired_atom_le (m : ℕ) {h x δ : ℝ}
    (hh : 0 < h) (hx : 1 < x) (hδ : 0 ≤ δ) {s : ℂ} (hs : s ≠ 0)
    (hgap : s.re ≤ 1 - δ) :
    ‖finiteLaplace (fun u => (dusartBoxWeight m h x u : ℂ)) (dusartBoxSupport m h x) (-s) +
        1 / s‖ ≤
      ((x + (m + 3 : ℕ) * h) * Real.exp (-δ * Real.log x)) * ‖(1 : ℂ) / s‖ := by
  rw [finiteLaplace_dusartBoxWeight_add_inv m hh hx hs]
  apply norm_iteratedBoxAverageComplex_le_on_Ici hh
    ((continuousOn_ofReal_cpow_Ici zero_lt_one s).div_const s) hx.le
  intro t ht
  have ht1 : 1 ≤ t := hx.le.trans ht.1
  have hlog := Real.log_le_log (lt_trans zero_lt_one hx) ht.1
  have hexp : Real.exp (-δ * Real.log t) ≤ Real.exp (-δ * Real.log x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hδ))
  exact (Complex.norm_real_cpow_div_le_exp_gap_mul_reciprocal ht1 hgap).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul ht.2 hexp (Real.exp_pos _).le
        (by linarith [mul_nonneg (Nat.cast_nonneg (m + 3)) hh.le])) (norm_nonneg _))

end

end PrimeFactorUnimodality
