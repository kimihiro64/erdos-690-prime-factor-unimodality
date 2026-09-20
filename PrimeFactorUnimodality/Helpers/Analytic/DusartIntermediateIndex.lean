import PrimeFactorUnimodality.Helpers.Analytic.DusartProof

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace PrimeFactorUnimodality

noncomputable section

/- The exponent index used in the intermediate part of Lemma 3.3 is bounded
   by the two elementary inequalities 2^23 ≤ 10^7 and 10^33 < 2^110. -/
theorem dusart_intermediate_log_index_bounds
    {x : Real} (hlo : (10 : Real) ^ 7 ≤ x)
    (hhi : x ≤ (10 : Real) ^ 33) :
    23 ≤ ⌊Real.log x / Real.log 2⌋₊ ∧
      ⌊Real.log x / Real.log 2⌋₊ ≤ 109 := by
  have hxpos : 0 < x := by
    have : (0 : Real) < 10 ^ 7 := by norm_num
    exact this.trans_le hlo
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 ≤ Real.log x := by
    apply Real.log_nonneg
    have : (1 : Real) ≤ (10 : Real) ^ 7 := by norm_num
    exact this.trans hlo
  have hlowpow : (2 : Real) ^ 23 ≤ x := by
    norm_num at hlo ⊢
    exact le_trans (by norm_num) hlo
  have hlowlog : Real.log ((2 : Real) ^ 23) ≤ Real.log x :=
    Real.log_le_log (by positivity) hlowpow
  have hlow : (23 : Real) ≤ Real.log x / Real.log 2 := by
    apply (le_div_iff₀ hlog2).2
    rw [Real.log_pow] at hlowlog
    norm_num at hlowlog ⊢
    exact hlowlog
  have hupperpow : (10 : Real) ^ 33 < (2 : Real) ^ 110 := by
    norm_num
  have huplog : Real.log x < Real.log ((2 : Real) ^ 110) := by
    exact (Real.log_le_log hxpos.le hhi).trans_lt
      (Real.log_lt_log (by positivity) hupperpow)
  have huper : Real.log x / Real.log 2 < (110 : Real) := by
    apply (div_lt_iff₀ hlog2).2
    rw [Real.log_pow] at huplog
    norm_num at huplog ⊢
    exact huplog
  constructor
  · exact Nat.le_floor hlow
  · have hf : ⌊Real.log x / Real.log 2⌋₊ < 110 :=
      (Nat.floor_lt hlogx).2 huper
    omega

theorem dusart_floor_two_pow_le
    {x : Real} (hx : 1 ≤ x) :
    ((2 : Real) ^ (⌊Real.log x / Real.log 2⌋₊ : Nat)) ≤ x := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hfloor :
      (⌊Real.log x / Real.log 2⌋₊ : Real) ≤ Real.log x / Real.log 2 := by
    exact_mod_cast Nat.floor_le (div_nonneg hlogx hlog2.le)
  have hlog_le :
      Real.log ((2 : Real) ^ (⌊Real.log x / Real.log 2⌋₊ : Nat)) ≤
        (Real.log x / Real.log 2) * Real.log 2 := by
    rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_right hfloor hlog2.le
  have hpow :
      ((2 : Real) ^ (⌊Real.log x / Real.log 2⌋₊ : Nat)) ≤
        (2 : Real) ^ (Real.log x / Real.log 2) := by
    apply (Real.le_rpow_iff_log_le (by positivity) (by positivity)).2
    exact hlog_le
  have heq : (2 : Real) ^ (Real.log x / Real.log 2) = x := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    rw [show Real.log 2 * (Real.log x / Real.log 2) = Real.log x by
      field_simp]
    exact Real.exp_log hxpos
  simpa [heq] using hpow

end

end PrimeFactorUnimodularity
