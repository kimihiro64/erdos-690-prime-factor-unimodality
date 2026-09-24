import PrimeFactorUnimodality.Helpers.Analytic.XiAffinePhase
import PrimeFactorUnimodality.Helpers.Analytic.XiSimplePhaseIntervals

/-! # Shared affine phase checks without per-sample logarithms

One checked base logarithm prepares both the phase value and slope. Sample
evaluation uses rational interval arithmetic and the one-sided quadratic
remainder `[0,Q]`. The Stirling correction and the separate Gamma remainder
are retained. A model is valid only when its actual base value and slope
are enclosed; numerical data alone does not supply these proofs.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core

/-- A common rational base and certified affine coefficients for a block. -/
structure XiAffinePhaseIntervals where
  base : ℚ
  value : IntervalRat
  slope : IntervalRat

namespace XiAffinePhaseIntervals

/-- The coefficients enclose the actual elementary phase and tangent slope. -/
structure Valid (d : XiAffinePhaseIntervals) : Prop where
  base_pos : 0 < d.base
  value : xiSimplePhase d.base ∈ d.value
  slope : xiSimplePhaseSlope d.base ∈ d.slope

/-- Compute the base logarithm once and share it between both coefficients. -/
def prepare (d : XiSimplePhaseIntervals) (c : SharedTaylorIntervals) (base : ℚ) :
    XiAffinePhaseIntervals :=
  let H := base / 2
  let L := IntervalRat.sub (c.log H) d.logPi
  ⟨base, IntervalRat.add
    (IntervalRat.sub (IntervalRat.scale H L) (IntervalRat.singleton H))
    (IntervalRat.scale (7 / 8) d.pi), IntervalRat.scale (1 / 2) L⟩

/-- Shared pi data and one prepared logarithm certify both affine coefficients. -/
theorem prepare_valid {d : XiSimplePhaseIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {base : ℚ} (hb : 0 < base) :
    (prepare d c base).Valid := by
  have hlog := SharedTaylorIntervals.mem_log hc (div_pos hb (by norm_num : (0 : ℚ) < 2))
  have hL := IntervalRat.mem_sub hlog hd.2
  refine ⟨hb, ?_, ?_⟩
  · dsimp only [prepare]
    have h := IntervalRat.mem_add
      (IntervalRat.mem_sub (IntervalRat.mem_scale (base / 2) hL)
        (IntervalRat.mem_singleton (base / 2))) (IntervalRat.mem_scale (7 / 8) hd.1)
    convert h using 1
    unfold xiSimplePhase
    push_cast
    ring
  · dsimp only [prepare]
    have h := IntervalRat.mem_scale (1 / 2) hL
    convert h using 1
    unfold xiSimplePhaseSlope
    push_cast
    ring

/-- Validate materialized, possibly outward-rounded coefficients once for the whole block. -/
def checkPrepared (d : XiAffinePhaseIntervals) (p : XiSimplePhaseIntervals)
    (c : SharedTaylorIntervals) : Bool :=
  let prepared := prepare p c d.base
  decide (0 < d.base) && intervalSubset prepared.value d.value &&
    intervalSubset prepared.slope d.slope

/-- Literal coefficients receive their semantic proof from checked preparation, not an assertion. -/
theorem valid_of_checkPrepared {d : XiAffinePhaseIntervals} {p : XiSimplePhaseIntervals}
    (hp : p.Valid) {c : SharedTaylorIntervals} (hc : c.Prepared)
    (h : d.checkPrepared p c = true) : d.Valid := by
  simp only [checkPrepared, Bool.and_eq_true, decide_eq_true_eq] at h
  have hp' := prepare_valid hp hc h.1.1
  exact ⟨h.1.1, mem_of_intervalSubset h.1.2 hp'.value, mem_of_intervalSubset h.2 hp'.slope⟩

/-- Enclose the affine model using only rational operations at the sample. -/
def affine (d : XiAffinePhaseIntervals) (T : IntervalRat) : IntervalRat :=
  IntervalRat.add d.value
    (IntervalRat.mul d.slope (IntervalRat.sub T (IntervalRat.singleton d.base)))

/-- The exact affine model lies in its computed interval. -/
theorem mem_affine {d : XiAffinePhaseIntervals} (hd : d.Valid) {T : IntervalRat}
    {t : ℝ} (ht : t ∈ T) : xiAffinePhase d.base t ∈ d.affine T :=
  IntervalRat.mem_add hd.value
    (IntervalRat.mem_mul hd.slope (IntervalRat.mem_sub ht (IntervalRat.mem_singleton d.base)))

/-- A one-sided remainder enclosure; invalid nonpositive bases are rejected by the checker. -/
def remainder (d : XiAffinePhaseIntervals) (T : IntervalRat) : IntervalRat :=
  ⟨0, intervalPointRadius T d.base ^ 2 / (2 * |d.base|),
    div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))⟩

/-- The quadratic remainder bound holds for every positive height in the sample interval. -/
theorem mem_remainder {d : XiAffinePhaseIntervals} (hd : d.Valid) {T : IntervalRat}
    {t : ℝ} (ht : t ∈ T) (htpos : 0 < t) :
    xiSimplePhase t - xiAffinePhase d.base t ∈ d.remainder T := by
  have hb : (0 : ℝ) < d.base := by exact_mod_cast hd.base_pos
  have hr := abs_sub_le_intervalPointRadius ht d.base
  have hs : (t - (d.base : ℝ)) ^ 2 ≤ (intervalPointRadius T d.base : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hr 2
  refine ⟨?_, (xiSimplePhase_sub_affine_le hb htpos).trans ?_⟩
  · simpa only [remainder, Rat.cast_zero] using
      sub_nonneg.mpr (xiAffinePhase_le_simple hb htpos)
  · change _ ≤ ((intervalPointRadius T d.base ^ 2 / (2 * |d.base|) : ℚ) : ℝ)
    push_cast
    rw [abs_of_pos hb]
    exact div_le_div_of_nonneg_right hs (by positivity)

/-- Add the one-sided remainder without reevaluating a logarithm at the sample height. -/
def evaluate (d : XiAffinePhaseIntervals) (T : IntervalRat) : IntervalRat :=
  IntervalRat.add (d.affine T) (d.remainder T)

/-- The full elementary phase is enclosed, including all coefficient and remainder errors. -/
theorem mem_evaluate {d : XiAffinePhaseIntervals} (hd : d.Valid) {T : IntervalRat}
    {t : ℝ} (ht : t ∈ T) (htpos : 0 < t) : xiSimplePhase t ∈ d.evaluate T := by
  have h := IntervalRat.mem_add (mem_affine hd ht) (mem_remainder hd ht htpos)
  simpa only [evaluate, add_sub_cancel] using h

/-- Retain the entire analytical simplification error and reject nonpositive domains. -/
def check (d : XiAffinePhaseIntervals) (T : IntervalRat) (phase error : ℚ) : Bool :=
  decide (0 < d.base ∧ 0 < T.lo ∧
    33 / (16 * T.lo) + intervalPointRadius (d.evaluate T) phase ≤ error)

/-- An accepted rational check supplies the actual Stirling-phase inequality. -/
theorem abs_stirling_sub_le_of_check {d : XiAffinePhaseIntervals} (hd : d.Valid)
    {T : IntervalRat} {t : ℝ} (ht : t ∈ T) {phase error : ℚ}
    (h : d.check T phase error = true) :
    |turingStirlingPhase t - (phase : ℝ)| ≤ (error : ℝ) := by
  simp only [check, decide_eq_true_eq] at h
  have hpos : (0 : ℝ) < T.lo := Rat.cast_pos.mpr h.2.1
  have htpos : 0 < t := hpos.trans_le ht.1
  have he := abs_sub_le_intervalPointRadius (mem_evaluate hd ht htpos) phase
  have hb : 33 / (16 * t) ≤ ((33 / (16 * T.lo) : ℚ) : ℝ) := by
    push_cast
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left ht.1 (by norm_num))
  have hbudget : ((33 / (16 * T.lo) : ℚ) : ℝ) +
      (intervalPointRadius (d.evaluate T) phase : ℝ) ≤ (error : ℝ) := by
    exact_mod_cast h.2.2
  exact ((abs_sub_le _ _ _).trans
    (add_le_add (abs_turingStirlingPhase_sub_simple_le htpos) he)).trans
      ((add_le_add hb le_rfl).trans hbudget)

/-- The actual counting phase retains the separate complete Gamma remainder. -/
theorem abs_counting_sub_le_of_check {d : XiAffinePhaseIntervals} (hd : d.Valid)
    {T : IntervalRat} {t : ℝ} (ht : t ∈ T) {phase error : ℚ}
    (h : d.check T phase error = true) :
    |turingCountingPhase t - (phase : ℝ)| ≤ 1 / 10 + (error : ℝ) :=
  (abs_sub_le _ _ _).trans (add_le_add (abs_turingCountingPhase_sub_stirling_le t)
    (abs_stirling_sub_le_of_check hd ht h))

end XiAffinePhaseIntervals

end PrimeFactorUnimodality
