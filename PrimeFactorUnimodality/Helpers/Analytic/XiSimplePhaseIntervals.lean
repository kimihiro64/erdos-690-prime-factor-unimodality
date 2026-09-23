import PrimeFactorUnimodality.Helpers.Analytic.RationalIntervalBounds
import PrimeFactorUnimodality.Helpers.Analytic.SharedLogIntervals
import PrimeFactorUnimodality.Helpers.Analytic.XiSimplePhase

/-! # Executable elementary xi-phase error checks

Pi and its logarithm are shared by every sample. Each positive height needs
only a prepared real-logarithm interval and rational arithmetic. The check
includes the full argument/norm simplification error before it feeds the
existing Stirling-phase consumer. Its Gamma remainder is still separate.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core

/-- Shared numerical constants for the elementary phase. -/
structure XiSimplePhaseIntervals where
  pi : IntervalRat
  logPi : IntervalRat

namespace XiSimplePhaseIntervals

/-- Both shared intervals enclose the actual transcendental constants. -/
def Valid (d : XiSimplePhaseIntervals) : Prop :=
  Real.pi ∈ d.pi ∧ Real.log Real.pi ∈ d.logPi

/-- Prepare the shared logarithm once from an enclosed positive pi interval. -/
def prepare (c : SharedTaylorIntervals) (P : IntervalRat) : XiSimplePhaseIntervals :=
  ⟨P, c.logInterval P⟩

/-- The scalar logarithm theorem validates the shared configuration. -/
theorem prepare_valid {c : SharedTaylorIntervals} (hc : c.Prepared) {P : IntervalRat}
    (hP : 0 < P.lo) (hpi : Real.pi ∈ P) : (prepare c P).Valid :=
  ⟨hpi, SharedTaylorIntervals.mem_logInterval hc hP hpi⟩

/-- Evaluate the elementary expression while retaining all interval dependence. -/
def evaluate (d : XiSimplePhaseIntervals) (c : SharedTaylorIntervals)
    (T : IntervalRat) : IntervalRat :=
  let H := IntervalRat.scale (1 / 2) T
  IntervalRat.add
    (IntervalRat.sub (IntervalRat.sub (IntervalRat.mul H (c.logInterval H)) H)
      (IntervalRat.mul H d.logPi))
    (IntervalRat.scale (7 / 8) d.pi)

/-- Every positive enclosed height has its actual elementary phase inside the result. -/
theorem mem_evaluate {d : XiSimplePhaseIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {T : IntervalRat}
    (hT : 0 < T.lo) {t : ℝ} (ht : t ∈ T) : xiSimplePhase t ∈ d.evaluate c T := by
  have hh : t / 2 ∈ IntervalRat.scale (1 / 2) T := by
    simpa [div_eq_mul_inv, mul_comm] using IntervalRat.mem_scale (1 / 2) ht
  have hhpos : 0 < (IntervalRat.scale (1 / 2) T).lo := by
    norm_num [IntervalRat.scale]
    exact hT
  have hlog := SharedTaylorIntervals.mem_logInterval hc hhpos hh
  have h := IntervalRat.mem_add
    (IntervalRat.mem_sub (IntervalRat.mem_sub (IntervalRat.mem_mul hh hlog) hh)
      (IntervalRat.mem_mul hh hd.2)) (IntervalRat.mem_scale (7 / 8) hd.1)
  have he : xiSimplePhase t = t / 2 * Real.log (t / 2) - t / 2 -
      t / 2 * Real.log Real.pi + ((7 / 8 : ℚ) : ℝ) * Real.pi := by
    unfold xiSimplePhase
    push_cast
    ring
  rw [he]
  exact h

/-- The full rational budget includes the height-dependent analytical simplification error. -/
def check (d : XiSimplePhaseIntervals) (c : SharedTaylorIntervals)
    (T : IntervalRat) (phase error : ℚ) : Bool :=
  decide (0 < T.lo ∧ 33 / (16 * T.lo) + intervalPointRadius (d.evaluate c T) phase ≤ error)

/-- A successful check supplies the exact phase premise of the existing grid evaluator. -/
theorem abs_stirling_sub_le_of_check {d : XiSimplePhaseIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {T : IntervalRat} {t : ℝ} (ht : t ∈ T)
    {phase error : ℚ} (h : d.check c T phase error = true) :
    |turingStirlingPhase t - (phase : ℝ)| ≤ (error : ℝ) := by
  simp only [check, decide_eq_true_eq] at h
  have hpos : (0 : ℝ) < T.lo := Rat.cast_pos.mpr h.1
  have htpos : 0 < t := hpos.trans_le ht.1
  have he := abs_sub_le_intervalPointRadius (mem_evaluate hd hc h.1 ht) phase
  have hb : 33 / (16 * t) ≤ ((33 / (16 * T.lo) : ℚ) : ℝ) := by
    push_cast
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left ht.1 (by norm_num))
  have hbudget : ((33 / (16 * T.lo) : ℚ) : ℝ) +
      (intervalPointRadius (d.evaluate c T) phase : ℝ) ≤ (error : ℝ) := by
    exact_mod_cast h.2
  exact ((abs_sub_le _ _ _).trans
    (add_le_add (abs_turingStirlingPhase_sub_simple_le htpos) he)).trans
      ((add_le_add hb le_rfl).trans hbudget)

/-- Retain the separate complete Gamma remainder when bounding the actual xi phase. -/
theorem abs_counting_sub_le_of_check {d : XiSimplePhaseIntervals} (hd : d.Valid)
    {c : SharedTaylorIntervals} (hc : c.Prepared) {T : IntervalRat} {t : ℝ} (ht : t ∈ T)
    {phase error : ℚ} (h : d.check c T phase error = true) :
    |turingCountingPhase t - (phase : ℝ)| ≤ 1 / 10 + (error : ℝ) :=
  (abs_sub_le _ _ _).trans (add_le_add (abs_turingCountingPhase_sub_stirling_le t)
    (abs_stirling_sub_le_of_check hd hc ht h))

end XiSimplePhaseIntervals

end PrimeFactorUnimodality
