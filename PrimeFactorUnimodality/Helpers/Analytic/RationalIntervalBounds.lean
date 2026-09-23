import LeanCert.Core.IntervalRat.Basic

/-! # Rational endpoint tests for real interval bounds

These adapters use the proved interval arithmetic membership relation.
They check containment and distance budgets without evaluating real numbers.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core

/-- Maximum distance from a rational point to either interval endpoint. -/
def intervalPointRadius (I : IntervalRat) (q : ℚ) : ℚ := max |I.lo - q| |I.hi - q|

/-- Every interval member lies within the computable endpoint radius. -/
theorem abs_sub_le_intervalPointRadius {x : ℝ} {I : IntervalRat} (hx : x ∈ I) (q : ℚ) :
    |x - (q : ℝ)| ≤ (intervalPointRadius I q : ℝ) := by
  have hlo : |(I.lo : ℝ) - q| ≤ (intervalPointRadius I q : ℝ) := by
    exact_mod_cast le_max_left |I.lo - q| |I.hi - q|
  have hhi : |(I.hi : ℝ) - q| ≤ (intervalPointRadius I q : ℝ) := by
    exact_mod_cast le_max_right |I.lo - q| |I.hi - q|
  obtain ⟨hxlo, hxhi⟩ := hx
  obtain ⟨hl, _⟩ := abs_le.mp hlo
  obtain ⟨_, hh⟩ := abs_le.mp hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Rational endpoint comparison for inclusion of an entire interval. -/
def intervalSubset (I J : IntervalRat) : Bool := decide (J.lo ≤ I.lo ∧ I.hi ≤ J.hi)

/-- Successful containment retains every real member, including boundary points. -/
theorem mem_of_intervalSubset {I J : IntervalRat} (h : intervalSubset I J = true)
    {x : ℝ} (hx : x ∈ I) : x ∈ J := by
  simp only [intervalSubset, decide_eq_true_eq] at h
  have hlo : (J.lo : ℝ) ≤ I.lo := by exact_mod_cast h.1
  have hhi : (I.hi : ℝ) ≤ J.hi := by exact_mod_cast h.2
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

end PrimeFactorUnimodality
