import PrimeFactorUnimodality.Helpers.Analytic.ComplexInterval
import PrimeFactorUnimodality.Helpers.Analytic.ZetaEulerFactor

/-! # Successive interval evaluation of the short Bernoulli polynomial

The rational Bernoulli coefficients are prepared once, independently of all
sample heights. One evolving normalized rising factor is then shared across
successive orders. The entire list, including zero coefficients, is retained.
-/

namespace PrimeFactorUnimodality

open Complex Polynomial

/-- Exact rational boundary coefficients in their recurrence order. -/
def eulerBernoulliCoefficients (start count : ℕ) : List ℚ :=
  (List.range' start count).map (fun j =>
    _root_.bernoulli (j + 1) / ((j + 1).factorial : ℚ))

/-- Advance the normalized rising product with one multiplication and one rational scale. -/
def eulerRisingStep (N : ℕ) (S : ComplexInterval) (k : ℕ)
    (W : ComplexInterval) : ComplexInterval :=
  ComplexInterval.scale (1 / (N : ℚ))
    (W.mul (S.add (ComplexInterval.point ⟨k, 0⟩)))

/-- The recurrence preserves the exact scaled rising factorial. -/
theorem mem_eulerRisingStep (N k : ℕ) {s : ℂ} {S W : ComplexInterval}
    (hs : s ∈ S) (hw : zetaRisingFactor s k / (N : ℂ) ^ k ∈ W) :
    zetaRisingFactor s (k + 1) / (N : ℂ) ^ (k + 1) ∈ eulerRisingStep N S k W := by
  have hk : (k : ℂ) ∈ ComplexInterval.point ⟨k, 0⟩ := by
    simpa using ComplexInterval.mem_constant (k : ℚ)
  have h := ComplexInterval.mem_scale (1 / (N : ℚ))
    (ComplexInterval.mem_mul hw (ComplexInterval.mem_add hs hk))
  rw [zetaRisingFactor_div_pow_succ]
  simpa [eulerRisingStep, div_eq_mul_inv, mul_comm] using h

/-- Evaluate in one forward pass, without recomputing any rising-factor prefix. -/
def eulerBernoulliInterval (N : ℕ) (S : ComplexInterval) (start : ℕ)
    (W : ComplexInterval) : List ℚ → ComplexInterval
  | [] => ComplexInterval.point ⟨0, 0⟩
  | b :: rest => (ComplexInterval.scale b W).add
      (eulerBernoulliInterval N S (start + 1) (eulerRisingStep N S start W) rest)

/-- All finite Bernoulli terms are enclosed by the successive-factor evaluation. -/
theorem mem_eulerBernoulliInterval (N : ℕ) {s : ℂ} {S : ComplexInterval} (hs : s ∈ S)
    (start count : ℕ) {W : ComplexInterval}
    (hw : zetaRisingFactor s start / (N : ℂ) ^ start ∈ W) :
    ((List.range' start count).map (fun j =>
      (bernoulliNormalizedReal (j + 1) 0 : ℂ) *
        (zetaRisingFactor s j / (N : ℂ) ^ j))).sum ∈
      eulerBernoulliInterval N S start W (eulerBernoulliCoefficients start count) := by
  induction count generalizing start W with
  | zero =>
    simpa [eulerBernoulliCoefficients, eulerBernoulliInterval] using
      ComplexInterval.mem_constant 0
  | succ count ih =>
    simp only [eulerBernoulliCoefficients, List.range'_succ, List.map_cons,
      List.sum_cons, eulerBernoulliInterval]
    apply ComplexInterval.mem_add
    · simpa only [bernoulliNormalizedReal_zero, Complex.ofReal_ratCast] using
        ComplexInterval.mem_scale
          (_root_.bernoulli (start + 1) / ((start + 1).factorial : ℚ)) hw
    · exact ih (start + 1) (mem_eulerRisingStep N start hs hw)

end PrimeFactorUnimodality
