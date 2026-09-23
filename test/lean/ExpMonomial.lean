import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Exp.Monomial

/-! # Regression statements for the far-ray Dusart bounds -/

namespace PrimeFactorUnimodality.Tests

open Real

example (n : ℕ) {a x y : ℝ}
    (ha : 0 < a) (hx : (n : ℝ) / a ≤ x) (hxy : x ≤ y) :
    y ^ n * exp (-a * y) ≤ x ^ n * exp (-a * x) := by
  apply Real.pow_mul_exp_neg_le_of_le <;> assumption

example (n : ℕ) {a : ℝ} (ha : 0 < a) :
    AntitoneOn (fun x : ℝ => x ^ n * exp (-a * x)) (Set.Ici ((n : ℝ) / a)) := by
  apply Real.antitoneOn_pow_mul_exp_neg <;> assumption

example {a x y : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (hxy : x ≤ y) :
    exp (-a * y) ≤ exp (-a * x) := by
  simpa using Real.pow_mul_exp_neg_le_of_le 0 ha (by simpa using hx) hxy

example {y : ℝ} (hy : 4 ≤ y) :
    y ^ 5 * exp (-(5 / 4 : ℝ) * y) ≤ 4 ^ 5 * exp (-(5 / 4 : ℝ) * 4) :=
  Real.pow_mul_exp_neg_le_of_le 5 (by norm_num) (by norm_num) hy

example {n : ℕ} {a x : ℝ} (ha : 0 < a) (hx : (n : ℝ) / a ≤ x) :
    x ^ n * exp (-a * x) ≤ x ^ n * exp (-a * x) :=
  Real.pow_mul_exp_neg_le_of_le n ha hx le_rfl

end PrimeFactorUnimodality.Tests
