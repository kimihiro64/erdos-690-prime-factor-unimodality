import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.NegativeHalfNorm

/-! Opposite half-integer lines include the exceptional first pair and every signed height. -/

example (m : ℕ) (t : ℝ) :
    ‖Complex.Gamma (-(((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (8 / 3) * ‖Complex.Gamma ((((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
  Complex.norm_Gamma_neg_nat_sub_half_le m t

example (m : ℕ) (hm : 2 ≤ m) (t : ℝ) :
    ‖Complex.Gamma (-(((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ‖Complex.Gamma ((((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
  Complex.norm_Gamma_neg_nat_sub_half_le_pos m hm t

example : Real.Gamma (3 / 2) < Real.Gamma (-(3 / 2)) := by
  rw [Real.Gamma_neg_three_halves_eq]
  nlinarith [Real.Gamma_pos_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)]

example (m : ℕ) :
    Continuous (fun t : ℝ =>
      Complex.Gamma (-(((m : ℝ) + 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
  Complex.continuous_Gamma_neg_nat_sub_half m
