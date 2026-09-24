import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.QuarterNorm

/-! Beta ratios and the compensated Gamma bound cover arbitrary signed heights. -/

example {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    ‖Complex.betaIntegral u v‖ ≤
      Real.Gamma u.re * Real.Gamma v.re / Real.Gamma (u.re + v.re) :=
  Complex.norm_betaIntegral_le hu hv

example {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖Complex.Gamma s‖ / ‖Complex.Gamma (s + (a : ℂ))‖ ≤
      Real.Gamma s.re / Real.Gamma (s.re + a) :=
  Complex.norm_Gamma_div_norm_Gamma_add_real_le hs ha

example (t : ℝ) :
    ‖Complex.Gamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I)‖ * Real.exp (Real.pi * t / 2) ≤
      Real.sqrt (2 * Real.pi * (Real.Gamma (1 / 4) / Real.Gamma (3 / 4))) :=
  Complex.norm_Gamma_quarter_add_mul_I_mul_exp_le t

example :
    ‖Complex.Gamma ((1 / 4 : ℂ) + ((-7 : ℝ) : ℂ) * Complex.I)‖ *
        Real.exp (Real.pi * (-7) / 2) ≤
      Real.sqrt (2 * Real.pi * (Real.Gamma (1 / 4) / Real.Gamma (3 / 4))) :=
  Complex.norm_Gamma_quarter_add_mul_I_mul_exp_le (-7)

example (t : ℝ) :
    ‖Complex.Gamma ((1 / 4 : ℂ) + (t : ℂ) * Complex.I)‖ * Real.exp (Real.pi * t / 2) ≤ 5 :=
  Complex.norm_Gamma_quarter_add_mul_I_mul_exp_le_five t
