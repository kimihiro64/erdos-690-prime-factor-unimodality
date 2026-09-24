import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.DiscretePoisson

/-! Integer-series regrouping, signed frequencies, centered representatives and DFT errors. -/

example {N : ℕ} [NeZero N] {a : ℤ → ℂ} (ha : Summable a) (j : ℤ) :
    (∑' n : ℤ, a n * fourier n (((j : ℝ) / N : ℝ) : UnitAddCircle)) =
      ZMod.dft (ZMod.residueTsum a) (-(j : ZMod N)) :=
  ZMod.tsum_fourier_grid_eq_dft_neg ha j

example {a : ℤ → ℂ} (ha : Summable a) :
    (∑' n : ℤ, a n * fourier n ((-(1 / 4 : ℝ)) : UnitAddCircle)) =
      ZMod.dft (ZMod.residueTsum a) (1 : ZMod 4) := by
  convert ZMod.tsum_fourier_grid_eq_dft_neg (N := 4) ha (-1) using 1 <;> norm_num

example (a : ℤ → ℂ) : ZMod.residueTsum a (3 : ZMod 4) =
    ∑' l : ℤ, a (-1 + 4 * l) :=
  ZMod.residueTsum_eq_of_intCast (N := 4) a (-1) 3 (by decide)

example : ((3 : ZMod 4).valMinAbs : ℝ) = -1 := by
  exact_mod_cast (show (3 : ZMod 4).valMinAbs = (-1 : ℤ) by decide)

example {a b : ZMod 4 → ℂ} {ε : ℝ} (h : ∀ i, ‖a i - b i‖ ≤ ε) (j : ZMod 4) :
    ‖ZMod.dft a j - ZMod.dft b j‖ ≤ 4 * ε := by
  simpa using ZMod.norm_dft_sub_le h j
