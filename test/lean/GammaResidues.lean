import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.Residue
import PrimeFactorUnimodality.Mathlib.Analysis.SpecialFunctions.Gamma.ShiftNorm

/-! Arbitrary Gamma poles, inverse affine slope and shifted strip bounds. -/

open Filter Complex
open scoped Topology

example (n : ℕ) :
    Tendsto (fun z : ℂ => (z + (n : ℂ)) * Gamma z) (𝓝[≠] (-(n : ℂ)))
      (𝓝 (((-1 : ℂ) ^ n) / (n.factorial : ℂ))) :=
  tendsto_add_nat_mul_Gamma n

example (n : ℕ) : meromorphicOrderAt Gamma (-(n : ℂ)) = (-1 : ℤ) :=
  meromorphicOrderAt_Gamma_neg_nat n

example : Tendsto (fun z : ℂ => z * Gamma (2 * z)) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  simpa using tendsto_sub_mul_Gamma_affine 0 (a := 2) (b := 0) (p := 0)
    (by norm_num) (by norm_num)

example (n : ℕ) {z : ℂ} (hz : 1 ≤ |z.im|) : ‖Gamma z‖ ≤ ‖Gamma (z + (n : ℂ))‖ :=
  norm_Gamma_le_norm_Gamma_add_nat hz n

example (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℂ}
    (hz : 1 ≤ |z.im|) (hre : z.re + (n : ℝ) ∈ Set.Icc a b) :
    ‖Gamma z‖ ≤ max (Real.Gamma a) (Real.Gamma b) :=
  norm_Gamma_le_max_of_shifted_re_mem_Icc n ha hb hz hre
