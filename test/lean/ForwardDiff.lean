import PrimeFactorUnimodality.Mathlib.Analysis.Calculus.Deriv.ForwardDiff

/-! # Samplewise error propagation through binomial differences -/

open Function Finset

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h x : ℝ) (n : ℕ) (f : ℝ → E) (v : ℕ → E) (e : ℕ → ℝ)
    (he : ∀ j ∈ range (n + 1), ‖f (x + j • h) - v j‖ ≤ e j) :
    ‖((fwdDiff h)^[n] f) x -
      ∑ j ∈ range (n + 1), ((-1 : ℤ) ^ (n - j) * n.choose j) • v j‖ ≤
      ∑ j ∈ range (n + 1), (n.choose j : ℝ) * e j :=
  norm_fwdDiff_iter_sub_sum_le h x n f v e he

example (h x e : ℝ) (f : ℝ → ℝ) (v : ℕ → ℝ) (he : |f x - v 0| ≤ e) :
    ‖((fwdDiff h)^[0] f) x - v 0‖ ≤ e := by
  have hn := norm_fwdDiff_iter_sub_sum_le h x 0 f v (fun _ => e) (by simpa using he)
  simpa using hn
