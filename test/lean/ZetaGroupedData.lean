import PrimeFactorUnimodality.Helpers.Analytic.ZetaGroupedData

/-! # Shared exponential evaluation interfaces and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset

variable {ι κ : Type*} [DecidableEq κ]

example (N m : ℕ) {s : ℂ} (hs : s ≠ 0) :
    zetaEulerApproxOrder N s m =
      (∑ n ∈ Icc 1 N, 1 / (n : ℂ) ^ s) + zetaEulerCorrection N s m := by
  exact PrimeFactorUnimodality.zetaEulerApproxOrder_eq_prefix_add_correction N m hs

example (m : ℕ) (t : ℝ) : zetaEulerApproxOrder 0 ((1 / 2 : ℂ) + t * I) m =
    zetaEulerCorrection 0 ((1 / 2 : ℂ) + t * I) m := by
  simpa using zetaEulerApproxOrder_eq_prefix_add_correction 0 m (by
    intro h; have hr := congrArg Complex.re h; norm_num at hr)

example {d : ZetaGroupedBlock} (h : d.cutoff = 0) : ¬d.Valid := by
  intro hd
  have := hd.cutoff_pos
  omega

def unitBlock : ZetaGroupedBlock :=
  ⟨1, 0, 1, 0, 0, {0}, fun _ => 0, fun _ _ => 1, fun _ _ => 0⟩

example : unitBlock.Valid := by
  constructor
  · norm_num [unitBlock]
  · intro n hn
    simp [unitBlock]
  · intro n hn
    simp [unitBlock, dirichletFrequency]
  · intro b hb j hj
    have hb' : b = 0 := by simpa [unitBlock] using hb
    have hj' : j = 0 := by simpa [unitBlock] using hj
    subst b
    subst j
    norm_num [unitBlock, expSumMoment, ZetaGroupedBlock.center]

end

end PrimeFactorUnimodality.Tests
