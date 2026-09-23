import PrimeFactorUnimodality.Mathlib.NumberTheory.LSeries.GroupedEvaluation

/-! # Shared exponential evaluation interfaces and boundary cases -/

set_option autoImplicit false

namespace PrimeFactorUnimodality.Tests

noncomputable section

open Complex Finset

variable {ι κ : Type*} [DecidableEq κ]

example (n : ℕ) (hn : 0 < n) (s : ℂ) (R v : ℝ) :
    1 / (n : ℂ) ^ (s + (R * v : ℝ) * I) =
      (1 / (n : ℂ) ^ s) * exp (I * ((v * dirichletFrequency R n : ℝ) : ℂ)) := by
  exact Complex.natCpow_inv_shift n hn s R v

example {n : ℕ} (hn : 0 < n) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖1 / (n : ℂ) ^ s‖ ≤ 1 := by
  exact Complex.norm_natCpow_inv_le_one hn hs

example (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    {s : ℂ} (hs : 0 ≤ s.re) : (∑ n ∈ S, ‖1 / (n : ℂ) ^ s‖) ≤ S.card := by
  exact Complex.sum_norm_natCpow_inv_le_card S hS hs

example (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    {s : ℂ} (hs : 0 ≤ s.re) (R : ℝ) {v : ℝ} (hv : |v| ≤ 1) (m : ℕ) :
    ‖(∑ n ∈ S, 1 / (n : ℂ) ^ (s + (R * v : ℝ) * I)) -
      dirichletGroupedApprox S s R m v‖ ≤
      (S.card : ℝ) * ((1 / 2 : ℝ) ^ m * Real.exp (1 / 2)) := by
  exact Complex.norm_dirichlet_sum_sub_grouped_le S hS hs R hv m

example {κ : Type*} [DecidableEq κ]
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) {s : ℂ} (hs : 0 ≤ s.re)
    (R : ℝ) (B : Finset κ) (bin : ℕ → κ) (c : κ → ℝ)
    (hbin : ∀ n ∈ S, bin n ∈ B) {A v : ℝ} (hA : 0 ≤ A) (hv : |v| ≤ 1)
    (hres : ∀ n ∈ S, |dirichletFrequency R n - c (bin n)| ≤ A)
    (m : ℕ) (a : κ → ℕ → ℂ) (p : κ → ℂ) (ε : κ → ℕ → ℝ) (δ : κ → ℝ)
    (ha : ∀ b ∈ B, ∀ j ∈ range m,
      ‖expSumMoment (S.filter (fun n => bin n = b)) (fun n => 1 / (n : ℂ) ^ s)
        (fun n => dirichletFrequency R n - c b) j - a b j‖ ≤ ε b j)
    (hp : ∀ b ∈ B, ‖exp (I * ((v * c b : ℝ) : ℂ)) - p b‖ ≤ δ b) :
    ‖(∑ n ∈ S, 1 / (n : ℂ) ^ (s + (R * v : ℝ) * I)) -
      ∑ b ∈ B, p b * ∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ ≤
      (S.card : ℝ) * (A ^ m * Real.exp A) +
        ∑ b ∈ B, ((∑ j ∈ range m, ε b j * |v| ^ j) +
          ‖∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ * δ b) := by
  exact Complex.norm_dirichlet_sum_sub_rounded_with_centers_le S hS hs R B bin c hbin hA hv hres m a p ε δ ha hp

example
    (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) {s : ℂ} (hs : 0 ≤ s.re)
    (R : ℝ) {v : ℝ} (hv : |v| ≤ 1) (m : ℕ)
    (a : ℤ → ℕ → ℂ) (p : ℤ → ℂ) (ε : ℤ → ℕ → ℝ) (δ : ℤ → ℝ)
    (ha : ∀ b ∈ dirichletFrequencyBins S R, ∀ j ∈ range m,
      ‖dirichletGroupMoment S s R b j - a b j‖ ≤ ε b j)
    (hp : ∀ b ∈ dirichletFrequencyBins S R,
      ‖exp (I * ((v * b : ℝ) : ℂ)) - p b‖ ≤ δ b) :
    ‖(∑ n ∈ S, 1 / (n : ℂ) ^ (s + (R * v : ℝ) * I)) -
      ∑ b ∈ dirichletFrequencyBins S R, p b * ∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ ≤
      (S.card : ℝ) * ((1 / 2 : ℝ) ^ m * Real.exp (1 / 2)) +
        ∑ b ∈ dirichletFrequencyBins S R, ((∑ j ∈ range m, ε b j * |v| ^ j) +
          ‖∑ j ∈ range m, a b j * (v : ℂ) ^ j‖ * δ b) := by
  exact Complex.norm_dirichlet_sum_sub_roundedGrouped_le S hS hs R hv m a p ε δ ha hp

example (s : ℂ) (R v : ℝ) :
    1 / (1 : ℂ) ^ (s + (R * v : ℝ) * I) =
      (1 / (1 : ℂ) ^ s) * exp (I * ((v * dirichletFrequency R 1 : ℝ) : ℂ)) := by
  simpa only [Nat.cast_one] using natCpow_inv_shift 1 (by norm_num) s R v

example {s : ℂ} (hs : 0 ≤ s.re) (R : ℝ) (m : ℕ) :
    ‖(∑ n ∈ Icc (1 : ℕ) 7, 1 / (n : ℂ) ^ (s + (R * (-1) : ℝ) * I)) -
      dirichletGroupedApprox (Icc (1 : ℕ) 7) s R m (-1)‖ ≤
      ((Icc (1 : ℕ) 7).card : ℝ) * ((1 / 2 : ℝ) ^ m * Real.exp (1 / 2)) :=
  norm_dirichlet_sum_sub_grouped_le (Icc 1 7) (fun n hn => (mem_Icc.mp hn).1)
    hs R (v := -1) (by norm_num) m

end

end PrimeFactorUnimodality.Tests
