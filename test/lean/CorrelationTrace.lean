import PrimeFactorUnimodality.Mathlib.Analysis.Fourier.CorrelationTrace

/-! Regression checks for cross terms, collisions, transform signs and trace normalization. -/

open Finset

-- Both errors are nonzero: dropping their cross term would give the false bound 10.
example : ‖(4 : ℂ) * 6 - 3 * 4‖ ≤ (1 : ℝ) * (4 + 2) + 3 * 2 := by
  apply Complex.norm_mul_sub_mul_le_of_approx_bounds <;> norm_num

-- A nonzero initial accumulator contributes even when no terms are processed.
example (a v : ℕ → ℂ) (ε : ℕ → ℝ) {δ : ℝ} (h : ‖v 0‖ ≤ δ) :
    ‖(∑ i ∈ range 0, a i) - v 0‖ ≤ δ + ∑ i ∈ range 0, ε i :=
  Complex.norm_sum_range_sub_accumulated_le 0 a v ε h (by omega)

-- Product, addition and initialization errors each enter the accumulated budget.
example : ‖(∑ _i ∈ range 1, (2 : ℂ) * 3) - 7‖ ≤ (1 : ℝ) + ∑ _i ∈ range 1, (1 + 1) := by
  have he := Complex.norm_sum_range_mul_sub_accumulated_le 1
    (fun _ => 2) (fun _ => 3) (fun _ => 5) (fun i => if i = 0 then 1 else 7)
    (fun _ => 1) (fun _ => 1) (δ := 1)
    (by norm_num) (by intro i hi; norm_num)
    (by
      intro i hi
      have : i = 0 := by omega
      subst i
      norm_num)
  simpa using he

example {N : ℕ} [NeZero N] (j : ZMod N) (a p : ℕ → ℂ)
    (ε : ℕ → ℝ) {b : ℂ} {δ : ℝ}
    (ha : ∀ i ∈ range 2, ‖a i - p i‖ ≤ ε i) (hb : ‖p 0 + p 1 - b‖ ≤ δ) :
    ‖ZMod.bucketCoefficients (range 2) (fun _ => j) a j - b‖ ≤ ε 0 + ε 1 + δ := by
  simpa [sum_range_succ] using
    ZMod.norm_bucketCoefficients_sub_rounded_le (range 2) (fun _ => j) ha j
      (by simpa [ZMod.bucketCoefficients, sum_range_succ] using hb)

example {ι : Type*} {n : ℕ} (t : Fourier.CorrelationTrace ι n)
    (i : ι) (l : ZMod (2 ^ n)) :
    t.leftDFT i (-l) = (t.left i).values[l.val]'(ZMod.val_lt l) := by
  simp only [Fourier.CorrelationTrace.leftDFT, neg_neg]

noncomputable def scalarCorrelation : Fourier.CorrelationTrace (Fin 1) 0 where
  leftInput := fun _ => Vector.singleton 3
  rightInput := fun _ => Vector.singleton 4
  left := fun _ => .leaf 3 0
  right := fun _ => .leaf 4 0
  products := Vector.singleton 12
  inverse := .leaf 12 0
  leftCap := fun _ => 3
  rightCap := fun _ => 4
  rounding := 0

theorem scalarCorrelation_valid : scalarCorrelation.Valid univ
    (fun _ _ => 3) (fun _ _ => 4) (fun _ _ => 0) (fun _ _ => 0) := by
  constructor <;>
    norm_num [scalarCorrelation, Fourier.RadixTrace.Valid, Fourier.CorrelationTrace.leftDFT,
      Fourier.CorrelationTrace.rightDFT, Fourier.RadixTrace.values, Fin.sum_univ_one]

example (j : ZMod (2 ^ 0)) :
    ‖(∑ _i : Fin 1, ZMod.cyclicCorrelation (fun _ => 3) (fun _ => 4) j) -
      scalarCorrelation.value j‖ ≤ 0 := by
  simpa [Fourier.CorrelationTrace.error, Fourier.CorrelationTrace.productError,
    Fourier.CorrelationTrace.leftError, Fourier.CorrelationTrace.rightError,
    scalarCorrelation, Fourier.RadixTrace.error] using
      scalarCorrelation_valid.norm_sum_correlation_sub_le j

example {n : ℕ} {t : Fourier.RadixTrace n} {q : Vector ℂ (2 ^ n)}
    (ht : t.Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) q)
    {a : ZMod (2 ^ n) → ℂ} {ε : ℝ}
    (ha : ∀ l, ‖a l - q[l.val]'(ZMod.val_lt l)‖ ≤ ε) (j : ZMod (2 ^ n)) :
    ‖((2 ^ n : ℕ) : ℂ)⁻¹ * ZMod.dft a (-j) -
      ((2 ^ n : ℕ) : ℂ)⁻¹ * t.values[j.val]'(ZMod.val_lt j)‖ ≤
      ε + t.error / (2 ^ n : ℕ) :=
  ht.norm_inv_dft_sub_le ha j
