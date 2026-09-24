import PrimeFactorUnimodality.Helpers.Analytic.PlattRadixApproximation
import PrimeFactorUnimodality.Helpers.Analytic.PlattStirlingRowBounds

/-! # Complete compact-row coverage supplies the existing FFT input interface

Rows are indexed by the actual finite grid, including its signed central
offsets. One universal validity premise covers every index. The assembler
retains the row, power, multiplication, FFT and analytic alias errors.
-/

namespace PrimeFactorUnimodality

open Complex

/-- Exact rational offset of one point in the central time grid. -/
def plattRationalTimeOffset (N : ℕ) (B : ℚ) (i : ZMod N) : ℚ :=
  (i.valMinAbs : ℚ) * B / N

/-- Rational and analytic grid coordinates agree exactly. -/
theorem cast_plattRationalTimeOffset (N : ℕ) (B : ℚ) (i : ZMod N) :
    (plattRationalTimeOffset N B i : ℝ) = (i.valMinAbs : ℝ) * (B : ℝ) / N := by
  simp [plattRationalTimeOffset]

/-- Exact range coverage supplies every grid index, with no unchecked remainder. -/
theorem plattStirling_valid_grid_of_range {N : ℕ} [NeZero N] (B : ℚ)
    {c : PlattStirlingContext} {rows : ZMod N → PlattStirlingRow}
    (h : PlattStirlingRow.ValidRange c
      (fun i => plattRationalTimeOffset N B (i : ZMod N))
      (fun i => rows (i : ZMod N)) 0 N) :
    ∀ i, (rows i).Valid c (plattRationalTimeOffset N B i) := by
  intro i
  have hi := h i.val (Nat.zero_le _) (by simpa using ZMod.val_lt i)
  simpa only [ZMod.natCast_zmod_val] using hi

/-- Valid rows covering every index supply the exact input premise of the existing FFT theorem. -/
theorem norm_plattRadixApproximation_sub_le_of_stirling_rows
    (m k : ℕ) (hm : 1 ≤ m) {n : ℕ} {c : PlattStirlingContext} (hc : c.Valid)
    {B : ℚ} (hcenter : 0 ≤ c.center) (hwidth : 0 < c.width) (hB : 0 < B)
    (hk : 4 * (k : ℝ) * (c.width : ℝ) ^ 2 < (B : ℝ) ^ 2)
    (rows : ZMod (2 ^ n) → PlattStirlingRow)
    (hr : ∀ i, (rows i).Valid c (plattRationalTimeOffset (2 ^ n) B i))
    {p : ZMod (2 ^ n) → ℂ} {ν ρ : ZMod (2 ^ n) → ℝ}
    {q : Vector ℂ (2 ^ n)} {ε : ℝ} {t : Fourier.RadixTrace n}
    (hp : ∀ i, ‖plattKernelPower k (plattRationalTimeOffset (2 ^ n) B i) - p i‖ ≤ ν i)
    (hq : ∀ i, ‖(rows i).value.toComplex * p i - q[i.val]'(ZMod.val_lt i)‖ ≤ ρ i)
    (hbudget : ∀ i, plattStirlingInputError c.order c.center
      (plattRationalTimeOffset (2 ^ n) B i)
      ((rows i).logInput c (plattRationalTimeOffset (2 ^ n) B i)).toComplex
      ((rows i).logError c) (rows i).expError *
        (2 * Real.pi * |(plattRationalTimeOffset (2 ^ n) B i : ℝ)|) ^ k +
          ‖(rows i).value.toComplex‖ * ν i + ρ i ≤ ε)
    (ht : t.Valid (ZMod.stdAddChar (1 : ZMod (2 ^ n))) q) (j : ZMod (2 ^ n)) :
    ‖(((B : ℝ) / (2 ^ n : ℕ) : ℝ) : ℂ) * t.values[j.val]'(ZMod.val_lt j) -
        plattFrequencyGrid (2 ^ n) k c.center c.width B (-j)‖ ≤
      ((B : ℝ) / (2 ^ n : ℕ)) * t.error + (B : ℝ) * ε +
        (B : ℝ) * plattTimeAliasBound k c.width B +
          plattFourierAliasBound m k c.center c.width ((2 ^ n : ℕ) / (B : ℝ)) := by
  apply norm_plattRadixApproximation_sub_le m k hm (by exact_mod_cast hcenter)
    (by exact_mod_cast hwidth) (by exact_mod_cast hB) hk ?_ ht j
  intro i
  have h := ((hr i).norm_kernel_sub_le hc k (hp i) (hq i)).trans (hbudget i)
  rw [norm_sub_rev] at h
  simpa only [plattTimeGrid, cast_plattRationalTimeOffset] using h

end PrimeFactorUnimodality
