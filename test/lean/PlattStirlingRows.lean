import PrimeFactorUnimodality.Helpers.Analytic.PlattStirlingGrid

/-! Shared base samples, signed grid offsets, empty chunks and ordered chunk composition. -/

open Complex PrimeFactorUnimodality

example (t h v : ℝ) :
    plattWindowKernel 0 t h v =
      exp (gammaRightLog (plattKernelArgument t v) + (plattKernelLogShift t h v : ℂ)) := by
  simpa [plattKernelPower] using plattWindowKernel_eq_compensated_exp 0 t h v

example (v : ℝ) : ‖plattKernelPower 1 v‖ = 2 * Real.pi * |v| := by
  simpa using norm_plattKernelPower 1 v

example (t : ℝ) : plattGammaRadius t (-t) = 1 / 4 := by norm_num [plattGammaRadius]

example (B : ℚ) : plattRationalTimeOffset 1 B 0 = 0 := by
  simp [plattRationalTimeOffset]

example (B : ℚ) : plattRationalTimeOffset 8 B (-1) = -B / 8 := by
  norm_num [plattRationalTimeOffset, ZMod.valMinAbs]

example (c : PlattStirlingContext) (v : ℕ → ℚ) (rows : ℕ → PlattStirlingRow) :
    PlattStirlingRow.ValidRange c v rows 7 0 := PlattStirlingRow.validRange_zero c v rows 7

example {c : PlattStirlingContext} {v : ℕ → ℚ} {rows : ℕ → PlattStirlingRow}
    (h₁ : PlattStirlingRow.ValidRange c v rows 0 3)
    (h₂ : PlattStirlingRow.ValidRange c v rows 3 5) :
    PlattStirlingRow.ValidRange c v rows 0 8 := h₁.append h₂

example {c : PlattStirlingContext} (hc : c.Valid) {r : PlattStirlingRow} {v : ℚ}
    (hr : r.Valid c v) :
    ‖plattWindowKernel 0 c.center c.width v - r.value.toComplex‖ ≤
      plattStirlingInputError c.order c.center v (r.logInput c v).toComplex
        (r.logError c) r.expError := hr.norm_kernel_zero_sub_le hc
