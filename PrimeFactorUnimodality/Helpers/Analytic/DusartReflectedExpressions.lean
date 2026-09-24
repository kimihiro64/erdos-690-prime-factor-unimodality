import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenExpressions
import PrimeFactorUnimodality.Helpers.Analytic.DusartReflectedLogStable
import PrimeFactorUnimodality.Helpers.Analytic.DusartReflectedThetaRows

/-! # Exact expression semantics for reflected theta caps

Reuse the coefficient, positive square root and damped-tail expressions.
The zero-damping power term has its own root-free expression, avoiding a
logarithm at zero. Both complete branches include smoothing and root costs.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core DusartFrozenExpressions

namespace DusartReflectedExpressions

/-- The full scaled power tail has no square-root or zero-logarithm subexpression. -/
def powerTail (c : Expr) (q H : ℚ) : Expr :=
  let L := Expr.log (.const H)
  let B := Expr.mul (.const 2) (.namedConst .pi)
  let density := Expr.mul (.div (.exp (.add c (.mul (.const (1 - q)) L))) B)
    (.add (.div (.sub L (.log B)) (.const (q - 1))) (.const (1 / (q - 1) ^ 2)))
  let reciprocal := Expr.div (.exp (.sub c (.mul (.const q) L))) (.const q)
  let boundary := Expr.mul (.mul (.const 2) (.add L (.const 17)))
    (.exp (.sub c (.mul (.const q) L)))
  .mul (.const 2) (.add (.add density reciprocal) boundary)

/-- Both high contributions are scaled before evaluation and averaged exactly. -/
def average (m : ℕ) (s p H : ℚ) (b : Expr) : Expr :=
  let low := Expr.mul (.mul (.const (1 + (m + 3 : ℕ) * s))
    (.exp (.mul (.const (-(1 / 2 : ℚ))) b))) (.const 70)
  let high := scaledTail (coefficient m s) (.div b (.const 6)) (m + 4 : ℕ) p H
  let reflected := powerTail (.sub (coefficient m s) (.div b (.const 2))) (m + 4 : ℕ) H
  .add (.add low (.div (.add high reflected) (.const 2))) (.mul (.const 4) (.exp (.neg b)))

/-- One complete normalized theta branch, using the existing rational shift. -/
def moment (row : DusartFrozenThetaRow) (H : ℚ) (left : Bool) : Expr :=
  let t := shift row
  let base := if left then
      Expr.mul (.const t) (average row.orderOffset (row.step / t) row.power H
        (.add (.const row.lower) (.log (.const t))))
    else average row.orderOffset row.step row.power H (.const row.lower)
  let smoothing := Expr.const ((row.orderOffset + 3 : ℕ) * row.step / 2)
  let root := Expr.mul (.const (8 / 5)) (.exp (.const (-row.lower / 2)))
  .mul (.add (.add base smoothing) root) (.const (row.upper ^ 2))

/-- The complete real branch prior to taking the maximum. -/
noncomputable def branchValue (row : DusartFrozenThetaRow) (H : ℝ) (left : Bool) : ℝ :=
  let t : ℝ := shift row
  let base := if left then
      t * dusartReflectedLogAverage row.orderOffset ((row.step : ℝ) / t)
        (row.lower + Real.log t) row.power H
    else dusartReflectedLogAverage row.orderOffset row.step row.lower row.power H
  (base + (row.orderOffset + 3 : ℕ) * (row.step : ℝ) / 2 +
    (8 / 5) * Real.exp (-(row.lower : ℝ) / 2)) * (row.upper : ℝ) ^ 2

/-- The root-free expression is the exact zero-damping specialization. -/
theorem powerTail_eval (ρ : ℕ → ℝ) (c : Expr) (q H : ℚ) :
    Expr.eval ρ (powerTail c q H) =
      dusartFrozenScaledPeakTail (Expr.eval ρ c) 0 q q (Real.log H) := by
  simp [powerTail, Expr.sub, Expr.div, Expr.eval, MathConst.toReal,
    dusartFrozenScaledPeakTail, sub_eq_add_neg, div_eq_mul_inv]

/-- Stable scaling and expression evaluation recover the entire original reflected average. -/
theorem average_eval (ρ : ℕ → ℝ) (m : ℕ) (s p H : ℚ) (b : Expr)
    (hs : 0 < s) (hH : 0 < H) (hb : 0 < Expr.eval ρ b) (hp : p < (m + 4 : ℕ)) :
    Expr.eval ρ (average m s p H b) = dusartReflectedLogAverage m s (Expr.eval ρ b) p H := by
  rw [dusartReflectedLogAverage_eq_stable m (by exact_mod_cast hs) (by exact_mod_cast hH)]
  have hp' : (p : ℝ) < (m + 4 : ℕ) := by exact_mod_cast hp
  push_cast at hp'
  have hroot : 0 < Expr.eval ρ (.div b (.const 6)) * (((m + 4 : ℕ) : ℚ) - p : ℝ) := by
    simp only [Expr.div, Expr.eval, Rat.cast_ofNat]
    push_cast
    exact mul_pos (mul_pos hb (by norm_num)) (sub_pos.mpr hp')
  have ht := scaledTail_eval ρ (coefficient m s) (.div b (.const 6)) (m + 4 : ℕ) p H hroot
  simp only [Expr.div, Nat.cast_add, Nat.cast_ofNat] at ht
  simp [average, Expr.sub, Expr.div, Expr.eval, ht, powerTail_eval, coefficient_eval,
    dusartReflectedLogAverageStable, sub_eq_add_neg, div_eq_mul_inv]

/-- Shared row geometry proves every positivity premise in the two branch interpretations. -/
theorem moment_eval (ρ : ℕ → ℝ) (row : DusartFrozenThetaRow) (H : ℚ) (left : Bool)
    (hg : row.Geometry) (hH : 0 < H) :
    Expr.eval ρ (moment row H left) = branchValue row H left := by
  have ht : 0 < shift row := by unfold shift; linarith [hg.step_small]
  have hlo : (25 : ℝ) ≤ row.lower := by exact_mod_cast hg.lower_ge
  have hshift := (DusartFrozenThetaRow.shift_geometry hg.lower_ge hg.step_small).2
  rw [← shift_cast] at hshift
  have hr := average_eval ρ row.orderOffset row.step row.power H (.const row.lower)
    hg.step_pos hH (by simpa [Expr.eval] using (by linarith : (0 : ℝ) < row.lower)) hg.power_lt
  have hl := average_eval ρ row.orderOffset (row.step / shift row) row.power H
    (.add (.const row.lower) (.log (.const (shift row)))) (div_pos hg.step_pos ht) hH
    (by simpa [Expr.eval] using (by linarith : (0 : ℝ) < row.lower + Real.log (shift row))) hg.power_lt
  simp only [div_eq_mul_inv] at hl
  cases left <;> simp [moment, branchValue, Expr.eval, hr, hl, div_eq_mul_inv]

/-- Two branch bounds imply the exact reflected cap used by the analytic row theorem. -/
theorem cap_of_branches (row : DusartFrozenThetaRow) (H c : ℝ)
    (hl : branchValue row H true ≤ c) (hr : branchValue row H false ≤ c) :
    row.reflectedBudget H * (row.upper : ℝ) ^ 2 ≤ c := by
  simp only [branchValue, Bool.false_eq_true, ite_false, ite_true, shift_cast] at hl hr
  unfold DusartFrozenThetaRow.reflectedBudget dusartReflectedLogPsiBound
  dsimp only
  by_cases h : (1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ)) *
      dusartReflectedLogAverage row.orderOffset
        ((row.step : ℝ) / (1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ)))
        (row.lower + Real.log (1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ))) row.power H ≤
    dusartReflectedLogAverage row.orderOffset row.step row.lower row.power H
  · rw [max_eq_right h]
    exact hr
  · rw [max_eq_left (le_of_not_ge h)]
    exact hl

end DusartReflectedExpressions

end PrimeFactorUnimodality
