import LeanCert.Core.Expr
import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenLogStable
import PrimeFactorUnimodality.Helpers.Analytic.DusartFrozenThetaRows

/-! # Shared expression semantics for frozen theta rows

Rational row parameters construct two closed expressions. Each includes one
adjacent average, the smoothing loss and the sharper root correction, scaled
by the upper logarithmic endpoint. The scaled high tail avoids premature
rounding of a tiny intermediate value. Both branches are interpreted by the
same semantic proof before any numerical checker is invoked.
The positive square root uses an exact log-exponential representation,
avoiding the dyadic backend's coarse square-root enclosure.
-/

namespace PrimeFactorUnimodality

open LeanCert.Core

namespace DusartFrozenExpressions

/-- A positive square root in a form admitting a sharp logarithmic enclosure. -/
def positiveRoot (e : Expr) : Expr := .exp (.mul (.const (1 / 2)) (.log e))

/-- Positivity justifies the log-exponential representation of the square root. -/
theorem positiveRoot_eval (ρ : ℕ → ℝ) (e : Expr) (he : 0 < Expr.eval ρ e) :
    Expr.eval ρ (positiveRoot e) = Real.sqrt (Expr.eval ρ e) := by
  simp [positiveRoot, Expr.eval, Real.sqrt_eq_rpow, Real.rpow_def_of_pos he, mul_comm]

/-- Reify the logarithm of the complete smoothing coefficient. -/
def coefficient (m : ℕ) (s : ℚ) : Expr :=
  .sub (.add (.mul (.const (m + 3 : ℕ)) (.log (.const 2)))
    (.mul (.const (m + 4 : ℕ)) (.log (.const (1 + (m + 3 : ℕ) * s)))))
    (.mul (.const (m + 3 : ℕ)) (.log (.const s)))

/-- Reify all three contributions to the scaled tail. -/
def scaledTail (c a : Expr) (q p H : ℚ) : Expr :=
  let L := Expr.log (.const H)
  let B := Expr.mul (.const 2) (.namedConst .pi)
  let peak := Expr.sub c (.mul (.const 2) (positiveRoot (.mul a (.const (q - p)))))
  let density := Expr.mul
    (.div (.exp (.add peak (.mul (.const (1 - p)) L))) B)
    (.add (.div (.sub L (.log B)) (.const (p - 1))) (.const (1 / (p - 1) ^ 2)))
  let reciprocal := Expr.div (.exp (.sub peak (.mul (.const p) L))) (.const p)
  let boundary := Expr.mul (.mul (.const 2) (.add L (.const 17)))
    (.exp (.sub (.sub c (.mul (.const q) L)) (.div a L)))
  .mul (.const 2) (.add (.add density reciprocal) boundary)

/-- One closed normalized average, parameterized by its logarithmic reference expression. -/
def average (m : ℕ) (s p H : ℚ) (b : Expr) : Expr :=
  let low := Expr.mul (.mul (.const (1 + (m + 3 : ℕ) * s))
    (.exp (.mul (.const (-(1 / 2 : ℚ))) b))) (.const 70)
  let high := scaledTail (coefficient m s) (.div b (.const 6)) (m + 4 : ℕ) p H
  .add (.add low high) (.mul (.const 4) (.exp (.neg b)))

/-- The exact rational lower-reference rescaling. -/
def shift (row : DusartFrozenThetaRow) : ℚ := 1 - (row.orderOffset + 3 : ℕ) * row.step

/-- One full normalized theta branch; the maximum is handled by two separate checks. -/
def moment (row : DusartFrozenThetaRow) (H : ℚ) (left : Bool) : Expr :=
  let t := shift row
  let base := if left then
      Expr.mul (.const t) (average row.orderOffset (row.step / t) row.power H
        (.add (.const row.lower) (.log (.const t))))
    else average row.orderOffset row.step row.power H (.const row.lower)
  let smoothing := Expr.const ((row.orderOffset + 3 : ℕ) * row.step / 2)
  let root := Expr.mul (.const (8 / 5)) (.exp (.const (-row.lower / 2)))
  .mul (.add (.add base smoothing) root) (.const (row.upper ^ 2))

/-- The real branch whose upper bound is required, before taking the maximum. -/
noncomputable def branchValue (row : DusartFrozenThetaRow) (H : ℝ) (left : Bool) : ℝ :=
  let t : ℝ := shift row
  let base := if left then
      t * dusartFrozenLogAverage row.orderOffset ((row.step : ℝ) / t)
        (row.lower + Real.log t) row.power H
    else dusartFrozenLogAverage row.orderOffset row.step row.lower row.power H
  (base + (row.orderOffset + 3 : ℕ) * (row.step : ℝ) / 2 +
    (8 / 5) * Real.exp (-(row.lower : ℝ) / 2)) * (row.upper : ℝ) ^ 2

/-- Rational precomputation preserves the real coefficient logarithm exactly. -/
theorem coefficient_eval (ρ : ℕ → ℝ) (m : ℕ) (s : ℚ) :
    Expr.eval ρ (coefficient m s) = dusartFrozenLogCoefficient m s := by
  simp [coefficient, Expr.sub, Expr.eval, dusartFrozenLogCoefficient, sub_eq_add_neg]

/-- The tail expression retains the density, reciprocal and endpoint terms. -/
theorem scaledTail_eval (ρ : ℕ → ℝ) (c a : Expr) (q p H : ℚ)
    (hroot : 0 < Expr.eval ρ a * ((q : ℝ) - p)) :
    Expr.eval ρ (scaledTail c a q p H) =
      dusartFrozenScaledPeakTail (Expr.eval ρ c) (Expr.eval ρ a) q p (Real.log H) := by
  have he := positiveRoot_eval ρ (.mul a (.const (q - p)))
    (by simpa [Expr.eval] using hroot)
  simp only [sub_eq_add_neg] at he
  simp [scaledTail, Expr.sub, Expr.div, Expr.eval, he, MathConst.toReal,
    dusartFrozenScaledPeakTail, sub_eq_add_neg, div_eq_mul_inv]

/-- A positive rational step lets the stable expression recover the original average. -/
theorem average_eval (ρ : ℕ → ℝ) (m : ℕ) (s p H : ℚ) (b : Expr) (hs : 0 < s)
    (hb : 0 < Expr.eval ρ b) (hp : p < (m + 4 : ℕ)) :
    Expr.eval ρ (average m s p H b) = dusartFrozenLogAverage m s (Expr.eval ρ b) p H := by
  rw [dusartFrozenLogAverage_eq_stable m (by exact_mod_cast hs)]
  have hp' : (p : ℝ) < (m + 4 : ℕ) := by exact_mod_cast hp
  push_cast at hp'
  have hroot : 0 < Expr.eval ρ (.div b (.const 6)) * (((m + 4 : ℕ) : ℚ) - p : ℝ) := by
    simp only [Expr.div, Expr.eval, Rat.cast_ofNat]
    push_cast
    exact mul_pos (mul_pos hb (by norm_num)) (sub_pos.mpr hp')
  have ht := scaledTail_eval ρ (coefficient m s) (.div b (.const 6)) (m + 4 : ℕ) p H hroot
  simp only [Expr.div, Nat.cast_add, Nat.cast_ofNat] at ht
  simp [average, Expr.div, Expr.eval, ht, coefficient_eval,
    dusartFrozenLogAverageStable, div_eq_mul_inv]

/-- The rational shift is the same shift used in the analytic two-average bound. -/
theorem shift_cast (row : DusartFrozenThetaRow) :
    (shift row : ℝ) = 1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ) := by
  simp [shift]

/-- Each closed expression evaluates to its full branch, including the upper-log square. -/
theorem moment_eval (ρ : ℕ → ℝ) (row : DusartFrozenThetaRow) (H : ℚ) (left : Bool)
    (hlo : 25 ≤ row.lower) (hs : 0 < row.step)
    (hstep : (row.orderOffset + 3 : ℕ) * row.step ≤ (1 / 2 : ℚ))
    (hp : row.power < (row.orderOffset + 4 : ℕ)) :
    Expr.eval ρ (moment row H left) = branchValue row H left := by
  have ht : 0 < shift row := by unfold shift; linarith
  have hlo' : (25 : ℝ) ≤ row.lower := by exact_mod_cast hlo
  have hshift := (DusartFrozenThetaRow.shift_geometry hlo hstep).2
  rw [← shift_cast] at hshift
  have hr := average_eval ρ row.orderOffset row.step row.power H (.const row.lower) hs
    (by simpa [Expr.eval] using (by linarith : (0 : ℝ) < row.lower)) hp
  have hl := average_eval ρ row.orderOffset (row.step / shift row) row.power H
    (.add (.const row.lower) (.log (.const (shift row)))) (div_pos hs ht)
    (by simpa [Expr.eval] using (by linarith : (0 : ℝ) < row.lower + Real.log (shift row))) hp
  simp only [div_eq_mul_inv] at hl
  cases left <;> simp [moment, branchValue, Expr.eval, hr, hl, div_eq_mul_inv]

/-- Bounds on both branches control the exact maximum in the row validity predicate. -/
theorem cap_of_branches (row : DusartFrozenThetaRow) (H c : ℝ)
    (hl : branchValue row H true ≤ c) (hr : branchValue row H false ≤ c) :
    row.budget H * (row.upper : ℝ) ^ 2 ≤ c := by
  simp only [branchValue, Bool.false_eq_true, ite_false, ite_true, shift_cast] at hl hr
  unfold DusartFrozenThetaRow.budget dusartFrozenLogPsiBound
  dsimp only
  by_cases h : (1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ)) *
      dusartFrozenLogAverage row.orderOffset
        ((row.step : ℝ) / (1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ)))
        (row.lower + Real.log (1 - (row.orderOffset + 3 : ℕ) * (row.step : ℝ))) row.power H ≤
    dusartFrozenLogAverage row.orderOffset row.step row.lower row.power H
  · rw [max_eq_right h]
    exact hr
  · rw [max_eq_left (le_of_not_ge h)]
    exact hl

end DusartFrozenExpressions

end PrimeFactorUnimodality
