/-
Copyright (c) 2026 kimihiro64. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kimihiro64
-/
import Mathlib.Data.Nat.Periodic

set_option autoImplicit false

/-!
# Counting periodic predicates

Exact block and remainder formulas for `Nat.count`.  These are the finite
core needed to turn residue-class counts into natural-density limits.
-/

namespace Nat

open Function

/-- A periodic predicate has the same number of witnesses in every whole
number of periods. -/
theorem count_mul_period {p : ℕ → Prop} [DecidablePred p]
    {a : ℕ} (hp : Periodic p a) (q : ℕ) :
    Nat.count p (q * a) = q * Nat.count p a := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, Nat.count_add, ih, Nat.succ_mul]
      congr 1
      congr 1
      funext k
      exact propext (by
        simpa [Nat.nsmul_eq_mul, add_comm] using hp.nsmul q k)

/-- Split the count of a periodic predicate into complete periods and its
final incomplete period. -/
theorem count_eq_mod_add_div_mul {p : ℕ → Prop} [DecidablePred p]
    {a : ℕ} (hp : Periodic p a) (n : ℕ) :
    Nat.count p n = Nat.count p (n % a) + (n / a) * Nat.count p a := by
  calc
    Nat.count p n = Nat.count p (a * (n / a) + n % a) := by
      congr 1
      simpa [add_comm] using (n.mod_add_div a).symm
    _ = Nat.count p (a * (n / a)) +
        Nat.count (fun k => p (a * (n / a) + k)) (n % a) :=
      Nat.count_add _ _ _
    _ = (n / a) * Nat.count p a + Nat.count p (n % a) := by
      rw [show Nat.count p (a * (n / a)) = (n / a) * Nat.count p a by
        simpa [mul_comm] using Nat.count_mul_period hp (n / a)]
      congr 1
      unfold Nat.count
      apply List.countP_congr
      intro k hk
      have hprop : p (a * (n / a) + k) = p k := by
        simpa only [Nat.nsmul_eq_mul, mul_comm (n / a) a,
          add_comm k (a * (n / a))] using hp.nsmul (n / a) k
      simpa only [decide_eq_true_eq] using hprop.to_iff
    _ = Nat.count p (n % a) + (n / a) * Nat.count p a := add_comm _ _

end Nat
