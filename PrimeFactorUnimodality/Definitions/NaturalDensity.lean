import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import PrimeFactorUnimodality.Mathlib.Data.Nat.Periodic

set_option autoImplicit false

/-!
# Natural density of predicates on the natural numbers

This module supplies the analytic endpoint for the exact periodic counts used
by the prime-factor problem.  The normalization counts witnesses in
`{0, ..., n - 1}`; changing finitely many initial values does not affect the
limit.
-/

open Filter Function
open scoped Topology

namespace PrimeFactorUnimodality

/-- A predicate has natural density `d` when its normalized initial-segment
counts converge to `d`. -/
def HasNaturalDensity (predicate : ℕ → Prop) [DecidablePred predicate]
    (density : ℝ) : Prop :=
  Tendsto (fun n => (Nat.count predicate n : ℝ) / (n : ℝ)) atTop (𝓝 density)

/-- Pointwise equivalent predicates have the same natural-density statement. -/
theorem HasNaturalDensity.congr {predicate predicate' : ℕ → Prop}
    [DecidablePred predicate] [DecidablePred predicate'] {density : ℝ}
    (has_density : HasNaturalDensity predicate density)
    (equivalent : ∀ n, predicate n ↔ predicate' n) :
    HasNaturalDensity predicate' density := by
  unfold HasNaturalDensity at has_density ⊢
  apply has_density.congr'
  exact .of_forall fun n => by
    change (Nat.count predicate n : ℝ) / (n : ℝ) =
      (Nat.count predicate' n : ℝ) / (n : ℝ)
    have count_equal : Nat.count predicate n = Nat.count predicate' n := by
      rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
      apply congrArg Finset.card
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      exact and_congr Iff.rfl (equivalent x)
    rw [count_equal]

/-- The natural density of a periodic predicate is its proportion in one
positive period. -/
theorem hasNaturalDensity_of_periodic {predicate : ℕ → Prop}
    [DecidablePred predicate] {period : ℕ} (period_pos : 0 < period)
    (periodic : Periodic predicate period) :
    HasNaturalDensity predicate
      ((Nat.count predicate period : ℝ) / (period : ℝ)) := by
  have remainder_tends_to_zero : Tendsto
      (fun n : ℕ => (Nat.count predicate (n % period) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
      (b := (0 : ℝ)) (B := (period : ℝ))
    · exact .of_forall fun n => by positivity
    · exact .of_forall fun n => by
        change (Nat.count predicate (n % period) : ℝ) ≤ (period : ℝ)
        exact_mod_cast (Nat.count_le (p := predicate)).trans
          (Nat.mod_lt n period_pos).le
    · exact tendsto_natCast_atTop_atTop
  have mod_div_tends_to_zero : Tendsto
      (fun n : ℕ => ((n % period : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
      (b := (0 : ℝ)) (B := (period : ℝ))
    · exact .of_forall fun n => by positivity
    · exact .of_forall fun n => by
        change ((n % period : ℕ) : ℝ) ≤ (period : ℝ)
        exact_mod_cast (Nat.mod_lt n period_pos).le
    · exact tendsto_natCast_atTop_atTop
  have complete_periods_tendsto_density : Tendsto
      (fun n : ℕ => ((Nat.count predicate period : ℝ) / (period : ℝ)) *
        (1 - ((n % period : ℕ) : ℝ) / (n : ℝ))) atTop
      (𝓝 ((Nat.count predicate period : ℝ) / (period : ℝ))) := by
    have constant_density : Tendsto
        (fun _ : ℕ => (Nat.count predicate period : ℝ) / (period : ℝ))
        atTop (nhds ((Nat.count predicate period : ℝ) / (period : ℝ))) :=
      tendsto_const_nhds
    have constant_one : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using constant_density.mul (constant_one.sub mod_div_tends_to_zero)
  unfold HasNaturalDensity
  have combined_limit : Tendsto
      (fun n : ℕ => (Nat.count predicate (n % period) : ℝ) / (n : ℝ) +
        ((Nat.count predicate period : ℝ) / (period : ℝ)) *
          (1 - ((n % period : ℕ) : ℝ) / (n : ℝ)))
      atTop (nhds ((Nat.count predicate period : ℝ) / (period : ℝ))) := by
    simpa using remainder_tends_to_zero.add complete_periods_tendsto_density
  apply combined_limit.congr'
  filter_upwards [eventually_gt_atTop 0] with n n_pos
  have count_decomposition := Nat.count_eq_mod_add_div_mul periodic n
  rw [count_decomposition]
  push_cast
  have division_algorithm :
      (period : ℝ) * ((n / period : ℕ) : ℝ) +
          ((n % period : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast (by
      simpa [add_comm] using n.mod_add_div period)
  field_simp [period_pos.ne', n_pos.ne']
  nlinarith

/-- Delete the value at zero from a predicate. -/
def WithoutZero (predicate : ℕ → Prop) (n : ℕ) : Prop :=
  n ≠ 0 ∧ predicate n

instance instDecidablePredWithoutZero (predicate : ℕ → Prop)
    [DecidablePred predicate] : DecidablePred (WithoutZero predicate) :=
  fun n => by
    unfold WithoutZero
    infer_instance

theorem count_withoutZero_succ {predicate : ℕ → Prop}
    [DecidablePred predicate] (n : ℕ) :
    Nat.count (WithoutZero predicate) (n + 1) + (if predicate 0 then 1 else 0) =
      Nat.count predicate (n + 1) := by
  rw [Nat.count_succ', Nat.count_succ']
  simp [WithoutZero]

/-- Removing the exceptional value at zero does not change natural density. -/
theorem HasNaturalDensity.withoutZero {predicate : ℕ → Prop}
    [DecidablePred predicate] {density : ℝ}
    (has_density : HasNaturalDensity predicate density) :
    HasNaturalDensity (WithoutZero predicate) density := by
  by_cases holds_at_zero : predicate 0
  · have correction_tends_to_zero : Tendsto
        (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_bdd_div_atTop_nhds_zero
        (.of_forall fun _ => by positivity)
        (.of_forall fun _ => le_rfl)
        tendsto_natCast_atTop_atTop
    unfold HasNaturalDensity at has_density ⊢
    have corrected_limit : Tendsto
        (fun n : ℕ => (Nat.count predicate n : ℝ) / (n : ℝ) -
          (1 : ℝ) / (n : ℝ)) atTop (nhds density) := by
      simpa using has_density.sub correction_tends_to_zero
    apply corrected_limit.congr'
    filter_upwards [eventually_gt_atTop 0] with n n_pos
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero n_pos.ne'
    rw [show m.succ = m + 1 by omega]
    have count_identity := count_withoutZero_succ (predicate := predicate) m
    simp only [holds_at_zero, ite_true] at count_identity
    have cast_identity :
        (Nat.count (WithoutZero predicate) (m + 1) : ℝ) + 1 =
          (Nat.count predicate (m + 1) : ℝ) := by
      exact_mod_cast count_identity
    rw [← cast_identity]
    field_simp
    ring
  · have predicates_equal : WithoutZero predicate = predicate := by
      funext n
      apply propext
      cases n with
      | zero => simp [WithoutZero, holds_at_zero]
      | succ n => simp [WithoutZero]
    simpa [predicates_equal] using has_density

end PrimeFactorUnimodality
