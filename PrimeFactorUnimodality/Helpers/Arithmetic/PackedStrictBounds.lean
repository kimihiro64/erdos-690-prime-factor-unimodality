import Mathlib.Data.Rat.Cast.Order
import PrimeFactorUnimodality.Mathlib.Data.Nat.BitLaneCompare

/-! # Fixed-point separation bounds from one packed integer comparison

A positive common denominator and optional rational offset interpret packed
unsigned lanes as signed rational bounds. The integers are checked in bulk;
semantic enclosure premises connect them to the quantities being compared.
Independent chunks compose without replaying their arithmetic.
-/

namespace PrimeFactorUnimodality

/-- Two packed arrays with a common fixed-point interpretation and exact declared length. -/
structure PackedStrictBounds (n : ℕ) where
  width : ℕ
  lower : ℕ
  upper : ℕ
  denominator : ℕ
  offset : ℚ

namespace PackedStrictBounds

/-- Decode a lower bound; this is used in theorem statements, not the bulk check. -/
def lo {n : ℕ} (p : PackedStrictBounds n) (i : Fin n) : ℚ :=
  (Nat.bitLaneDigit p.width p.lower i.val : ℚ) / p.denominator + p.offset

/-- Decode the corresponding upper bound with the same denominator and offset. -/
def hi {n : ℕ} (p : PackedStrictBounds n) (i : Fin n) : ℚ :=
  (Nat.bitLaneDigit p.width p.upper i.val : ℚ) / p.denominator + p.offset

/-- Check the denominator, lane ranges and all strict inequalities by whole-integer operations. -/
def check {n : ℕ} (p : PackedStrictBounds n) : Bool :=
  decide (0 < p.denominator) && Nat.checkBitLaneLt p.width n p.lower p.upper

/-- The bulk Boolean proves every decoded fixed-point inequality. -/
theorem lt_of_check {n : ℕ} {p : PackedStrictBounds n} (h : p.check = true) (i : Fin n) :
    p.lo i < p.hi i := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  have hd : (0 : ℚ) < p.denominator := by exact_mod_cast h.1
  have hlt : (Nat.bitLaneDigit p.width p.lower i.val : ℚ) <
      Nat.bitLaneDigit p.width p.upper i.val := by
    exact_mod_cast Nat.bitLaneDigit_lt_of_check _ _ _ _ h.2 i.val i.isLt
  simpa only [lo, hi, add_comm] using add_lt_add_right (div_lt_div_of_pos_right hlt hd) p.offset

/-- These are proved enclosures of actual inputs, not claims trusted from generated data. -/
def Encloses {n : ℕ} (p : PackedStrictBounds n) (a b : Fin n → ℚ) : Prop :=
  (∀ i, a i ≤ p.lo i) ∧ (∀ i, p.hi i ≤ b i)

/-- Enclosed quantities inherit the certified strict separation. -/
theorem lt_of_encloses_check {n : ℕ} {p : PackedStrictBounds n} {a b : Fin n → ℚ}
    (hp : p.Encloses a b) (h : p.check = true) (i : Fin n) : a i < b i :=
  (hp.1 i).trans_lt ((lt_of_check h i).trans_le (hp.2 i))

/-- Independently checked chunks concatenate at the semantic level, without any repeated check. -/
theorem lt_append {n m : ℕ} {p : PackedStrictBounds n} {q : PackedStrictBounds m}
    (hp : p.check = true) (hq : q.check = true) (i : Fin (n + m)) :
    Fin.addCases (motive := fun _ => ℚ) p.lo q.lo i <
      Fin.addCases (motive := fun _ => ℚ) p.hi q.hi i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa using lt_of_check hp j
  · simpa using lt_of_check hq j

end PackedStrictBounds

end PrimeFactorUnimodality
