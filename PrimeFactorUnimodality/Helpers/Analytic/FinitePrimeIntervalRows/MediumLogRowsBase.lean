import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Core
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.EndpointBounds

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Compact medium log-cubed row data

The finite Proposition 5.4(c) prefix stores only adjacent prime pairs.  The
scaled product and primality checks are fields of one datum, while the row
and chain assemblers below are shared by every generated band. -/

namespace PrimeFactorUnimodality

noncomputable section

def mediumLogSeedRow : FinitePrimeGapLogRow := by
  apply FinitePrimeGapLogRow.of_gap_row (g := 60)
    (row := {
      left := 89693
      right := 89752
      left_le_right := by norm_num
      witness := 89753
      witness_prime := by decide
      right_lt_witness := by norm_num
      witness_le_left_add_gap := by norm_num })
    (by norm_num) (L := (1141 : Real) / 100)
  · norm_num
  · exact log_89693_le_1141_over_100
  · norm_num

theorem mediumLogSeedChain :
    FinitePrimeGapLogRowsChain 89693 89752 [mediumLogSeedRow] := by
  apply FinitePrimeGapLogRowsChain.cons mediumLogSeedRow
  · norm_num
  · norm_num
  exact FinitePrimeGapLogRowsChain.empty (by norm_num)

def FinitePrimeGapLogRowsCoverUpTo
    (rows : List FinitePrimeGapLogRow) (X : Real) : Prop :=
  ∀ x : Real, (89693 : Real) ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧
      x < (row.right : Real) + 1

theorem finitePrimeGapLogRowsCoverUpTo_of_chain
    {b : Nat} {X : Real} {rows : List FinitePrimeGapLogRow}
    (chain : FinitePrimeGapLogRowsChain 89693 b rows)
    (hXb : X ≤ b) :
    FinitePrimeGapLogRowsCoverUpTo rows X := by
  intro x hx hX
  exact finitePrimeGapLogRowsCover_of_chain chain
    (by linarith [hX]) (by
      have hxb : x ≤ (b : Real) := hX.trans hXb
      exact lt_of_le_of_lt hxb (by norm_num))

theorem hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows
    {X : Real} {rows : List FinitePrimeGapLogRow}
    (cover : FinitePrimeGapLogRowsCoverUpTo rows X) :
    HasLogCubedShortIntervalPrimeBelow X := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  have hleft_large : (89693 : Real) ≤ (row.left : Real) := by
    exact_mod_cast row.left_large
  have hwidth : logCubedWidth (row.left : Real) ≤ logCubedWidth x := by
    exact logCubedWidth_monotoneOn (a := (row.left : Real)) (b := x)
      (by norm_num at hleft_large ⊢; linarith)
      (Set.mem_Ici.mpr (by norm_num at hleft_large ⊢; linarith)) hleft
  refine ⟨row.witness, row.witness_prime, ?_, ?_⟩
  · exact lt_of_lt_of_le hright (by exact_mod_cast row.right_lt_witness)
  · have hgap : (row.witness : Real) - x ≤ logCubedWidth x := by
      have hqleft : (row.witness : Real) - x ≤
          (row.witness : Real) - row.left := by linarith
      exact hqleft.trans (row.witness_width.trans hwidth)
    linarith

structure MediumLogDatum (lower upper Lnum Lden : Nat) where
  p : Nat
  q : Nat
  p_lower : lower ≤ p
  p_upper : p ≤ upper
  q_prime : q.Prime
  p_lt_q : p < q
  scaled_product : (q - p) * Lnum ^ 3 ≤ p * Lden ^ 3

def MediumLogDatumChain (a b : Nat)
    {lower upper Lnum Lden : Nat} :
    List (MediumLogDatum lower upper Lnum Lden) → Prop
  | [] => b < a
  | datum :: tail =>
      datum.p ≤ a ∧ datum.p < datum.q ∧
        MediumLogDatumChain datum.q b tail

theorem mediumLogRowsChain_of_data
    {a b lower upper Lnum Lden : Nat}
    {data : List (MediumLogDatum lower upper Lnum Lden)}
    (rowOf : MediumLogDatum lower upper Lnum Lden → FinitePrimeGapLogRow)
    (left_eq : ∀ datum, (rowOf datum).left = datum.p)
    (right_eq : ∀ datum, (rowOf datum).right + 1 = datum.q)
    (chain : MediumLogDatumChain a b data) :
    FinitePrimeGapLogRowsChain a b (data.map rowOf) := by
  induction data generalizing a b with
  | nil =>
      exact FinitePrimeGapLogRowsChain.empty chain
  | cons datum tail ih =>
      rcases chain with ⟨hleft, hlt, htail⟩
      simp only [List.map]
      apply FinitePrimeGapLogRowsChain.cons (rowOf datum)
      · rw [left_eq]
        exact hleft
      · rw [left_eq]
        have hq : (rowOf datum).right + 1 = datum.q := right_eq datum
        omega
      · apply ih
        rw [right_eq]
        exact htail

end

end PrimeFactorUnimodality
