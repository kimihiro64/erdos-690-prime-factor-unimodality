import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.High
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Low
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogRows
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingRows
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Assembly

set_option autoImplicit false

set_option maxRecDepth 100000

/-! # Shared finite row coverage for short prime intervals

The medium numerical part of the explicit interval theorem is naturally a
finite cover.  This module keeps the cover data separate from its consumer:
one row supplies one verified prime, and the cover theorem propagates that
prime to every real point in the row.  Thus a table of rows can be checked as
one list rather than as a collection of one-file witness replays. -/

namespace PrimeFactorUnimodality

noncomputable section

def finitePrimeGapLogRow_of_explicit_100000
    {p q : Nat} (hq : q.Prime) (hpq : p < q)
    (hproduct : (q - p : Real) * ((116 : Real) / 10) ^ 3 ≤ p)
    (hleft_large : 89693 ≤ p) (hp100000 : p ≤ 100000) :
    FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit hq hpq hleft_large
    (log_le_116_over_10_of_89693_le hleft_large hp100000)
    (by norm_num) hproduct

def finitePrimeGapLogRow_89693_89752 : FinitePrimeGapLogRow := by
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

def finitePrimeGapLogRow_89753_89758 : FinitePrimeGapLogRow := by
  apply FinitePrimeGapLogRow.of_gap_row (g := 6)
    (row := {
      left := 89753
      right := 89758
      left_le_right := by norm_num
      witness := 89759
      witness_prime := by decide
      right_lt_witness := by norm_num
      witness_le_left_add_gap := by norm_num })
    (by norm_num) (L := (116 : Real) / 10)
  · norm_num
  · exact log_le_116_over_10_of_89693_le (by norm_num) (by norm_num)
  · norm_num

def finitePrimeGapLogRow_89759_89766 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89759) (q := 89767)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89767_89778 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89767) (q := 89779)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89779_89782 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89779) (q := 89783)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89783_89796 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89783) (q := 89797)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89797_89808 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89797) (q := 89809)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89809_89818 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89809) (q := 89819)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89819_89820 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89819) (q := 89821)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89821_89832 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89821) (q := 89833)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89833_89838 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89833) (q := 89839)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89839_89848 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89839) (q := 89849)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89849_89866 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89849) (q := 89867)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRow_89867_89890 : FinitePrimeGapLogRow :=
  finitePrimeGapLogRow_of_explicit_100000 (p := 89867) (q := 89891)
    (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

def finitePrimeGapLogRows_89693_89752 :
    List FinitePrimeGapLogRow :=
  [finitePrimeGapLogRow_89693_89752]

theorem finitePrimeGapLogRows_89693_89752_cover :
    FinitePrimeGapLogRowsCoverUpTo
      finitePrimeGapLogRows_89693_89752 (89752 : Real) := by
  intro x hx hX
  refine ⟨finitePrimeGapLogRow_89693_89752, by simp, ?_, ?_⟩
  · norm_num
  · norm_num at ⊢
    linarith

def finitePrimeGapLogRows_89693_89758 :
    List FinitePrimeGapLogRow :=
  [finitePrimeGapLogRow_89693_89752,
    finitePrimeGapLogRow_89753_89758]

theorem finitePrimeGapLogRows_89693_89758_chain :
    FinitePrimeGapLogRowsChain 89693 89758
      finitePrimeGapLogRows_89693_89758 := by
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89693_89752
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89753_89758
  · norm_num
  · norm_num
  exact FinitePrimeGapLogRowsChain.empty (by norm_num)

theorem finitePrimeGapLogRows_89693_89758_cover :
    FinitePrimeGapLogRowsCoverUpTo
      finitePrimeGapLogRows_89693_89758 (89758 : Real) := by
  exact finitePrimeGapLogRowsCoverUpTo_of_chain
    finitePrimeGapLogRows_89693_89758_chain (by norm_num)

def finitePrimeGapLogRows_89693_89890 :
    List FinitePrimeGapLogRow :=
  [finitePrimeGapLogRow_89693_89752,
    finitePrimeGapLogRow_89753_89758,
    finitePrimeGapLogRow_89759_89766,
    finitePrimeGapLogRow_89767_89778,
    finitePrimeGapLogRow_89779_89782,
    finitePrimeGapLogRow_89783_89796,
    finitePrimeGapLogRow_89797_89808,
    finitePrimeGapLogRow_89809_89818,
    finitePrimeGapLogRow_89819_89820,
    finitePrimeGapLogRow_89821_89832,
    finitePrimeGapLogRow_89833_89838,
    finitePrimeGapLogRow_89839_89848,
    finitePrimeGapLogRow_89849_89866,
    finitePrimeGapLogRow_89867_89890]

theorem finitePrimeGapLogRows_89693_89890_chain :
    FinitePrimeGapLogRowsChain 89693 89890
      finitePrimeGapLogRows_89693_89890 := by
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89693_89752
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89753_89758
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89759_89766
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89767_89778
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89779_89782
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89783_89796
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89797_89808
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89809_89818
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89819_89820
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89821_89832
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89833_89838
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89839_89848
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89849_89866
  · norm_num
  · norm_num
  apply FinitePrimeGapLogRowsChain.cons
    finitePrimeGapLogRow_89867_89890
  · norm_num
  · norm_num
  exact FinitePrimeGapLogRowsChain.empty (by norm_num)

theorem finitePrimeGapLogRows_89693_89890_cover :
    FinitePrimeGapLogRowsCoverUpTo
      finitePrimeGapLogRows_89693_89890 (89890 : Real) := by
  exact finitePrimeGapLogRowsCoverUpTo_of_chain
    finitePrimeGapLogRows_89693_89890_chain (by norm_num)

theorem hasLogCubedShortIntervalPrimeBelow_89693_89752 :
    HasLogCubedShortIntervalPrimeBelow (89752 : Real) :=
  hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows
    finitePrimeGapLogRows_89693_89752_cover

theorem hasLogCubedShortIntervalPrimeBelow_89693_89758 :
    HasLogCubedShortIntervalPrimeBelow (89758 : Real) :=
  hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows
    finitePrimeGapLogRows_89693_89758_cover

theorem hasLogCubedShortIntervalPrimeBelow_89693_89890 :
    HasLogCubedShortIntervalPrimeBelow (89890 : Real) :=
  hasLogCubedShortIntervalPrimeBelow_of_finite_gap_log_rows
    finitePrimeGapLogRows_89693_89890_cover

theorem hasLogCubedShortIntervalPrime_of_rows
    (upper_mono : ∀ {a b : Real}, 89693 ≤ a → a ≤ b →
      logCubedUpper a ≤ logCubedUpper b)
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCover rows) :
    HasLogCubedShortIntervalPrime := by
  intro x x_large
  obtain ⟨row, row_mem, left_mem, right_mem⟩ := cover x x_large
  exact logCubedPrimeRow_provides upper_mono row left_mem right_mem

theorem hasLogCubedShortIntervalPrime_of_rows_closed
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCover rows) :
    HasLogCubedShortIntervalPrime := by
  refine hasLogCubedShortIntervalPrime_of_rows ?_ cover
  intro a b ha hab
  exact logCubedUpper_monotoneOn (by norm_num at ⊢; linarith)
    (by norm_num at ⊢; linarith) hab

theorem hasLogCubedShortIntervalPrimeBelow_of_rows
    {X : Real} {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows X) :
    HasLogCubedShortIntervalPrimeBelow X := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  exact logCubedPrimeRow_provides
    (fun {a b} ha hab => logCubedUpper_monotoneOn
      (by norm_num at ⊢; linarith)
      (by norm_num at ⊢; linarith) hab)
    row hleft hright

theorem hasLogCubedShortIntervalPrime_of_bounded_rows_and_large_x
    {rows : List LogCubedPrimeRow}
    (X : Real) (hX : (4e18 : Real) ≤ X)
    (cover : LogCubedPrimeRowsCoverUpTo rows X)
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    HasLogCubedShortIntervalPrime := by
  intro x hx
  by_cases hsmall : x ≤ X
  · obtain ⟨row, row_mem, left_mem, right_mem⟩ := cover x hx hsmall
    exact logCubedPrimeRow_provides
      (fun {a b} ha hab => logCubedUpper_monotoneOn (by norm_num at ⊢; linarith)
        (by norm_num at ⊢; linarith) hab)
      row left_mem right_mem
  · exact large_x_logCubedShortIntervalPrime thetaError x
      (hX.trans (le_of_lt (lt_of_not_ge hsmall)))

theorem hasLogCubedShortIntervalPrime_of_rows_at_large_cutoff
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    HasLogCubedShortIntervalPrime :=
  hasLogCubedShortIntervalPrime_of_bounded_rows_and_large_x
    (4e18 : Real) le_rfl cover thetaError

theorem hasDusartShortIntervalPrime_of_rows_and_thetaError
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    HasDusartShortIntervalPrime := by
  exact hasDusartShortIntervalPrime_of_below_and_logCubed
    (hasDusartShortIntervalPrimeBelow_of_rows dusartCover)
    (hasLogCubedShortIntervalPrime_of_rows_at_large_cutoff logCover thetaError)

end

end PrimeFactorUnimodality
