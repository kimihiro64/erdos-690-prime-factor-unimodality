import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Core
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.EndpointBounds
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.High
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Low
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.MediumLogRows
import PrimeFactorUnimodality.Helpers.Analytic.MediumPNT
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime
import PrimeFactorUnimodality.Helpers.Analytic.ThetaFromPsi

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

structure DusartThetaBoundsRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  upper : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    Chebyshev.theta x - x < x / 36260
  lower : ∀ x : Real, 2 < x → (left : Real) ≤ x → x ≤ right →
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x

structure DusartThetaEndpointRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  theta_lower : Real
  theta_upper : Real
  theta_lower_le : theta_lower ≤ Chebyshev.theta left
  theta_right_le : Chebyshev.theta right ≤ theta_upper
  upper_error : theta_upper - left < (left : Real) / 36260
  lower_upper_error : theta_upper - left <
    (12323 / 10000 : Real) * (left : Real) / Real.log right
  lower_lower_error : right - theta_lower <
    (12323 / 10000 : Real) * (left : Real) / Real.log right

/-! Compact rows for the strict finite prefix used in Schoenfeld's theta
estimate.  They intentionally carry only the upper endpoint information;
the published relaxed error budget is assembled separately. -/
structure StrictThetaUpperRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  theta_upper : Real
  theta_right_le : Chebyshev.theta right ≤ theta_upper
  upper_error : theta_upper - left < 0

def strictThetaUpperRow_singleton (n : Nat) (hn : 2 ≤ n)
    (hupper : Chebyshev.theta n < n) : StrictThetaUpperRow :=
  { left := n
    right := n
    left_large := hn
    left_le_right := le_rfl
    theta_upper := Chebyshev.theta n
    theta_right_le := le_rfl
    upper_error := by simpa using hupper }

def StrictThetaUpperRowsCoverUpTo
    (rows : List StrictThetaUpperRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem strictThetaUpperRow_provides
    (row : StrictThetaUpperRow) {x : Real}
    (hleft : (row.left : Real) ≤ x) (hright : x ≤ row.right) :
    Chebyshev.theta x < x := by
  have htheta : Chebyshev.theta x ≤ row.theta_upper :=
    (Chebyshev.theta_mono hright).trans row.theta_right_le
  have hleft_pos : 0 ≤ (row.left : Real) := by positivity
  linarith

theorem hasStrictThetaUpperBelow_of_rows
    {X : Real} {rows : List StrictThetaUpperRow}
    (cover : StrictThetaUpperRowsCoverUpTo rows X) :
    HasStrictThetaUpperBelow X := by
  intro x hx hX
  by_cases hsmall : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
    linarith
  · obtain ⟨row, hrow, hleft, hright⟩ := cover x (le_of_not_gt hsmall) hX
    exact strictThetaUpperRow_provides row hleft hright

def StrictThetaUpperIndexedCoverUpTo
    {n : Nat} (rows : Fin n → StrictThetaUpperRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ i : Fin n, ((rows i).left : Real) ≤ x ∧ x ≤ (rows i).right

theorem hasStrictThetaUpperBelow_of_indexed_rows
    {n : Nat} {rows : Fin n → StrictThetaUpperRow} {X : Real}
    (cover : StrictThetaUpperIndexedCoverUpTo rows X) :
    HasStrictThetaUpperBelow X := by
  intro x hx hX
  by_cases hsmall : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
    linarith
  · obtain ⟨i, hleft, hright⟩ := cover x (le_of_not_gt hsmall) hX
    exact strictThetaUpperRow_provides (rows i) hleft hright

theorem hasDusartSymmetricThetaBoundsBelow_of_strict_rows_and_lower
    {X : Real} {rows : List StrictThetaUpperRow}
    (cover : StrictThetaUpperRowsCoverUpTo rows X)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x) :
    HasDusartSymmetricThetaBoundsBelow X := by
  exact hasDusartSymmetricThetaBoundsBelow_of_strict_theta_prefix
    (hasStrictThetaUpperBelow_of_rows cover) lower

/-! The certificate-facing form of the preceding assembly.  Keeping the
strict-prefix rows indexed avoids converting a compact generated table into a
large list merely to feed the analytic boundary. -/
theorem hasDusartSymmetricThetaBoundsBelow_of_indexed_strict_rows_and_lower
    {X : Real} {n : Nat} {rows : Fin n → StrictThetaUpperRow}
    (cover : StrictThetaUpperIndexedCoverUpTo rows X)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x) :
    HasDusartSymmetricThetaBoundsBelow X := by
  exact hasDusartSymmetricThetaBoundsBelow_of_strict_theta_prefix
    (hasStrictThetaUpperBelow_of_indexed_rows cover) lower

theorem theta_two_eq_log_two : Chebyshev.theta (2 : Real) = Real.log 2 := by
  have hprimes : Nat.primesLE 2 = {2} := by decide
  have hsum := Chebyshev.theta_eq_sum_primesLE_log 2
  rw [hprimes] at hsum
  simpa using hsum

/-! A singleton endpoint row is only sound when its three numerical endpoint
inequalities have already been proved.  Keeping those inequalities explicit
prevents a singleton constructor from being mistaken for a proof of a
nontrivial theta estimate. -/
def dusartThetaEndpointRow_two : DusartThetaEndpointRow :=
  { left := 2
    right := 2
    left_large := by norm_num
    left_le_right := by norm_num
    theta_lower := Chebyshev.theta 2
    theta_upper := Chebyshev.theta 2
    theta_lower_le := le_rfl
    theta_right_le := le_rfl
    upper_error := by
      have hlog : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
      rw [theta_two_eq_log_two]
      norm_num
      nlinarith [Real.log_two_lt_d9]
    lower_upper_error := by
      have hlog : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
      rw [theta_two_eq_log_two]
      norm_num
      have hpos : 0 < (12323 / 5000 : Real) / Real.log 2 :=
        div_pos (by norm_num) hlog
      nlinarith [Real.log_two_lt_d9]
    lower_lower_error := by
      have hlog : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
      rw [theta_two_eq_log_two]
      norm_num
      have hlt : Real.log 2 < 1 := by
        nlinarith [Real.log_two_lt_d9]
      have hquot : (2 : Real) < (12323 / 5000 : Real) / Real.log 2 := by
        apply (lt_div_iff₀ hlog).2
        nlinarith
      nlinarith }

def dusartThetaEndpointRow_singleton (n : Nat) (hn : 2 ≤ n)
    (hupper : Chebyshev.theta n - n < (n : Real) / 36260)
    (hlower_upper : Chebyshev.theta n - n <
      (12323 / 10000 : Real) * (n : Real) / Real.log n)
    (hlower_lower : (n : Real) - Chebyshev.theta n <
      (12323 / 10000 : Real) * (n : Real) / Real.log n) :
    DusartThetaEndpointRow :=
  { left := n
    right := n
    left_large := hn
    left_le_right := le_rfl
    theta_lower := Chebyshev.theta n
    theta_upper := Chebyshev.theta n
    theta_lower_le := le_rfl
    theta_right_le := le_rfl
    upper_error := hupper
    lower_upper_error := hlower_upper
    lower_lower_error := hlower_lower }

def DusartThetaEndpointRowsCoverUpTo
    (rows : List DusartThetaEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

/-! Endpoint rows are only used after the finite theta prefix.  Requiring
them to cover from `2` would be false: the endpoint error budgets are the
large-`x` Dusart budgets, not a small-`x` theta estimate. -/
def DusartThetaEndpointRowsCoverFrom
    (rows : List DusartThetaEndpointRow) (x₀ X : Real) : Prop :=
  ∀ x : Real, x₀ ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem dusartThetaEndpointRow_two_cover :
    DusartThetaEndpointRowsCoverUpTo [dusartThetaEndpointRow_two] 2 := by
  intro x hx hX
  have hx2 : x = 2 := by linarith
  subst x
  exact ⟨dusartThetaEndpointRow_two, by simp, by norm_num, by norm_num⟩

theorem dusartThetaEndpointRow_singleton_cover (n : Nat) (hn : 2 ≤ n)
    (hupper : Chebyshev.theta n - n < (n : Real) / 36260)
    (hlower_upper : Chebyshev.theta n - n <
      (12323 / 10000 : Real) * (n : Real) / Real.log n)
    (hlower_lower : (n : Real) - Chebyshev.theta n <
      (12323 / 10000 : Real) * (n : Real) / Real.log n) :
    DusartThetaEndpointRowsCoverFrom
      [dusartThetaEndpointRow_singleton n hn hupper hlower_upper hlower_lower] n n := by
  intro x hx hX
  have hxN : x = n := by exact_mod_cast le_antisymm hX hx
  subst x
  exact ⟨dusartThetaEndpointRow_singleton n hn hupper hlower_upper hlower_lower,
    by simp, by norm_num, by norm_num⟩

def DusartThetaEndpointIndexedCoverUpTo {n : Nat}
    (rows : Fin n → DusartThetaEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

def DusartThetaEndpointIndexedCoverFrom {n : Nat}
    (rows : Fin n → DusartThetaEndpointRow) (x₀ X : Real) : Prop :=
  ∀ x : Real, x₀ ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem dusartThetaEndpointIndexedCover_of_list
    {X : Real} {rows : List DusartThetaEndpointRow}
    (cover : DusartThetaEndpointRowsCoverUpTo rows X) :
    DusartThetaEndpointIndexedCoverUpTo
      (fun i : Fin rows.length => rows.get i) X := by
  exact indexed_interval_cover_of_list_cover rows
      (fun row => row.left) (fun row => row.right) cover

theorem dusartThetaEndpointIndexedCoverFrom_of_list
    {x₀ X : Real} {rows : List DusartThetaEndpointRow}
    (cover : DusartThetaEndpointRowsCoverFrom rows x₀ X) :
    DusartThetaEndpointIndexedCoverFrom
      (fun i : Fin rows.length => rows.get i) x₀ X := by
  exact indexed_interval_cover_of_list_cover rows
    (fun row => row.left) (fun row => row.right) cover

theorem dusartThetaEndpointIndexedCoverUpTo_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → DusartThetaEndpointRow}
    {right : Fin n₂ → DusartThetaEndpointRow}
    (hleft : DusartThetaEndpointIndexedCoverUpTo left m)
    (hright : DusartThetaEndpointIndexedCoverUpTo right X) :
    DusartThetaEndpointIndexedCoverUpTo (Fin.append left right) X := by
  intro x hx hX
  exact indexed_interval_cover_append left right
    (fun row => row.left) (fun row => row.right)
    (fun y hy _ hym => hleft y hy hym)
    (fun y hy _ hym hyX => hright y hy hyX)
    x hx trivial hX

theorem dusartThetaEndpointIndexedCoverFrom_append
    {x₀ m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → DusartThetaEndpointRow}
    {right : Fin n₂ → DusartThetaEndpointRow}
    (hleft : DusartThetaEndpointIndexedCoverFrom left x₀ m)
    (hright : DusartThetaEndpointIndexedCoverFrom right m X) :
    DusartThetaEndpointIndexedCoverFrom (Fin.append left right) x₀ X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨i, hleft_lower, hleft_upper⟩ := hleft x hx hxm
    refine ⟨Fin.castAdd n₂ i, ?_⟩
    simpa [Fin.append_left] using And.intro hleft_lower hleft_upper
  · obtain ⟨i, hright_lower, hright_upper⟩ :=
      hright x (le_of_not_ge hxm) hX
    refine ⟨Fin.natAdd n₁ i, ?_⟩
    simpa [Fin.append_right] using And.intro hright_lower hright_upper

theorem hasDusartSymmetricThetaBoundsBelow_of_indexed_endpoint_rows
    {n : Nat} {X : Real}
    {rows : Fin n → DusartThetaEndpointRow}
    (cover : DusartThetaEndpointIndexedCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      nlinarith
    · obtain ⟨i, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact (dusartThetaEndpointRow_provides (rows i) hleft hright).upper
        x hleft hright
  · intro x hx hX
    obtain ⟨i, hleft, hright⟩ := cover x (by linarith) hX
    exact (dusartThetaEndpointRow_provides (rows i) hleft hright).lower
      x hx hleft hright

theorem dusartThetaEndpointRowsCoverUpTo_append
    {m X : Real} {left right : List DusartThetaEndpointRow}
    (hleft : DusartThetaEndpointRowsCoverUpTo left m)
    (hright : DusartThetaEndpointRowsCoverUpTo right X) :
    DusartThetaEndpointRowsCoverUpTo (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem dusartThetaEndpointRowsCoverFrom_append
    {x₀ m X : Real} {left right : List DusartThetaEndpointRow}
    (hleft : DusartThetaEndpointRowsCoverFrom left x₀ m)
    (hright : DusartThetaEndpointRowsCoverFrom right m X) :
    DusartThetaEndpointRowsCoverFrom (left ++ right) x₀ X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ :=
      hright x (le_of_not_ge hxm) hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem dusartThetaEndpointRow_provides
    (row : DusartThetaEndpointRow) {x : Real}
    (hleft : (row.left : Real) ≤ x) (hright : x ≤ row.right) :
    DusartThetaBoundsRow := by
  have hleft2 : (2 : Real) ≤ row.left := by exact_mod_cast row.left_large
  have hright2 : (2 : Real) ≤ (row.right : Real) := by
    exact le_trans hleft2 (by exact_mod_cast row.left_le_right)
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith [hleft2, hleft])
  have hlogr_pos : 0 < Real.log (row.right : Real) := Real.log_pos (by linarith)
  have htheta_lower : row.theta_lower ≤ Chebyshev.theta x :=
    row.theta_lower_le.trans (Chebyshev.theta_mono hleft)
  have htheta_upper : Chebyshev.theta x ≤ row.theta_upper :=
    (Chebyshev.theta_mono hright).trans row.theta_right_le
  have hlog_mono : Real.log x ≤ Real.log (row.right : Real) :=
    Real.log_le_log (by linarith) hright
  have hratio : (row.left : Real) / Real.log (row.right : Real) ≤
      x / Real.log x := by
    apply (div_le_div_iff₀ hlogr_pos hlogx_pos).2
    calc
      (row.left : Real) * Real.log x ≤
          (row.left : Real) * Real.log (row.right : Real) :=
        mul_le_mul_of_nonneg_left hlog_mono (by positivity)
      _ ≤ x * Real.log (row.right : Real) :=
        mul_le_mul_of_nonneg_right hleft (by positivity)
  refine {
    left := row.left
    right := row.right
    left_large := row.left_large
    left_le_right := row.left_le_right
    upper := ?_
    lower := ?_
  }
  · intro y hyl hyr
    have htheta_y_upper : Chebyshev.theta y ≤ row.theta_upper :=
      (Chebyshev.theta_mono hyr).trans row.theta_right_le
    have hleft_y : (row.left : Real) ≤ y := hyl
    calc
      Chebyshev.theta y - y ≤ row.theta_upper - row.left := by linarith
      _ < (row.left : Real) / 36260 := row.upper_error
      _ ≤ y / 36260 := by
        exact div_le_div_of_nonneg_right hleft_y (by norm_num)
  · intro y hy2 hyl hyr
    have htheta_y_lower : row.theta_lower ≤ Chebyshev.theta y :=
      row.theta_lower_le.trans (Chebyshev.theta_mono hyl)
    have htheta_y_upper : Chebyshev.theta y ≤ row.theta_upper :=
      (Chebyshev.theta_mono hyr).trans row.theta_right_le
    have hylog_pos : 0 < Real.log y := Real.log_pos (by linarith)
    have hratio_y : (row.left : Real) / Real.log (row.right : Real) ≤
        y / Real.log y := by
      apply (div_le_div_iff₀ hlogr_pos hylog_pos).2
      calc
        (row.left : Real) * Real.log y ≤
            (row.left : Real) * Real.log (row.right : Real) :=
          mul_le_mul_of_nonneg_left
            (Real.log_le_log (by linarith) hyr) (by positivity)
        _ ≤ y * Real.log (row.right : Real) :=
          mul_le_mul_of_nonneg_right hyl (by positivity)
    have hupper : Chebyshev.theta y - y <
        (12323 / 10000 : Real) * y / Real.log y := by
      calc
        Chebyshev.theta y - y ≤ row.theta_upper - row.left := by linarith
        _ < (12323 / 10000 : Real) * (row.left : Real) /
            Real.log (row.right : Real) := row.lower_upper_error
        _ ≤ (12323 / 10000 : Real) * y / Real.log y := by
          exact mul_le_mul_of_nonneg_left hratio_y (by norm_num)
    have hlower : -(12323 / 10000 : Real) * y / Real.log y <
        Chebyshev.theta y - y := by
      have hdiff : y - Chebyshev.theta y <
          (12323 / 10000 : Real) * y / Real.log y := by
        calc
          y - Chebyshev.theta y ≤ row.right - row.theta_lower := by linarith
          _ < (12323 / 10000 : Real) * (row.left : Real) /
              Real.log (row.right : Real) := row.lower_lower_error
          _ ≤ (12323 / 10000 : Real) * y / Real.log y := by
            exact mul_le_mul_of_nonneg_left hratio_y (by norm_num)
      linarith
    exact (abs_lt).2 ⟨hlower, hupper⟩

theorem hasDusartSymmetricThetaBoundsBelow_of_endpoint_rows
    {X : Real} {rows : List DusartThetaEndpointRow}
    (cover : DusartThetaEndpointRowsCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      nlinarith
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact (dusartThetaEndpointRow_provides row hleft hright).upper x
        hleft hright
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x (by linarith) hX
      exact (dusartThetaEndpointRow_provides row hleft hright).lower x hx
      hleft hright

theorem hasDusartSymmetricThetaBoundsBelow_of_prefix_and_endpoint_rows
    {x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (prefix : HasDusartSymmetricThetaBoundsBelow x₀)
    {rows : List DusartThetaEndpointRow}
    (cover : DusartThetaEndpointRowsCoverFrom rows x₀ X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact prefix.1 x hx hsmall
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_ge hsmall) hX
      exact (dusartThetaEndpointRow_provides row hleft hright).upper
        x hleft hright
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact prefix.2 x hx hsmall
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_ge hsmall) hX
      exact (dusartThetaEndpointRow_provides row hleft hright).lower
        x hx hleft hright

theorem hasDusartSymmetricThetaBoundsBelow_of_indexed_prefix_and_endpoint_rows
    {n : Nat} {x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (prefix : HasDusartSymmetricThetaBoundsBelow x₀)
    {rows : Fin n → DusartThetaEndpointRow}
    (cover : DusartThetaEndpointIndexedCoverFrom rows x₀ X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact prefix.1 x hx hsmall
    · obtain ⟨i, hleft, hright⟩ := cover x
        (le_of_not_ge hsmall) hX
      exact (dusartThetaEndpointRow_provides (rows i) hleft hright).upper
        x hleft hright
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact prefix.2 x hx hsmall
    · obtain ⟨i, hleft, hright⟩ := cover x
        (le_of_not_ge hsmall) hX
      exact (dusartThetaEndpointRow_provides (rows i) hleft hright).lower
        x hleft hright

def DusartThetaBoundsRowsCoverUpTo
    (rows : List DusartThetaBoundsRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasDusartSymmetricThetaBoundsBelow_of_rows
    {X : Real} {rows : List DusartThetaBoundsRow}
    (cover : DusartThetaBoundsRowsCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      nlinarith
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact row.upper x hleft hright
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x
      (by linarith) hX
      exact row.lower x hx hleft hright

/-! Table 6.6 is stated in terms of relative coefficient bounds on each
interval, rather than fixed endpoint values.  Keep that published shape as a
separate row type so its finite data can be checked directly and then lowered
once into the generic theta-row consumer above. -/
structure DusartThetaRelativeRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  lower_coeff : Real
  upper_coeff : Real
  lower_bound : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    lower_coeff * x ≤ Chebyshev.theta x
  upper_bound : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    Chebyshev.theta x ≤ upper_coeff * x
  upper_coeff_error : upper_coeff - 1 < (1 : Real) / 36260
  lower_coeff_error : ∀ x : Real, 2 < x → (left : Real) ≤ x → x ≤ right →
    (1 - lower_coeff) * x <
      (12323 / 10000 : Real) * x / Real.log x

/-! The coefficient data printed in Dusart's Table 6.6.  These are kept as a
raw, exact rational table; the analytic validity fields remain explicit in
`DusartThetaRelativeRow` and are supplied by the finite verification layer. -/
structure DusartThetaTableCoefficientRow where
  left : Nat
  right : Nat
  lower_coeff : Real
  upper_coeff : Real

def dusartThetaTable6_6Coefficients :
    List DusartThetaTableCoefficientRow := [
  { left := 100000000, right := 200000000,
    lower_coeff := 99985 / 100000, upper_coeff := 99998 / 100000 },
  { left := 200000000, right := 300000000,
    lower_coeff := 99989 / 100000, upper_coeff := 99997 / 100000 },
  { left := 300000000, right := 400000000,
    lower_coeff := 99991 / 100000, upper_coeff := 99998 / 100000 },
  { left := 400000000, right := 500000000,
    lower_coeff := 99993 / 100000, upper_coeff := 99998 / 100000 },
  { left := 500000000, right := 600000000,
    lower_coeff := 99992 / 100000, upper_coeff := 99998 / 100000 },
  { left := 600000000, right := 700000000,
    lower_coeff := 99994 / 100000, upper_coeff := 99999 / 100000 },
  { left := 700000000, right := 800000000,
    lower_coeff := 99993 / 100000, upper_coeff := 99998 / 100000 },
  { left := 800000000, right := 900000000,
    lower_coeff := 99994 / 100000, upper_coeff := 99998 / 100000 },
  { left := 900000000, right := 1000000000,
    lower_coeff := 99994 / 100000, upper_coeff := 99998 / 100000 },
  { left := 1000000000, right := 2000000000,
    lower_coeff := 99995 / 100000, upper_coeff := 99999 / 100000 },
  { left := 2000000000, right := 3000000000,
    lower_coeff := 99996 / 100000, upper_coeff := 1 },
  { left := 3000000000, right := 4000000000,
    lower_coeff := 99997 / 100000, upper_coeff := 1 },
  { left := 4000000000, right := 5000000000,
    lower_coeff := 99997 / 100000, upper_coeff := 1 },
  { left := 5000000000, right := 6000000000,
    lower_coeff := 99997 / 100000, upper_coeff := 1 },
  { left := 6000000000, right := 7000000000,
    lower_coeff := 99998 / 100000, upper_coeff := 1 },
  { left := 7000000000, right := 8000000000,
    lower_coeff := 99998 / 100000, upper_coeff := 1 },
  { left := 8000000000, right := 9000000000,
    lower_coeff := 99998 / 100000, upper_coeff := 1 },
  { left := 9000000000, right := 10000000000,
    lower_coeff := 99998 / 100000, upper_coeff := 1 },
  { left := 10000000000, right := 20000000000,
    lower_coeff := 99998 / 100000, upper_coeff := 1 },
  { left := 20000000000, right := 30000000000,
    lower_coeff := 99998 / 100000, upper_coeff := 1 },
  { left := 30000000000, right := 40000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 40000000000, right := 50000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 50000000000, right := 60000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 60000000000, right := 70000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 70000000000, right := 80000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 80000000000, right := 90000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 90000000000, right := 100000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 100000000000, right := 200000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 200000000000, right := 300000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 300000000000, right := 400000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 400000000000, right := 500000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 500000000000, right := 600000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 600000000000, right := 700000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 },
  { left := 700000000000, right := 800000000000,
    lower_coeff := 99999 / 100000, upper_coeff := 1 }
]

theorem dusartThetaTable6_6Coefficients_length :
    dusartThetaTable6_6Coefficients.length = 35 := by decide

def DusartThetaTableCoefficientRow.toRelativeRow
    (row : DusartThetaTableCoefficientRow)
    (hleft : 2 ≤ row.left) (hle : row.left ≤ row.right)
    (hlower : ∀ x : Real, (row.left : Real) ≤ x → x ≤ row.right →
      row.lower_coeff * x ≤ Chebyshev.theta x)
    (hupper : ∀ x : Real, (row.left : Real) ≤ x → x ≤ row.right →
      Chebyshev.theta x ≤ row.upper_coeff * x)
    (hupper_error : row.upper_coeff - 1 < (1 : Real) / 36260)
    (hlower_error : ∀ x : Real, 2 < x → (row.left : Real) ≤ x →
      x ≤ row.right →
      (1 - row.lower_coeff) * x <
        (12323 / 10000 : Real) * x / Real.log x) :
    DusartThetaRelativeRow :=
  { left := row.left
    right := row.right
    left_large := hleft
    left_le_right := hle
    lower_coeff := row.lower_coeff
    upper_coeff := row.upper_coeff
    lower_bound := hlower
    upper_bound := hupper
    upper_coeff_error := hupper_error
    lower_coeff_error := hlower_error }

def dusartThetaRelativeRow_to_bounds
    (row : DusartThetaRelativeRow) : DusartThetaBoundsRow := by
  refine {
    left := row.left
    right := row.right
    left_large := row.left_large
    left_le_right := row.left_le_right
    upper := ?_
    lower := ?_ }
  · intro x hleft hright
    have hleft_nonneg : (0 : Real) ≤ (row.left : Real) := by positivity
    have hx : 0 ≤ x := hleft_nonneg.trans hleft
    have htheta := row.upper_bound x hleft hright
    have hcoeff := row.upper_coeff_error
    nlinarith
  · intro x hx hleft hright
    have htheta_upper := row.upper_bound x hleft hright
    have htheta_lower := row.lower_bound x hleft hright
    have herror := row.lower_coeff_error x hx hleft hright
    apply (abs_lt).2
    constructor <;> nlinarith

def DusartThetaRelativeRowsCoverUpTo
    (rows : List DusartThetaRelativeRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

def DusartThetaRelativeIndexedCoverUpTo {n : Nat}
    (rows : Fin n → DusartThetaRelativeRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem hasDusartSymmetricThetaBoundsBelow_of_relative_rows
    {X : Real} {rows : List DusartThetaRelativeRow}
    (cover : DusartThetaRelativeRowsCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_rows
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  exact ⟨dusartThetaRelativeRow_to_bounds row, by simp [hrow], hleft, hright⟩

theorem hasDusartSymmetricThetaBoundsBelow_of_indexed_relative_rows
    {n : Nat} {X : Real} {rows : Fin n → DusartThetaRelativeRow}
    (cover : DusartThetaRelativeIndexedCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_indexed_rows
  intro x hx hX
  obtain ⟨i, hleft, hright⟩ := cover x hx hX
  exact ⟨dusartThetaRelativeRow_to_bounds (rows i), hleft, hright⟩

/-! Closed regression seed for the coefficient-row adapter.  The published
table starts much later; this singleton only checks that the coefficient
representation composes with the existing low-endpoint seed. -/
def dusartThetaRelativeRow_two : DusartThetaRelativeRow := by
  let c : Real := Chebyshev.theta 2 / 2
  refine {
    left := 2
    right := 2
    left_large := by norm_num
    left_le_right := by norm_num
    lower_coeff := c
    upper_coeff := c
    lower_bound := ?_
    upper_bound := ?_
    upper_coeff_error := ?_
    lower_coeff_error := ?_ }
  · intro x hleft hright
    have hx : x = 2 := by linarith
    subst x
    dsimp [c]
    ring_nf
  · intro x hleft hright
    have hx : x = 2 := by linarith
    subst x
    dsimp [c]
    ring_nf
  · dsimp [c]
    rw [theta_two_eq_log_two]
    nlinarith [Real.log_two_lt_d9]
  · intro x hx hleft hright
    have hx2 : x = 2 := by linarith
    subst x
    dsimp [c]
    rw [theta_two_eq_log_two]
    have hlog_pos : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    have hlog_lt : Real.log (2 : Real) < 1 := by
      nlinarith [Real.log_two_lt_d9]
    have hleft_bound : (1 - Real.log (2 : Real) / 2) * 2 < 2 := by
      nlinarith
    have hright_bound : (2 : Real) <
        (12323 / 10000 : Real) * 2 / Real.log 2 := by
      apply (lt_div_iff₀ hlog_pos).2
      nlinarith [hlog_lt]
    exact hleft_bound.trans hright_bound

theorem dusartThetaRelativeRow_two_cover :
    DusartThetaRelativeRowsCoverUpTo [dusartThetaRelativeRow_two] 2 := by
  intro x hx hX
  refine ⟨dusartThetaRelativeRow_two, by simp, ?_, ?_⟩ <;> linarith

structure DusartPrimeCountingRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  lower : ∀ x : Real, (599 : Real) ≤ x → (left : Real) ≤ x →
    x ≤ right →
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real)
  upper : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x

structure DusartPrimeCountingEndpointRow where
  left : Nat
  right : Nat
  left_large : 599 ≤ left
  left_le_right : left ≤ right
  lower_endpoint : dusartPiLower right ≤ (Nat.primeCounting left : Real)
  upper_endpoint : (Nat.primeCounting right : Real) ≤ dusartPiUpper left

/-! A first nontrivial endpoint row, proved from the exact finite prime count
and elementary logarithm envelopes.  The row is deliberately a singleton:
it is a kernel-checked seed for the eventual interval-table generator. -/
def dusartPrimeCountingEndpointRow_1000 :
    DusartPrimeCountingEndpointRow := by
  have hcount : Nat.primeCounting 1000 = 168 := by decide
  have hlog_lower :
      (3 : Real) * (693147 / 1000000) +
        (3 : Real) * (1609437 / 1000000) ≤ Real.log 1000 := by
    exact LogTables.log_nat_ge_smooth_lower (by norm_num) (by norm_num)
  have hlog_upper : Real.log 1000 ≤
      (3 : Real) * (693148 / 1000000) +
        (3 : Real) * (1609438 / 1000000) := by
    exact LogTables.log_nat_le_smooth_upper (by norm_num) (by norm_num)
  have hlog_pos : 0 < Real.log (1000 : Real) :=
    Real.log_pos (by norm_num)
  refine { left := 1000, right := 1000
    left_large := by norm_num
    left_le_right := le_rfl
    lower_endpoint := ?_
    upper_endpoint := ?_ }
  · rw [hcount]
    dsimp [dusartPiLower]
    have hbase :
        1000 * (Real.log 1000 + 1) ≤ 168 * (Real.log 1000) ^ 2 := by
      let l₀ : Real :=
        (3 : Real) * (693147 / 1000000) +
          (3 : Real) * (1609437 / 1000000)
      have hmono : 0 ≤
          (Real.log 1000 - l₀) *
            (168 * (Real.log 1000 + l₀) - 1000) := by
        apply mul_nonneg
        · dsimp [l₀]
          linarith
        · dsimp [l₀]
          nlinarith [hlog_lower]
      dsimp [l₀] at hmono
      nlinarith
    field_simp [ne_of_gt hlog_pos]
    nlinarith
  · rw [hcount]
    dsimp [dusartPiUpper]
    have hbase :
        168 * (Real.log 1000) ^ 2 ≤
          1000 * Real.log 1000 + (6381 / 5000 : Real) * 1000 := by
      let u₀ : Real :=
        (3 : Real) * (693148 / 1000000) +
          (3 : Real) * (1609438 / 1000000)
      have hmono : 0 ≤
          (u₀ - Real.log 1000) *
            (168 * (u₀ + Real.log 1000) - 1000) := by
        apply mul_nonneg
        · dsimp [u₀]
          linarith
        · dsimp [u₀]
          nlinarith [hlog_upper, hlog_pos]
      dsimp [u₀] at hmono
      nlinarith
    field_simp [ne_of_gt hlog_pos]
    nlinarith

def DusartPrimeCountingEndpointRowsCoverFrom599
    (rows : List DusartPrimeCountingEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, (599 : Real) ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem dusartPrimeCountingEndpointRow_1000_cover :
    DusartPrimeCountingEndpointRowsCoverFrom599
      [dusartPrimeCountingEndpointRow_1000] 1000 := by
  intro x hx hX
  have hx1000 : x = 1000 := by linarith
  subst x
  exact ⟨dusartPrimeCountingEndpointRow_1000, by simp, by norm_num, by norm_num⟩

def DusartPrimeCountingEndpointIndexedCoverFrom599 {n : Nat}
    (rows : Fin n → DusartPrimeCountingEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, (599 : Real) ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem dusartPrimeCountingEndpointIndexedCover_of_list
    {X : Real} {rows : List DusartPrimeCountingEndpointRow}
    (cover : DusartPrimeCountingEndpointRowsCoverFrom599 rows X) :
    DusartPrimeCountingEndpointIndexedCoverFrom599
      (fun i : Fin rows.length => rows.get i) X := by
  exact indexed_interval_cover_of_list_cover rows
    (fun row => row.left) (fun row => row.right) cover

theorem dusartPrimeCountingEndpointIndexedCoverFrom599_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → DusartPrimeCountingEndpointRow}
    {right : Fin n₂ → DusartPrimeCountingEndpointRow}
    (hleft : DusartPrimeCountingEndpointIndexedCoverFrom599 left m)
    (hright : DusartPrimeCountingEndpointIndexedCoverFrom599 right X) :
    DusartPrimeCountingEndpointIndexedCoverFrom599
      (Fin.append left right) X := by
  intro x hx hX
  exact indexed_interval_cover_append left right
    (fun row => row.left) (fun row => row.right)
    (fun y hy _ hym => hleft y hy hym)
    (fun y hy _ hym hyX => hright y hy hyX)
    x hx trivial hX

theorem hasDusartRealPrimeCountingBoundsBelow_of_indexed_endpoint_rows
    {n : Nat} {X : Real}
    {rows : Fin n → DusartPrimeCountingEndpointRow}
    (cover : DusartPrimeCountingEndpointIndexedCoverFrom599 rows X)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨i, hleft, hright⟩ := cover x hx hX
    exact (dusartPrimeCountingEndpointRow_provides (rows i) hleft hright).1
  · intro x hx hX
    by_cases hsmall : x < 599
    · exact smallUpper x hx hsmall
    · obtain ⟨i, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact (dusartPrimeCountingEndpointRow_provides (rows i) hleft hright).2

theorem dusartPrimeCountingEndpointRowsCoverFrom599_append
    {m X : Real} {left right : List DusartPrimeCountingEndpointRow}
    (hleft : DusartPrimeCountingEndpointRowsCoverFrom599 left m)
    (hright : DusartPrimeCountingEndpointRowsCoverFrom599 right X) :
    DusartPrimeCountingEndpointRowsCoverFrom599 (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem dusartPrimeCountingEndpointRow_provides
    (row : DusartPrimeCountingEndpointRow) {x : Real}
    (hleft : (row.left : Real) ≤ x) (hright : x ≤ row.right) :
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real) ∧
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x := by
  have hleft599 : (599 : Real) ≤ row.left := by exact_mod_cast row.left_large
  have hright599 : (599 : Real) ≤ (row.right : Real) :=
    hleft599.trans (by exact_mod_cast row.left_le_right)
  have hfloor_left : row.left ≤ ⌊x⌋₊ := Nat.le_floor hleft
  have hfloor_right : ⌊x⌋₊ ≤ row.right := Nat.floor_le_of_le hright
  have hpi_left : (Nat.primeCounting row.left : Real) ≤
      (Nat.primeCounting ⌊x⌋₊ : Real) := by
    exact_mod_cast Nat.monotone_primeCounting hfloor_left
  have hpi_right : (Nat.primeCounting ⌊x⌋₊ : Real) ≤
      (Nat.primeCounting row.right : Real) := by
    exact_mod_cast Nat.monotone_primeCounting hfloor_right
  have hlower : dusartPiLower x ≤ dusartPiLower (row.right : Real) :=
    dusartPiLower_monotoneOn (by exact hleft599)
      (by exact hright599) hright
  have hupper : dusartPiUpper (row.left : Real) ≤ dusartPiUpper x :=
    dusartPiUpper_monotoneOn (by norm_num at hleft599 ⊢; linarith)
      (by norm_num at hleft599 hright599 ⊢; linarith) hleft
  constructor
  · exact hlower.trans (row.lower_endpoint.trans hpi_left)
  · exact hpi_right.trans (row.upper_endpoint.trans hupper)

theorem hasDusartRealPrimeCountingBoundsBelow_of_endpoint_rows
    {X : Real} {rows : List DusartPrimeCountingEndpointRow}
    (cover : DusartPrimeCountingEndpointRowsCoverFrom599 rows X)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
    exact (dusartPrimeCountingEndpointRow_provides row hleft hright).1
  · intro x hx hX
    by_cases hsmall : x < 599
    · exact smallUpper x hx hsmall
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact (dusartPrimeCountingEndpointRow_provides row hleft hright).2

def DusartPrimeCountingRowsCoverUpTo
    (rows : List DusartPrimeCountingRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

/-! The lower Dusart estimate starts only at `599`.  This variant keeps that
fact visible, so the finite table need not carry rows whose only purpose is
to establish the lower bound below `599`; the short upper range is supplied
by a separate elementary or computational lemma. -/
def DusartPrimeCountingRowsCoverFrom599
    (rows : List DusartPrimeCountingRow) (X : Real) : Prop :=
  ∀ x : Real, (599 : Real) ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasDusartRealPrimeCountingBoundsBelow_of_rows_from599
    {X : Real} {rows : List DusartPrimeCountingRow}
    (cover : DusartPrimeCountingRowsCoverFrom599 rows X)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
    exact row.lower x hx hleft hright
  · intro x hx hX
    by_cases hsmall : x < 599
    · exact smallUpper x hx hsmall
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact row.upper x hleft hright

theorem hasDusartRealPrimeCountingBoundsBelow_of_rows
    {X : Real} {rows : List DusartPrimeCountingRow}
    (cover : DusartPrimeCountingRowsCoverUpTo rows X) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x (by linarith) hX
    exact row.lower x hx hleft hright
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
    exact row.upper x hleft hright

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
