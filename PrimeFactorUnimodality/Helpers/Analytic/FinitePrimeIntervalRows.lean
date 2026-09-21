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

theorem theta_lower_of_unit_interval_endpoint
    {n : Nat} {a x : Real}
    (ha : 0 ≤ a)
    (hbound : a * ((n : Real) + 1) ≤ Chebyshev.theta (n : Real))
    (hleft : (n : Real) ≤ x)
    (hright : x < (n : Real) + 1) :
    a * x ≤ Chebyshev.theta x := by
  have hx_nonneg : 0 ≤ x := by positivity
  have hfloor : ⌊x⌋₊ = n := by
    apply (Nat.floor_eq_iff hx_nonneg).2
    constructor
    · exact_mod_cast hleft
    · simpa using hright
  have htheta : Chebyshev.theta x = Chebyshev.theta (n : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hfloor]
  calc
    a * x ≤ a * ((n : Real) + 1) :=
      mul_le_mul_of_nonneg_left (le_of_lt hright) ha
    _ ≤ Chebyshev.theta (n : Real) := hbound
    _ = Chebyshev.theta x := htheta.symm

theorem theta_upper_of_unit_interval_endpoint
    {n : Nat} {b x : Real}
    (hb : 0 ≤ b)
    (hbound : Chebyshev.theta (n : Real) ≤ b * (n : Real))
    (hleft : (n : Real) ≤ x)
    (hright : x < (n : Real) + 1) :
    Chebyshev.theta x ≤ b * x := by
  have hx_nonneg : 0 ≤ x := by positivity
  have hfloor : ⌊x⌋₊ = n := by
    apply (Nat.floor_eq_iff hx_nonneg).2
    constructor
    · exact_mod_cast hleft
    · simpa using hright
  have htheta : Chebyshev.theta x = Chebyshev.theta (n : Real) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, hfloor]
  calc
    Chebyshev.theta x = Chebyshev.theta (n : Real) := htheta
    _ ≤ b * (n : Real) := hbound
    _ ≤ b * x := mul_le_mul_of_nonneg_left hleft hb

def DusartThetaEndpointRow.toStrictUpperRow
    (row : DusartThetaEndpointRow)
    (hstrict : row.theta_upper < row.left) : StrictThetaUpperRow :=
  { left := row.left
    right := row.right
    left_large := row.left_large
    left_le_right := row.left_le_right
    theta_upper := row.theta_upper
    theta_right_le := row.theta_right_le
    upper_error := by
      exact sub_neg.mpr hstrict }

def DusartThetaEndpointRowsStrictUpperCoverUpTo
    (rows : List DusartThetaEndpointRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right ∧
      row.theta_upper < row.left

theorem hasStrictThetaUpperBelow_of_endpoint_rows
    {X : Real} {rows : List DusartThetaEndpointRow}
    (cover : DusartThetaEndpointRowsStrictUpperCoverUpTo rows X) :
    HasStrictThetaUpperBelow X := by
  intro x hx hX
  by_cases hsmall : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
    linarith
  · obtain ⟨row, hrow, hleft, hright, hstrict⟩ :=
      cover x (le_of_not_gt hsmall) hX
    exact strictThetaUpperRow_provides
      (row.toStrictUpperRow hstrict) hleft hright

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

theorem hasStrictThetaUpperBelow_of_prefix_and_indexed_rows
    {x₀ X : Real} (prefix : HasStrictThetaUpperBelow x₀)
    {n : Nat} {rows : Fin n → StrictThetaUpperRow}
    (cover : ∀ x : Real, x₀ ≤ x → x ≤ X →
      ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right) :
    HasStrictThetaUpperBelow X := by
  intro x hx hX
  by_cases hsmall : x ≤ x₀
  · exact prefix x hx hsmall
  · obtain ⟨i, hleft, hright⟩ := cover x
      (le_of_not_ge hsmall) hX
    exact strictThetaUpperRow_provides (rows i) hleft hright

theorem strictThetaUpperRowsCoverUpTo_append
    {m X : Real} {left right : List StrictThetaUpperRow}
    (hleft : StrictThetaUpperRowsCoverUpTo left m)
    (hright : StrictThetaUpperRowsCoverUpTo right X) :
    StrictThetaUpperRowsCoverUpTo (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem strictThetaUpperIndexedCoverUpTo_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → StrictThetaUpperRow}
    {right : Fin n₂ → StrictThetaUpperRow}
    (hleft : StrictThetaUpperIndexedCoverUpTo left m)
    (hright : StrictThetaUpperIndexedCoverUpTo right X) :
    StrictThetaUpperIndexedCoverUpTo (Fin.append left right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨i, hleft_lower, hleft_upper⟩ := hleft x hx hxm
    refine ⟨Fin.castAdd n₂ i, ?_⟩
    simpa [Fin.append_left] using And.intro hleft_lower hleft_upper
  · obtain ⟨i, hright_lower, hright_upper⟩ :=
      hright x hx hX
    refine ⟨Fin.natAdd n₁ i, ?_⟩
    simpa [Fin.append_right] using And.intro hright_lower hright_upper

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

theorem hasDusartSymmetricThetaBoundsBelow_of_prefix_and_indexed_strict_rows_and_lower
    {x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (prefix : HasDusartSymmetricThetaBoundsBelow x₀)
    {n : Nat} {rows : Fin n → StrictThetaUpperRow}
    (cover : ∀ x : Real, x₀ ≤ x → x ≤ X →
      ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right)
    (lower : ∀ x : Real, 2 < x → x ≤ X →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · have hupper := prefix.1 x hx hsmall
      nlinarith
    · obtain ⟨i, hleft, hright⟩ := cover x
        (h2x₀.trans (le_of_not_ge hsmall)) hX
      exact strictThetaUpperRow_provides (rows i) hleft hright
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact prefix.2 x hx hsmall
    · exact lower x hx hX

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

/-! The next endpoint is small enough for a direct Chebyshev sum.  Keeping it
as an ordinary endpoint row lets the same cover and assembler consume it as
the larger finite tables. -/
def dusartThetaEndpointRow_three : DusartThetaEndpointRow := by
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 3
  have hp : Nat.primesLE 3 = {2, 3} := by decide
  rw [hp] at htheta
  norm_num [Nat.log, Nat.log.go] at htheta
  have hlog2pos : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num)
  have hlog3pos : 0 < Real.log (3 : Real) :=
    Real.log_pos (by norm_num)
  have htheta_lt : Chebyshev.theta (3 : Real) < 3 := by
    nlinarith [htheta, Real.log_two_lt_d9, Real.log_three_lt_d9]
  have hupper : Chebyshev.theta (3 : Real) - 3 < (3 : Real) / 36260 := by
    nlinarith
  have hlower_upper : Chebyshev.theta (3 : Real) - 3 <
      (12323 / 10000 : Real) * 3 / Real.log 3 := by
    have hrhs : 0 < (12323 / 10000 : Real) * 3 / Real.log 3 := by
      positivity
    linarith
  have htheta_nonneg : 0 ≤ Chebyshev.theta (3 : Real) :=
    Chebyshev.theta_nonneg 3
  have hdiff_nonneg : 0 ≤ (3 : Real) - Chebyshev.theta 3 := by
    linarith
  have hdiff_log : ((3 : Real) - Chebyshev.theta 3) * Real.log 3 <
      (3 : Real) * (11 / 10 : Real) := by
    have hlog3 : Real.log (3 : Real) < (11 : Real) / 10 :=
      Real.log_three_lt_d9
    have hfirst := mul_le_mul_of_nonneg_left hlog3.le hdiff_nonneg
    have hsecond := mul_le_mul_of_nonneg_right
      (show (3 : Real) - Chebyshev.theta 3 ≤ 3 by linarith)
      (by norm_num : (0 : Real) ≤ (11 : Real) / 10)
    nlinarith
  have hlower_lower : (3 : Real) - Chebyshev.theta 3 <
      (12323 / 10000 : Real) * 3 / Real.log 3 := by
    apply (lt_div_iff₀ hlog3pos).2
    nlinarith [hdiff_log]
  exact
    { left := 3
      right := 3
      left_large := by norm_num
      left_le_right := by norm_num
      theta_lower := Chebyshev.theta 3
      theta_upper := Chebyshev.theta 3
      theta_lower_le := le_rfl
      theta_right_le := le_rfl
      upper_error := hupper
      lower_upper_error := hlower_upper
      lower_lower_error := hlower_lower }

theorem dusartThetaEndpointRow_three_cover :
    DusartThetaEndpointRowsCoverUpTo
      [dusartThetaEndpointRow_two, dusartThetaEndpointRow_three] 3 := by
  intro x hx hX
  by_cases hsmall : x ≤ 2
  · refine ⟨dusartThetaEndpointRow_two, by simp, ?_, hsmall⟩
    norm_num
    exact hx
  · refine ⟨dusartThetaEndpointRow_three, by simp, ?_, ?_⟩
    · norm_num
      exact le_of_not_ge hsmall
    · exact hX

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

/-! Compact chunks for the bounded theta endpoint table.  A chunk carries its
    coverage proof, so later generated bands can be appended without exposing
    one declaration per endpoint to the analytic assembly. -/
structure DusartThetaEndpointChunk where
  n : Nat
  cutoff : Real
  rows : Fin n → DusartThetaEndpointRow
  cover : DusartThetaEndpointIndexedCoverUpTo rows cutoff

def DusartThetaEndpointChunk.of_list
    {rows : List DusartThetaEndpointRow} {cutoff : Real}
    (cover : DusartThetaEndpointRowsCoverUpTo rows cutoff) :
    DusartThetaEndpointChunk :=
  { n := rows.length
    cutoff := cutoff
    rows := fun i => rows.get i
    cover := dusartThetaEndpointIndexedCover_of_list cover }

def DusartThetaEndpointChunk.append
    (left right : DusartThetaEndpointChunk) :
    DusartThetaEndpointChunk :=
  { n := left.n + right.n
    cutoff := right.cutoff
    rows := Fin.append left.rows right.rows
    cover := dusartThetaEndpointIndexedCoverUpTo_append
      left.cover right.cover }

def DusartThetaEndpointChunk.appendMany
    (first : DusartThetaEndpointChunk)
    (rest : List DusartThetaEndpointChunk) :
    DusartThetaEndpointChunk :=
  match rest with
  | [] => first
  | next :: tail =>
      DusartThetaEndpointChunk.appendMany
        (DusartThetaEndpointChunk.append first next) tail

theorem hasDusartSymmetricThetaBoundsBelow_of_endpoint_chunk
    (chunk : DusartThetaEndpointChunk) :
    HasDusartSymmetricThetaBoundsBelow chunk.cutoff := by
  exact hasDusartSymmetricThetaBoundsBelow_of_indexed_endpoint_rows
    chunk.cover

theorem hasDusartSymmetricThetaBoundsBelow_of_endpoint_chunks
    (first : DusartThetaEndpointChunk)
    (rest : List DusartThetaEndpointChunk) :
    HasDusartSymmetricThetaBoundsBelow
      (DusartThetaEndpointChunk.appendMany first rest).cutoff := by
  induction rest generalizing first with
  | nil =>
      exact hasDusartSymmetricThetaBoundsBelow_of_endpoint_chunk first
  | cons next tail ih =>
      exact ih (DusartThetaEndpointChunk.append first next)

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

theorem dusartThetaRelativeRow_provides
    (row : DusartThetaRelativeRow) : DusartThetaBoundsRow := by
  have hleft2 : (2 : Real) ≤ row.left := by exact_mod_cast row.left_large
  have hright2 : (2 : Real) ≤ (row.right : Real) := by
    exact le_trans hleft2 (by exact_mod_cast row.left_le_right)
  refine {
    left := row.left
    right := row.right
    left_large := row.left_large
    left_le_right := row.left_le_right
    upper := ?_
    lower := ?_ }
  · intro x hleft hright
    have hxpos : 0 < x := by linarith [hleft2, hleft]
    have hupper := row.upper_bound x hleft hright
    have hcoeff : row.upper_coeff < 1 + (1 : Real) / 36260 := by
      linarith [row.upper_coeff_error]
    have hscaled : row.upper_coeff * x <
        (1 + (1 : Real) / 36260) * x :=
      mul_lt_mul_of_pos_right hcoeff hxpos
    nlinarith
  · intro x hx hleft hright
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hupper := row.upper_bound x hleft hright
    have hlower := row.lower_bound x hleft hright
    have herror := row.lower_coeff_error x hx hleft hright
    have hxpos : 0 < x := by linarith [hleft2, hleft]
    have hcoeff : row.upper_coeff < 1 + (1 : Real) / 36260 := by
      linarith [row.upper_coeff_error]
    have hscaled : row.upper_coeff * x <
        (1 + (1 : Real) / 36260) * x :=
      mul_lt_mul_of_pos_right hcoeff hxpos
    have hupper_error : Chebyshev.theta x - x <
        (12323 / 10000 : Real) * x / Real.log x := by
      nlinarith
    have hlower_error :
        -(12323 / 10000 : Real) * x / Real.log x <
          Chebyshev.theta x - x := by
      nlinarith
    exact (abs_lt).2 ⟨hlower_error, hupper_error⟩

def DusartThetaRelativeRowsCoverUpTo
    (rows : List DusartThetaRelativeRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasDusartSymmetricThetaBoundsBelow_of_relative_rows
    {X : Real} {rows : List DusartThetaRelativeRow}
    (cover : DusartThetaRelativeRowsCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      nlinarith
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact (dusartThetaRelativeRow_provides row).upper x hleft hright
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x (by linarith) hX
    exact (dusartThetaRelativeRow_provides row).lower x hx hleft hright

/-! The six coefficient columns printed in Dusart's Table 6.6.  The first
pair gives constant-coefficient bounds; the next two pairs give the
`1 / log x` and `1 / log^2 x` correction bounds. -/
structure DusartThetaTable66Row where
  left : Nat
  right : Nat
  a0 : Real
  b0 : Real
  a1 : Real
  b1 : Real
  a2 : Real
  b2 : Real
  lower_zero : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    a0 * x ≤ Chebyshev.theta x
  upper_zero : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    Chebyshev.theta x ≤ b0 * x
  lower_one : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    x - a1 * x / Real.log x ≤ Chebyshev.theta x
  upper_one : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    Chebyshev.theta x ≤ x + b1 * x / Real.log x
  lower_two : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    x - a2 * x / Real.log x ^ 2 ≤ Chebyshev.theta x
  upper_two : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    Chebyshev.theta x ≤ x + b2 * x / Real.log x ^ 2

def DusartThetaTable66Row.toRelativeZero
    (row : DusartThetaTable66Row)
    (hleft_large : 2 ≤ row.left)
    (hleft_right : row.left ≤ row.right)
    (hupper_error : row.b0 - 1 < (1 : Real) / 36260)
    (hlower_error : ∀ x : Real, 2 < x → (row.left : Real) ≤ x →
      x ≤ row.right →
      (1 - row.a0) * x <
        (12323 / 10000 : Real) * x / Real.log x) :
    DusartThetaRelativeRow :=
  { left := row.left
    right := row.right
    left_large := hleft_large
    left_le_right := hleft_right
    lower_coeff := row.a0
    upper_coeff := row.b0
    lower_bound := row.lower_zero
    upper_bound := row.upper_zero
    upper_coeff_error := hupper_error
    lower_coeff_error := hlower_error }

theorem dusartThetaTable66Row_provides_zero
    (row : DusartThetaTable66Row)
    (hleft_large : 2 ≤ row.left)
    (hleft_right : row.left ≤ row.right)
    (hupper_error : row.b0 - 1 < (1 : Real) / 36260)
    (hlower_error : ∀ x : Real, 2 < x → (row.left : Real) ≤ x →
      x ≤ row.right →
      (1 - row.a0) * x <
        (12323 / 10000 : Real) * x / Real.log x) :
    DusartThetaBoundsRow := by
  exact dusartThetaRelativeRow_provides
    (row.toRelativeZero hleft_large hleft_right hupper_error hlower_error)

structure DusartThetaTable66CoefficientData where
  left : Nat
  right : Nat
  a0 : Real
  b0 : Real
  a1 : Real
  b1 : Real
  a2 : Real
  b2 : Real

/-! All six published Table 6.6 inequalities for one coefficient row are
    carried together.  This keeps the row certificate data independent of the
    common finite-range assembler. -/
structure DusartThetaTable66FormulaBounds
    (data : DusartThetaTable66CoefficientData) : Prop where
  lower_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    data.a0 * x ≤ Chebyshev.theta x
  upper_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    Chebyshev.theta x ≤ data.b0 * x
  lower_one : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    x - data.a1 * x / Real.log x ≤ Chebyshev.theta x
  upper_one : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    Chebyshev.theta x ≤ x + data.b1 * x / Real.log x
  lower_two : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    x - data.a2 * x / Real.log x ^ 2 ≤ Chebyshev.theta x
  upper_two : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ x + data.b2 * x / Real.log x ^ 2

/-! The constant-coefficient columns can be transported from endpoint bounds
    using only monotonicity of `theta`.  The logarithmic correction columns
    retain their own interval arguments. -/
theorem dusartThetaTable66_constant_bounds_of_endpoints
    (data : DusartThetaTable66CoefficientData)
    (ha0 : 0 ≤ data.a0) (hb0 : 0 ≤ data.b0)
    (lower_endpoint : data.a0 * (data.right : Real) ≤
      Chebyshev.theta data.left)
    (upper_endpoint : Chebyshev.theta data.right ≤
      data.b0 * (data.left : Real)) :
    (∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      data.a0 * x ≤ Chebyshev.theta x) ∧
    (∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ data.b0 * x) := by
  constructor
  · intro x hleft hright
    have hleft_le_theta : Chebyshev.theta data.left ≤
        Chebyshev.theta x := Chebyshev.theta_mono hleft
    have hscale : data.a0 * x ≤ data.a0 * (data.right : Real) := by
      exact mul_le_mul_of_nonneg_left hright ha0
    exact hscale.trans (lower_endpoint.trans hleft_le_theta)
  · intro x hleft hright
    have hright_theta : Chebyshev.theta x ≤
        Chebyshev.theta data.right := Chebyshev.theta_mono hright
    have hscale : data.b0 * (data.left : Real) ≤ data.b0 * x := by
      exact mul_le_mul_of_nonneg_left hleft hb0
    exact hright_theta.trans (upper_endpoint.trans hscale)

/-! The four logarithmic columns have the same endpoint shape once their
    correction functions have been shown monotone on the row.  This keeps
    the finite numerical input to one pair of endpoint inequalities per
    column; the monotonicity proofs remain ordinary real analysis. -/
theorem dusartThetaTable66_formula_bounds_of_monotone_corrections
    (data : DusartThetaTable66CoefficientData)
    (hle : data.left ≤ data.right)
    (lower_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      data.a0 * x ≤ Chebyshev.theta x)
    (upper_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ data.b0 * x)
    (lower_one_mono : MonotoneOn
      (fun x : Real => x - data.a1 * x / Real.log x)
      (Set.Icc (data.left : Real) (data.right : Real)))
    (upper_one_mono : MonotoneOn
      (fun x : Real => x + data.b1 * x / Real.log x)
      (Set.Icc (data.left : Real) (data.right : Real)))
    (lower_two_mono : MonotoneOn
      (fun x : Real => x - data.a2 * x / Real.log x ^ 2)
      (Set.Icc (data.left : Real) (data.right : Real)))
    (upper_two_mono : MonotoneOn
      (fun x : Real => x + data.b2 * x / Real.log x ^ 2)
      (Set.Icc (data.left : Real) (data.right : Real)))
    (lower_one_endpoint :
      data.right - data.a1 * data.right / Real.log data.right ≤
        Chebyshev.theta data.left)
    (upper_one_endpoint :
      Chebyshev.theta data.right ≤
        data.left + data.b1 * data.left / Real.log data.left)
    (lower_two_endpoint :
      data.right - data.a2 * data.right / Real.log data.right ^ 2 ≤
        Chebyshev.theta data.left)
    (upper_two_endpoint :
      Chebyshev.theta data.right ≤
        data.left + data.b2 * data.left / Real.log data.left ^ 2) :
    DusartThetaTable66FormulaBounds data := by
  refine { lower_zero := lower_zero, upper_zero := upper_zero,
    lower_one := ?_, upper_one := ?_, lower_two := ?_, upper_two := ?_ }
  · intro x hleft hright
    have hxmem : x ∈ Set.Icc (data.left : Real) (data.right : Real) :=
      ⟨hleft, hright⟩
    have hrightmem : (data.right : Real) ∈
        Set.Icc (data.left : Real) (data.right : Real) := by
      exact ⟨by exact_mod_cast hle, le_rfl⟩
    have hmono := lower_one_mono hxmem hrightmem hright
    have htheta := Chebyshev.theta_mono hleft
    exact hmono.trans (lower_one_endpoint.trans htheta)
  · intro x hleft hright
    have hxmem : x ∈ Set.Icc (data.left : Real) (data.right : Real) :=
      ⟨hleft, hright⟩
    have hleftmem : (data.left : Real) ∈
        Set.Icc (data.left : Real) (data.right : Real) := by
      exact ⟨le_rfl, by exact_mod_cast hle⟩
    have hmono := upper_one_mono hleftmem hxmem hleft
    have htheta := Chebyshev.theta_mono hright
    exact htheta.trans (upper_one_endpoint.trans hmono)
  · intro x hleft hright
    have hxmem : x ∈ Set.Icc (data.left : Real) (data.right : Real) :=
      ⟨hleft, hright⟩
    have hrightmem : (data.right : Real) ∈
        Set.Icc (data.left : Real) (data.right : Real) := by
      exact ⟨by exact_mod_cast hle, le_rfl⟩
    have hmono := lower_two_mono hxmem hrightmem hright
    have htheta := Chebyshev.theta_mono hleft
    exact hmono.trans (lower_two_endpoint.trans htheta)
  · intro x hleft hright
    have hxmem : x ∈ Set.Icc (data.left : Real) (data.right : Real) :=
      ⟨hleft, hright⟩
    have hleftmem : (data.left : Real) ∈
        Set.Icc (data.left : Real) (data.right : Real) := by
      exact ⟨le_rfl, by exact_mod_cast hle⟩
    have hmono := upper_two_mono hleftmem hxmem hleft
    have htheta := Chebyshev.theta_mono hright
    exact htheta.trans (upper_two_endpoint.trans hmono)

def dusartThetaTable6_6CoefficientData :
    List DusartThetaTable66CoefficientData := [
  { left := 100000000, right := 200000000,
    a0 := 99985 / 100000, b0 := 99998 / 100000,
    a1 := 275 / 100000, b1 := -44 / 100000,
    a2 := 5062 / 100000, b2 := -851 / 100000 },
  { left := 200000000, right := 300000000,
    a0 := 99989 / 100000, b0 := 99997 / 100000,
    a1 := 201 / 100000, b1 := -65 / 100000,
    a2 := 3847 / 100000, b2 := -1275 / 100000 },
  { left := 300000000, right := 400000000,
    a0 := 99991 / 100000, b0 := 99998 / 100000,
    a1 := 165 / 100000, b1 := -57 / 100000,
    a2 := 3256 / 100000, b2 := -1131 / 100000 },
  { left := 400000000, right := 500000000,
    a0 := 99993 / 100000, b0 := 99998 / 100000,
    a1 := 124 / 100000, b1 := -49 / 100000,
    a2 := 2447 / 100000, b2 := -988 / 100000 },
  { left := 500000000, right := 600000000,
    a0 := 99992 / 100000, b0 := 99998 / 100000,
    a1 := 152 / 100000, b1 := -52 / 100000,
    a2 := 3039 / 100000, b2 := -1061 / 100000 },
  { left := 600000000, right := 700000000,
    a0 := 99994 / 100000, b0 := 99999 / 100000,
    a1 := 103 / 100000, b1 := -38 / 100000,
    a2 := 2095 / 100000, b2 := -785 / 100000 },
  { left := 700000000, right := 800000000,
    a0 := 99993 / 100000, b0 := 99998 / 100000,
    a1 := 126 / 100000, b1 := -51 / 100000,
    a2 := 2577 / 100000, b2 := -1054 / 100000 },
  { left := 800000000, right := 900000000,
    a0 := 99994 / 100000, b0 := 99998 / 100000,
    a1 := 110 / 100000, b1 := -44 / 100000,
    a2 := 2268 / 100000, b2 := -916 / 100000 },
  { left := 900000000, right := 1000000000,
    a0 := 99994 / 100000, b0 := 99998 / 100000,
    a1 := 117 / 100000, b1 := -50 / 100000,
    a2 := 2398 / 100000, b2 := -1050 / 100000 },
  { left := 1000000000, right := 2000000000,
    a0 := 99995 / 100000, b0 := 99999 / 100000,
    a1 := 96 / 100000, b1 := -21 / 100000,
    a2 := 2009 / 100000, b2 := -455 / 100000 },
  { left := 2000000000, right := 3000000000,
    a0 := 99996 / 100000, b0 := 1,
    a1 := 67 / 100000, b1 := -18 / 100000,
    a2 := 1427 / 100000, b2 := -401 / 100000 },
  { left := 3000000000, right := 4000000000,
    a0 := 99997 / 100000, b0 := 1,
    a1 := 62 / 100000, b1 := -15 / 100000,
    a2 := 1340 / 100000, b2 := -333 / 100000 },
  { left := 4000000000, right := 5000000000,
    a0 := 99997 / 100000, b0 := 1,
    a1 := 50 / 100000, b1 := -17 / 100000,
    a2 := 1087 / 100000, b2 := -390 / 100000 },
  { left := 5000000000, right := 6000000000,
    a0 := 99997 / 100000, b0 := 1,
    a1 := 46 / 100000, b1 := -18 / 100000,
    a2 := 1026 / 100000, b2 := -410 / 100000 },
  { left := 6000000000, right := 7000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 40 / 100000, b1 := -13 / 100000,
    a2 := 900 / 100000, b2 := -313 / 100000 },
  { left := 7000000000, right := 8000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 45 / 100000, b1 := -18 / 100000,
    a2 := 1011 / 100000, b2 := -415 / 100000 },
  { left := 8000000000, right := 9000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 34 / 100000, b1 := -16 / 100000,
    a2 := 774 / 100000, b2 := -367 / 100000 },
  { left := 9000000000, right := 10000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 37 / 100000, b1 := -10 / 100000,
    a2 := 840 / 100000, b2 := -249 / 100000 },
  { left := 10000000000, right := 20000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 38 / 100000, b1 := -8 / 100000,
    a2 := 876 / 100000, b2 := -203 / 100000 },
  { left := 20000000000, right := 30000000000,
    a0 := 99998 / 100000, b0 := 1,
    a1 := 25 / 100000, b1 := -6 / 100000,
    a2 := 584 / 100000, b2 := -152 / 100000 },
  { left := 30000000000, right := 40000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 20 / 100000, b1 := -5 / 100000,
    a2 := 473 / 100000, b2 := -122 / 100000 },
  { left := 40000000000, right := 50000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 18 / 100000, b1 := -7 / 100000,
    a2 := 431 / 100000, b2 := -183 / 100000 },
  { left := 50000000000, right := 60000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 19 / 100000, b1 := -4 / 100000,
    a2 := 458 / 100000, b2 := -119 / 100000 },
  { left := 60000000000, right := 70000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 15 / 100000, b1 := -6 / 100000,
    a2 := 356 / 100000, b2 := -167 / 100000 },
  { left := 70000000000, right := 80000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 14 / 100000, b1 := -4 / 100000,
    a2 := 338 / 100000, b2 := -117 / 100000 },
  { left := 80000000000, right := 90000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 11 / 100000, b1 := -6 / 100000,
    a2 := 276 / 100000, b2 := -164 / 100000 },
  { left := 90000000000, right := 100000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 11 / 100000, b1 := -4 / 100000,
    a2 := 262 / 100000, b2 := -114 / 100000 },
  { left := 100000000000, right := 200000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 14 / 100000, b1 := -2 / 100000,
    a2 := 341 / 100000, b2 := -58 / 100000 },
  { left := 200000000000, right := 300000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 8 / 100000, b1 := -2 / 100000,
    a2 := 206 / 100000, b2 := -57 / 100000 },
  { left := 300000000000, right := 400000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 7 / 100000, b1 := -1 / 100000,
    a2 := 170 / 100000, b2 := -31 / 100000 },
  { left := 400000000000, right := 500000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 8 / 100000, b1 := -2 / 100000,
    a2 := 188 / 100000, b2 := -61 / 100000 },
  { left := 500000000000, right := 600000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 6 / 100000, b1 := -1 / 100000,
    a2 := 138 / 100000, b2 := -38 / 100000 },
  { left := 600000000000, right := 700000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 5 / 100000, b1 := -2 / 100000,
    a2 := 131 / 100000, b2 := -70 / 100000 },
  { left := 700000000000, right := 800000000000,
    a0 := 99999 / 100000, b0 := 1,
    a1 := 6 / 100000, b1 := -1 / 100000,
    a2 := 144 / 100000, b2 := -39 / 100000 }
]

theorem dusartThetaTable6_6CoefficientData_length :
    dusartThetaTable6_6CoefficientData.length = 34 := by decide

theorem dusartThetaTable6_6CoefficientData_side_conditions :
    ∀ row ∈ dusartThetaTable6_6CoefficientData,
      0 ≤ row.a1 ∧ row.a1 < (12323 : Real) / 10000 ∧ row.b0 ≤ 1 := by
  norm_num [dusartThetaTable6_6CoefficientData]

theorem dusartThetaTable6_6CoefficientData_coefficients_nonneg :
    ∀ row ∈ dusartThetaTable6_6CoefficientData,
      0 ≤ row.a0 ∧ 0 ≤ row.b0 := by
  norm_num [dusartThetaTable6_6CoefficientData]

theorem dusartThetaTable6_6CoefficientData_upper_one_coeff_negative :
    ∀ row ∈ dusartThetaTable6_6CoefficientData, row.b1 < 0 := by
  norm_num [dusartThetaTable6_6CoefficientData]

theorem dusartThetaTable6_6CoefficientData_row_bounds :
    ∀ row ∈ dusartThetaTable6_6CoefficientData,
      2 ≤ row.left ∧ row.left ≤ row.right ∧
      (row.right : Real) ≤ (8e11 : Real) ∧
      (99985 : Real) / 100000 ≤ row.a0 ∧ row.b0 ≤ 1 := by
  norm_num [dusartThetaTable6_6CoefficientData]

theorem strictThetaUpper_of_table66_formula_data
    (data : DusartThetaTable66CoefficientData)
    (hdata : data ∈ dusartThetaTable6_6CoefficientData)
    (formula : DusartThetaTable66FormulaBounds data)
    {x : Real} (hleft : (data.left : Real) ≤ x)
    (hright : x ≤ data.right) :
    Chebyshev.theta x < x := by
  have hrow := dusartThetaTable6_6CoefficientData_row_bounds data hdata
  have hleft_large : (2 : Real) ≤ data.left := by
    exact_mod_cast hrow.1
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hupper := formula.upper_one x hleft hright
  have hb1 := dusartThetaTable6_6CoefficientData_upper_one_coeff_negative
    data hdata
  have hcorrection : data.b1 * x / Real.log x < 0 := by
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hb1 hxpos) hlogpos
  nlinarith

def dusartThetaTable6_6CoefficientDataNatRanges : List (Nat × Nat) :=
  dusartThetaTable6_6CoefficientData.map fun row => (row.left, row.right)

theorem dusartThetaTable6_6CoefficientDataNatRanges_length :
    dusartThetaTable6_6CoefficientDataNatRanges.length = 34 := by
  simp [dusartThetaTable6_6CoefficientDataNatRanges,
    dusartThetaTable6_6CoefficientData_length]

theorem dusartThetaTable6_6CoefficientDataNatRanges_adjacent :
    dusartThetaTable6_6CoefficientDataNatRanges.Chain'
      (fun first second => first.2 = second.1) := by
  decide

theorem dusartThetaTable6_6CoefficientDataNatRanges_cover :
    ∀ n : Nat, 100000000 ≤ n → n ≤ 800000000000 →
      ∃ range ∈ dusartThetaTable6_6CoefficientDataNatRanges,
        range.1 ≤ n ∧ n ≤ range.2 := by
  intro n hn hN
  simp [dusartThetaTable6_6CoefficientDataNatRanges,
    dusartThetaTable6_6CoefficientData]
  omega

theorem dusartThetaTable6_6CoefficientData_cover_real :
    ∀ x : Real, (100000000 : Real) ≤ x → x ≤ (8e11 : Real) →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right := by
  intro x hlow hhigh
  have hceil_low : 100000000 ≤ ⌈x⌉₊ := by
    exact_mod_cast hlow.trans (Nat.le_ceil x)
  have hceil_high : ⌈x⌉₊ ≤ 800000000000 := by
    exact Nat.ceil_le.mpr hhigh
  obtain ⟨data, hdata, hleft, hright⟩ :
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        data.left ≤ ⌈x⌉₊ ∧ ⌈x⌉₊ ≤ data.right := by
    simpa [dusartThetaTable6_6CoefficientDataNatRanges] using
      dusartThetaTable6_6CoefficientDataNatRanges_cover
        ⌈x⌉₊ hceil_low hceil_high
  refine ⟨data, hdata, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast hleft) (Nat.le_ceil x)
  · exact le_trans (Nat.le_ceil x) (by exact_mod_cast hright)

def DusartThetaTable66CoefficientData.toRow
    (data : DusartThetaTable66CoefficientData)
    (lower_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      data.a0 * x ≤ Chebyshev.theta x)
    (upper_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ data.b0 * x)
    (lower_one : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      x - data.a1 * x / Real.log x ≤ Chebyshev.theta x)
    (upper_one : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ x + data.b1 * x / Real.log x)
    (lower_two : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      x - data.a2 * x / Real.log x ^ 2 ≤ Chebyshev.theta x)
    (upper_two : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ x + data.b2 * x / Real.log x ^ 2) :
    DusartThetaTable66Row :=
  { left := data.left
    right := data.right
    a0 := data.a0
    b0 := data.b0
    a1 := data.a1
    b1 := data.b1
    a2 := data.a2
    b2 := data.b2
    lower_zero := lower_zero
    upper_zero := upper_zero
    lower_one := lower_one
    upper_one := upper_one
    lower_two := lower_two
    upper_two := upper_two }

/-! The published six-column row can be lowered directly to the relative-row
    interface after all of its interval inequalities have been proved.  This
    keeps the `1 / log x` and `1 / log x ^ 2` estimates attached to the row
    instead of projecting them away before verification. -/
def DusartThetaTable66CoefficientData.toRelativeRow_of_formula_bounds
    (data : DusartThetaTable66CoefficientData)
    (hleft : 2 ≤ data.left) (hle : data.left ≤ data.right)
    (hupper_error : data.b0 - 1 < (1 : Real) / 36260)
    (ha1_nonneg : 0 ≤ data.a1)
    (ha1 : data.a1 < (12323 : Real) / 10000)
    (lower_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      data.a0 * x ≤ Chebyshev.theta x)
    (upper_zero : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ data.b0 * x)
    (lower_one : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      x - data.a1 * x / Real.log x ≤ Chebyshev.theta x)
    (upper_one : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ x + data.b1 * x / Real.log x)
    (lower_two : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      x - data.a2 * x / Real.log x ^ 2 ≤ Chebyshev.theta x)
    (upper_two : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ x + data.b2 * x / Real.log x ^ 2) :
    DusartThetaRelativeRow := by
  exact (data.toRow lower_zero upper_zero lower_one upper_one lower_two upper_two).toRelativeRow
    hleft hle hupper_error ha1_nonneg ha1

def DusartThetaTable66Row.toRelativeRow
    (row : DusartThetaTable66Row)
    (hleft : 2 ≤ row.left) (hle : row.left ≤ row.right)
    (hupper_error : row.b0 - 1 < (1 : Real) / 36260)
    (ha1_nonneg : 0 ≤ row.a1)
    (ha1 : row.a1 < (12323 : Real) / 10000) :
    DusartThetaRelativeRow :=
  { left := row.left
    right := row.right
    left_large := hleft
    left_le_right := hle
    lower_coeff := 1 - row.a1 / Real.log (row.right : Real)
    upper_coeff := row.b0
    lower_bound := by
      intro x hleftx hrightx
      have hxpos : 0 < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
      have hlog_le : Real.log x ≤ Real.log (row.right : Real) :=
        Real.log_le_log hxpos hrightx
      have hinv : 1 / Real.log (row.right : Real) ≤ 1 / Real.log x :=
        one_div_le_one_div_of_le hlogpos hlog_le
      have hmul : row.a1 * x / Real.log (row.right : Real) ≤
          row.a1 * x / Real.log x := by
        calc
          row.a1 * x / Real.log (row.right : Real) =
              (row.a1 * x) * (1 / Real.log (row.right : Real)) := by ring
          _ ≤ (row.a1 * x) * (1 / Real.log x) :=
            mul_le_mul_of_nonneg_left hinv
              (mul_nonneg ha1_nonneg hxpos.le)
          _ = row.a1 * x / Real.log x := by ring
      have hformula := row.lower_one x hleftx hrightx
      nlinarith
    upper_bound := row.upper_zero
    upper_coeff_error := hupper_error
    lower_coeff_error := by
      intro x hx hleftx hrightx
      have hxpos : 0 < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
      have hlog_le : Real.log x ≤ Real.log (row.right : Real) :=
        Real.log_le_log hxpos hrightx
      have hinv : 1 / Real.log (row.right : Real) ≤ 1 / Real.log x :=
        one_div_le_one_div_of_le hlogpos hlog_le
      have hmul : row.a1 * x / Real.log (row.right : Real) ≤
          row.a1 * x / Real.log x := by
        calc
          row.a1 * x / Real.log (row.right : Real) =
              (row.a1 * x) * (1 / Real.log (row.right : Real)) := by ring
          _ ≤ (row.a1 * x) * (1 / Real.log x) :=
            mul_le_mul_of_nonneg_left hinv
              (mul_nonneg ha1_nonneg hxpos.le)
          _ = row.a1 * x / Real.log x := by ring
      have ha1' : row.a1 * x / Real.log x <
          (12323 / 10000 : Real) * x / Real.log x := by
        apply (div_lt_div_iff_of_pos_right hlogpos).2
        exact mul_lt_mul_of_pos_right ha1 hxpos
      nlinarith
  }

def DusartThetaTable66RowsCoverUpTo
    (rows : List DusartThetaTable66Row) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasDusartSymmetricThetaBoundsBelow_of_table66_rows
    {X : Real} {rows : List DusartThetaTable66Row}
    (cover : DusartThetaTable66RowsCoverUpTo rows X)
    (hleft : ∀ row ∈ rows, 2 ≤ row.left)
    (hle : ∀ row ∈ rows, row.left ≤ row.right)
    (hupper_error : ∀ row ∈ rows,
      row.b0 - 1 < (1 : Real) / 36260)
    (ha1_nonneg : ∀ row ∈ rows, 0 ≤ row.a1)
    (ha1 : ∀ row ∈ rows, row.a1 < (12323 : Real) / 10000) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_relative_rows (rows := rows)
  intro x hx hX
  obtain ⟨row, hrow, hleftx, hrightx⟩ := cover x hx hX
  refine ⟨row.toRelativeRow (hleft row hrow) (hle row hrow)
      (hupper_error row hrow) (ha1_nonneg row hrow) (ha1 row hrow),
    hrow, hleftx, hrightx⟩

def DusartThetaTable66IndexedCoverUpTo {n : Nat}
    (rows : Fin n → DusartThetaTable66Row) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧ x ≤ (rows i).right

theorem dusartThetaTable66IndexedCoverUpTo_of_list
    {X : Real} {rows : List DusartThetaTable66Row}
    (cover : DusartThetaTable66RowsCoverUpTo rows X) :
    DusartThetaTable66IndexedCoverUpTo
      (fun i : Fin rows.length => rows.get i) X := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hrow
  refine ⟨⟨i, hi⟩, ?_⟩
  simpa [List.get_eq_getElem, hget] using And.intro hleft hright

theorem dusartThetaTable66IndexedCoverUpTo_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → DusartThetaTable66Row}
    {right : Fin n₂ → DusartThetaTable66Row}
    (hleft : DusartThetaTable66IndexedCoverUpTo left m)
    (hright : DusartThetaTable66IndexedCoverUpTo right X) :
    DusartThetaTable66IndexedCoverUpTo (Fin.append left right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨i, hleft_lower, hleft_upper⟩ := hleft x hx hxm
    refine ⟨Fin.castAdd n₂ i, ?_, ?_⟩
    · simpa [Fin.append_left] using hleft_lower
    · simpa [Fin.append_left] using hleft_upper
  · obtain ⟨i, hright_lower, hright_upper⟩ := hright x hx hX
    refine ⟨Fin.natAdd n₁ i, ?_, ?_⟩
    · simpa [Fin.append_right] using hright_lower
    · simpa [Fin.append_right] using hright_upper

structure DusartThetaTable66Chunk where
  n : Nat
  cutoff : Real
  rows : Fin n → DusartThetaTable66Row
  cover : DusartThetaTable66IndexedCoverUpTo rows cutoff
  left_large : ∀ i, 2 ≤ (rows i).left
  left_le_right : ∀ i, (rows i).left ≤ (rows i).right
  upper_error : ∀ i, (rows i).b0 - 1 < (1 : Real) / 36260
  a1_nonneg : ∀ i, 0 ≤ (rows i).a1
  a1_bound : ∀ i, (rows i).a1 < (12323 : Real) / 10000

def DusartThetaTable66Chunk.of_list
    {rows : List DusartThetaTable66Row} {cutoff : Real}
    (cover : DusartThetaTable66RowsCoverUpTo rows cutoff)
    (left_large : ∀ row ∈ rows, 2 ≤ row.left)
    (left_le_right : ∀ row ∈ rows, row.left ≤ row.right)
    (upper_error : ∀ row ∈ rows,
      row.b0 - 1 < (1 : Real) / 36260)
    (a1_nonneg : ∀ row ∈ rows, 0 ≤ row.a1)
    (a1_bound : ∀ row ∈ rows,
      row.a1 < (12323 : Real) / 10000) :
    DusartThetaTable66Chunk :=
  { n := rows.length
    cutoff := cutoff
    rows := fun i => rows.get i
    cover := dusartThetaTable66IndexedCoverUpTo_of_list cover
    left_large := by
      intro i
      exact left_large (rows.get i) (List.get_mem rows i)
    left_le_right := by
      intro i
      exact left_le_right (rows.get i) (List.get_mem rows i)
    upper_error := by
      intro i
      exact upper_error (rows.get i) (List.get_mem rows i)
    a1_nonneg := by
      intro i
      exact a1_nonneg (rows.get i) (List.get_mem rows i)
    a1_bound := by
      intro i
      exact a1_bound (rows.get i) (List.get_mem rows i) }

def DusartThetaTable66Chunk.append
    (left right : DusartThetaTable66Chunk) : DusartThetaTable66Chunk :=
  { n := left.n + right.n
    cutoff := right.cutoff
    rows := Fin.append left.rows right.rows
    cover := dusartThetaTable66IndexedCoverUpTo_append
      left.cover right.cover
    left_large := by
      intro i
      induction i using Fin.addCases with
      | left j => simpa [Fin.append_left] using left.left_large j
      | right j => simpa [Fin.append_right] using right.left_large j
    left_le_right := by
      intro i
      induction i using Fin.addCases with
      | left j => simpa [Fin.append_left] using left.left_le_right j
      | right j => simpa [Fin.append_right] using right.left_le_right j
    upper_error := by
      intro i
      induction i using Fin.addCases with
      | left j => simpa [Fin.append_left] using left.upper_error j
      | right j => simpa [Fin.append_right] using right.upper_error j
    a1_nonneg := by
      intro i
      induction i using Fin.addCases with
      | left j => simpa [Fin.append_left] using left.a1_nonneg j
      | right j => simpa [Fin.append_right] using right.a1_nonneg j
    a1_bound := by
      intro i
      induction i using Fin.addCases with
      | left j => simpa [Fin.append_left] using left.a1_bound j
      | right j => simpa [Fin.append_right] using right.a1_bound j }

def DusartThetaTable66Chunk.appendMany
    (first : DusartThetaTable66Chunk)
    (rest : List DusartThetaTable66Chunk) : DusartThetaTable66Chunk :=
  match rest with
  | [] => first
  | next :: tail =>
      DusartThetaTable66Chunk.appendMany
        (DusartThetaTable66Chunk.append first next) tail

def DusartThetaTable66Chunk.toRelativeRows
    (chunk : DusartThetaTable66Chunk) :
    Fin chunk.n → DusartThetaRelativeRow :=
  fun i => (chunk.rows i).toRelativeRow
    (chunk.left_large i) (chunk.left_le_right i)
    (chunk.upper_error i) (chunk.a1_nonneg i) (chunk.a1_bound i)

theorem hasDusartSymmetricThetaBoundsBelow_of_table66_chunk
    (chunk : DusartThetaTable66Chunk) :
    HasDusartSymmetricThetaBoundsBelow chunk.cutoff := by
  apply hasDusartSymmetricThetaBoundsBelow_of_indexed_relative_rows
    (rows := chunk.toRelativeRows)
  intro x hx hX
  obtain ⟨i, hleft, hright⟩ := chunk.cover x hx hX
  refine ⟨i, ?_, ?_⟩
  · exact hleft
  · exact hright

theorem hasDusartSymmetricThetaBoundsBelow_of_table66_chunks
    (first : DusartThetaTable66Chunk)
    (rest : List DusartThetaTable66Chunk) :
    HasDusartSymmetricThetaBoundsBelow
      (DusartThetaTable66Chunk.appendMany first rest).cutoff := by
  induction rest generalizing first with
  | nil =>
      exact hasDusartSymmetricThetaBoundsBelow_of_table66_chunk first
  | cons next tail ih =>
      exact ih (DusartThetaTable66Chunk.append first next)

/-! The older two-coefficient projection is retained for data whose
constant-coefficient validity has already been established independently. -/
structure DusartThetaTableCoefficientRow where
  left : Nat
  right : Nat
  lower_coeff : Real
  upper_coeff : Real

def DusartThetaTable66CoefficientData.toCoefficientRow
    (data : DusartThetaTable66CoefficientData) :
    DusartThetaTableCoefficientRow :=
  { left := data.left
    right := data.right
    lower_coeff := data.a0
    upper_coeff := data.b0 }

def dusartThetaTable6_6Coefficients :
    List DusartThetaTableCoefficientRow :=
  dusartThetaTable6_6CoefficientData.map
    DusartThetaTable66CoefficientData.toCoefficientRow

theorem dusartThetaTable6_6Coefficients_length :
    dusartThetaTable6_6Coefficients.length = 34 := by
  simp [dusartThetaTable6_6Coefficients,
    dusartThetaTable6_6CoefficientData_length]

/-! The numerical endpoints are projected to a computationally decidable
representation before checking the table's shape.  This keeps the provenance
checks independent of the real-valued coefficient fields. -/
def dusartThetaTable6_6NatRanges : List (Nat × Nat) :=
  dusartThetaTable6_6CoefficientDataNatRanges

theorem dusartThetaTable6_6NatRanges_length :
    dusartThetaTable6_6NatRanges.length = 34 := by
  simp [dusartThetaTable6_6NatRanges, dusartThetaTable6_6Coefficients_length]

theorem dusartThetaTable6_6NatRanges_nonempty :
    ∀ range ∈ dusartThetaTable6_6NatRanges, range.1 ≤ range.2 := by
  decide

theorem dusartThetaTable6_6NatRanges_strictly_ordered :
    dusartThetaTable6_6NatRanges.Chain'
      (fun first second => first.1 < second.1) := by
  decide

theorem dusartThetaTable6_6NatRanges_adjacent :
    dusartThetaTable6_6NatRanges.Chain'
      (fun first second => first.2 = second.1) := by
  decide

theorem dusartThetaTable6_6NatRanges_cover :
    ∀ n : Nat, 100000000 ≤ n → n ≤ 800000000000 →
      ∃ range ∈ dusartThetaTable6_6NatRanges,
        range.1 ≤ n ∧ n ≤ range.2 := by
  intro n hn hN
  simp [dusartThetaTable6_6NatRanges,
    dusartThetaTable6_6CoefficientDataNatRanges]
  omega

theorem dusartThetaTable_upper_coeff_error_of_le_one
    {upper_coeff : Real} (hupper : upper_coeff ≤ 1) :
    upper_coeff - 1 < (1 : Real) / 36260 := by
  nlinarith

theorem dusartThetaTable_lower_coeff_error_of_minimum
    {lower_coeff x : Real}
    (hlower : (99985 : Real) / 100000 ≤ lower_coeff)
    (hx : 2 < x) (hxupper : x ≤ (8e11 : Real)) :
    (1 - lower_coeff) * x <
      (12323 / 10000 : Real) * x / Real.log x := by
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog : Real.log x < 30 := by
    exact (Real.log_le_log hxpos hxupper).trans_lt
      LogTables.log_eight_hundred_billion_lt_thirty
  have hratio : (15 : Real) / 100000 <
      (12323 / 10000 : Real) / Real.log x := by
    apply (lt_div_iff₀ hlogpos).2
    nlinarith
  have hscaled := mul_lt_mul_of_pos_right hratio hxpos
  have hcoeff : 1 - lower_coeff ≤ (15 : Real) / 100000 := by
    nlinarith
  have hscaled' := mul_le_mul_of_nonneg_right hcoeff hxpos.le
  calc
    (1 - lower_coeff) * x ≤ (15 : Real) / 100000 * x := hscaled'
    _ < ((12323 / 10000 : Real) / Real.log x) * x := hscaled
    _ = (12323 / 10000 : Real) * x / Real.log x := by ring

/-! The raw Table 6.6 coefficients already satisfy the numerical error
    margins required by the relative-row interface.  This lemma packages
    those margins independently of the still separate theta interval bounds. -/
theorem dusartThetaTable6_6CoefficientData_error_margins
    (row : DusartThetaTable66CoefficientData)
    (hrow : row ∈ dusartThetaTable6_6CoefficientData) :
    row.b0 - 1 < (1 : Real) / 36260 ∧
      ∀ x : Real, 2 < x → x ≤ (8e11 : Real) →
        (1 - row.a0) * x <
          (12323 / 10000 : Real) * x / Real.log x := by
  have hmeta := dusartThetaTable6_6CoefficientData_row_bounds row hrow
  rcases hmeta with ⟨_, _, _, hlower, hupper⟩
  constructor
  · exact dusartThetaTable_upper_coeff_error_of_le_one hupper
  · intro x hx hxupper
    exact dusartThetaTable_lower_coeff_error_of_minimum
      hlower hx hxupper

theorem dusartThetaTable6_6CoefficientData_error_margins_all :
    ∀ row ∈ dusartThetaTable6_6CoefficientData,
      row.b0 - 1 < (1 : Real) / 36260 ∧
        ∀ x : Real, 2 < x → x ≤ (8e11 : Real) →
          (1 - row.a0) * x <
            (12323 / 10000 : Real) * x / Real.log x := by
  intro row hrow
  exact dusartThetaTable6_6CoefficientData_error_margins row hrow

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

def DusartThetaTableCoefficientRow.toRelativeRow_of_table_bounds
    (row : DusartThetaTableCoefficientRow)
    (hleft : 2 ≤ row.left) (hle : row.left ≤ row.right)
    (hright_endpoint : (row.right : Real) ≤ (8e11 : Real))
    (hlower_min : (99985 : Real) / 100000 ≤ row.lower_coeff)
    (hupper_le : row.upper_coeff ≤ 1)
    (hlower : ∀ x : Real, (row.left : Real) ≤ x → x ≤ row.right →
      row.lower_coeff * x ≤ Chebyshev.theta x)
    (hupper : ∀ x : Real, (row.left : Real) ≤ x → x ≤ row.right →
      Chebyshev.theta x ≤ row.upper_coeff * x) :
    DusartThetaRelativeRow :=
  row.toRelativeRow hleft hle hlower hupper
    (dusartThetaTable_upper_coeff_error_of_le_one hupper_le)
    (fun x hx hleftx hrightx =>
      dusartThetaTable_lower_coeff_error_of_minimum hlower_min hx
        (hrightx.trans hright_endpoint))

/-! A table row becomes usable only after its numerical theta bounds have been
    proved.  Keeping those proofs with the row prevents the raw printed
    coefficients from being consumed as if they already certified theta. -/
structure DusartThetaTableVerifiedRow where
  data : DusartThetaTableCoefficientRow
  left_large : 2 ≤ data.left
  left_le_right : data.left ≤ data.right
  right_le_cutoff : (data.right : Real) ≤ (8e11 : Real)
  lower_coeff_min : (99985 : Real) / 100000 ≤ data.lower_coeff
  upper_coeff_le_one : data.upper_coeff ≤ 1
  lower_bound : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    data.lower_coeff * x ≤ Chebyshev.theta x
  upper_bound : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    Chebyshev.theta x ≤ data.upper_coeff * x

def DusartThetaTable66CoefficientData.toVerifiedRow
    (data : DusartThetaTable66CoefficientData)
    (hleft : 2 ≤ data.left)
    (hle : data.left ≤ data.right)
    (hright : (data.right : Real) ≤ (8e11 : Real))
    (hlower_min : (99985 : Real) / 100000 ≤ data.a0)
    (hupper_le : data.b0 ≤ 1)
    (lower_bound : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      data.a0 * x ≤ Chebyshev.theta x)
    (upper_bound : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ data.b0 * x) :
    DusartThetaTableVerifiedRow :=
  { data := data.toCoefficientRow
    left_large := hleft
    left_le_right := hle
    right_le_cutoff := hright
    lower_coeff_min := by
      simpa [DusartThetaTable66CoefficientData.toCoefficientRow] using hlower_min
    upper_coeff_le_one := by
      simpa [DusartThetaTable66CoefficientData.toCoefficientRow] using hupper_le
    lower_bound := by
      simpa [DusartThetaTable66CoefficientData.toCoefficientRow] using lower_bound
    upper_bound := by
      simpa [DusartThetaTable66CoefficientData.toCoefficientRow] using upper_bound }

def DusartThetaTable66CoefficientData.toVerifiedRow_of_table_bounds
    (data : DusartThetaTable66CoefficientData)
    (hdata : data ∈ dusartThetaTable6_6CoefficientData)
    (lower_bound : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      data.a0 * x ≤ Chebyshev.theta x)
    (upper_bound : ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
      Chebyshev.theta x ≤ data.b0 * x) :
    DusartThetaTableVerifiedRow := by
  have hmeta := dusartThetaTable6_6CoefficientData_row_bounds data hdata
  exact data.toVerifiedRow hmeta.1 hmeta.2.1 hmeta.2.2.1
    hmeta.2.2.2.1 hmeta.2.2.2.2.1 lower_bound upper_bound

def DusartThetaTableVerifiedRow.toRelativeRow
    (row : DusartThetaTableVerifiedRow) : DusartThetaRelativeRow :=
  row.data.toRelativeRow_of_table_bounds row.left_large row.left_le_right
    row.right_le_cutoff row.lower_coeff_min row.upper_coeff_le_one
    row.lower_bound row.upper_bound

def DusartThetaTableVerifiedRow.toStrictUpperRow
    (row : DusartThetaTableVerifiedRow)
    (hmargin : row.data.upper_coeff * (row.data.right : Real) <
      row.data.left) : StrictThetaUpperRow := by
  have hleft : (row.data.left : Real) ≤ (row.data.right : Real) := by
    exact_mod_cast row.left_le_right
  refine {
    left := row.data.left
    right := row.data.right
    left_large := row.left_large
    left_le_right := row.left_le_right
    theta_upper := row.data.upper_coeff * (row.data.right : Real)
    theta_right_le := ?_
    upper_error := ?_ }
  · exact row.upper_bound (row.data.right : Real) hleft le_rfl
  · exact sub_neg.mpr hmargin

def DusartThetaTableVerifiedRowsCoverUpTo
    (rows : List DusartThetaTableVerifiedRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.data.left : Real) ≤ x ∧ x ≤ row.data.right

def DusartThetaTableVerifiedStrictRowsCoverUpTo
    (rows : List DusartThetaTableVerifiedRow) (X : Real)
    (margin : ∀ row,
      row.data.upper_coeff * (row.data.right : Real) < row.data.left) : Prop :=
  StrictThetaUpperRowsCoverUpTo
    (rows.map fun row => row.toStrictUpperRow (margin row)) X

theorem hasStrictThetaUpperBelow_of_verified_table_rows
    {X : Real} {rows : List DusartThetaTableVerifiedRow}
    (cover : DusartThetaTableVerifiedRowsCoverUpTo rows X)
    (margin : ∀ row,
      row.data.upper_coeff * (row.data.right : Real) < row.data.left) :
    HasStrictThetaUpperBelow X := by
  apply hasStrictThetaUpperBelow_of_rows
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  let strictRow := row.toStrictUpperRow (margin row)
  refine ⟨strictRow, ?_, ?_, ?_⟩
  · exact List.mem_map.2 ⟨row, hrow, rfl⟩
  · simpa [strictRow, DusartThetaTableVerifiedRow.toStrictUpperRow] using hleft
  · simpa [strictRow, DusartThetaTableVerifiedRow.toStrictUpperRow] using hright

def DusartThetaTableVerifiedIndexedCoverUpTo {n : Nat}
    (rows : Fin n → DusartThetaTableVerifiedRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ i : Fin n, (rows i).data.left ≤ x ∧ x ≤ (rows i).data.right

theorem hasStrictThetaUpperBelow_of_indexed_verified_table_rows
    {n : Nat} {X : Real}
    {rows : Fin n → DusartThetaTableVerifiedRow}
    (cover : DusartThetaTableVerifiedIndexedCoverUpTo rows X)
    (margin : ∀ i,
      (rows i).data.upper_coeff * ((rows i).data.right : Real) <
        (rows i).data.left) :
    HasStrictThetaUpperBelow X := by
  let strictRows : Fin n → StrictThetaUpperRow :=
    fun i => (rows i).toStrictUpperRow (margin i)
  apply hasStrictThetaUpperBelow_of_indexed_rows (rows := strictRows)
  intro x hx hX
  obtain ⟨i, hleft, hright⟩ := cover x hx hX
  refine ⟨i, ?_, ?_⟩
  · simpa [strictRows, DusartThetaTableVerifiedRow.toStrictUpperRow] using hleft
  · simpa [strictRows, DusartThetaTableVerifiedRow.toStrictUpperRow] using hright

theorem dusartThetaTableVerifiedIndexedCoverUpTo_of_list
    {X : Real} {rows : List DusartThetaTableVerifiedRow}
    (cover : DusartThetaTableVerifiedRowsCoverUpTo rows X) :
    DusartThetaTableVerifiedIndexedCoverUpTo
      (fun i : Fin rows.length => rows.get i) X := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hrow
  refine ⟨⟨i, hi⟩, ?_⟩
  simpa [List.get_eq_getElem, hget] using And.intro hleft hright

theorem hasDusartSymmetricThetaBoundsBelow_of_verified_table_rows
  {X : Real} {rows : List DusartThetaTableVerifiedRow}
    (cover : DusartThetaTableVerifiedRowsCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_relative_rows
    (rows := rows.map DusartThetaTableVerifiedRow.toRelativeRow)
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  refine ⟨row.toRelativeRow, ?_, ?_, ?_⟩
  · exact List.mem_map.2 ⟨row, hrow, rfl⟩
  · simpa [DusartThetaTableVerifiedRow.toRelativeRow] using hleft
  · simpa [DusartThetaTableVerifiedRow.toRelativeRow] using hright

/-! Assemble the published Table 6.6 coefficient data after its two analytic
    endpoint inequalities have been proved.  The raw table remains data; only
    rows carrying both theta bounds are admitted to the provider. -/
theorem hasDusartSymmetricThetaBoundsBelow_of_table66_coefficient_bounds
    {X : Real}
    (cover : ∀ x : Real, 2 ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (lower : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        data.a0 * x ≤ Chebyshev.theta x)
    (upper : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ data.b0 * x) :
    HasDusartSymmetricThetaBoundsBelow X := by
  let rows : List DusartThetaTableVerifiedRow :=
    dusartThetaTable6_6CoefficientData.attach.map fun entry =>
      entry.1.toVerifiedRow_of_table_bounds entry.2
        (lower entry.1 entry.2) (upper entry.1 entry.2)
  apply hasDusartSymmetricThetaBoundsBelow_of_verified_table_rows
  intro x hx hX
  obtain ⟨data, hdata, hleft, hright⟩ := cover x hx hX
  refine ⟨data.toVerifiedRow_of_table_bounds hdata
      (lower data hdata) (upper data hdata), ?_, hleft, hright⟩
  change data.toVerifiedRow_of_table_bounds hdata
      (lower data hdata) (upper data hdata) ∈
    dusartThetaTable6_6CoefficientData.attach.map (fun entry =>
      entry.1.toVerifiedRow_of_table_bounds entry.2
        (lower entry.1 entry.2) (upper entry.1 entry.2))
  apply List.mem_map.2
  refine ⟨⟨data, hdata⟩, ?_, rfl⟩
  simp

/-! The full Table 6.6 interface.  A caller proving the six published
    interval inequalities can assemble the bounded theta estimate without
    first replacing the correction terms by constant endpoint bounds. -/
theorem hasDusartSymmetricThetaBoundsBelow_of_table66_formula_bounds
    {X : Real}
    (cover : ∀ x : Real, 2 ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (lower_zero : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        data.a0 * x ≤ Chebyshev.theta x)
    (upper_zero : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ data.b0 * x)
    (lower_one : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        x - data.a1 * x / Real.log x ≤ Chebyshev.theta x)
    (upper_one : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ x + data.b1 * x / Real.log x)
    (lower_two : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        x - data.a2 * x / Real.log x ^ 2 ≤ Chebyshev.theta x)
    (upper_two : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ x + data.b2 * x / Real.log x ^ 2) :
    HasDusartSymmetricThetaBoundsBelow X := by
  let rows : List DusartThetaRelativeRow :=
    dusartThetaTable6_6CoefficientData.attach.map fun entry =>
      entry.1.toRelativeRow_of_formula_bounds
        (dusartThetaTable6_6CoefficientData_row_bounds entry.1 entry.2).1
        (dusartThetaTable6_6CoefficientData_row_bounds entry.1 entry.2).2.1
        (dusartThetaTable_upper_coeff_error_of_le_one
          (dusartThetaTable6_6CoefficientData_row_bounds entry.1 entry.2).2.2.2.2)
        (dusartThetaTable6_6CoefficientData_side_conditions entry.1 entry.2).1
        (dusartThetaTable6_6CoefficientData_side_conditions entry.1 entry.2).2.1
        (lower_zero entry.1 entry.2) (upper_zero entry.1 entry.2)
        (lower_one entry.1 entry.2) (upper_one entry.1 entry.2)
        (lower_two entry.1 entry.2) (upper_two entry.1 entry.2)
  apply hasDusartSymmetricThetaBoundsBelow_of_relative_rows (rows := rows)
  intro x hx hX
  obtain ⟨data, hdata, hleft, hright⟩ := cover x hx hX
  let row := data.toRelativeRow_of_formula_bounds
    (dusartThetaTable6_6CoefficientData_row_bounds data hdata).1
    (dusartThetaTable6_6CoefficientData_row_bounds data hdata).2.1
    (dusartThetaTable_upper_coeff_error_of_le_one
      (dusartThetaTable6_6CoefficientData_row_bounds data hdata).2.2.2.2)
    (dusartThetaTable6_6CoefficientData_side_conditions data hdata).1
    (dusartThetaTable6_6CoefficientData_side_conditions data hdata).2.1
    (lower_zero data hdata) (upper_zero data hdata)
    (lower_one data hdata) (upper_one data hdata)
    (lower_two data hdata) (upper_two data hdata)
  refine ⟨row, ?_, hleft, hright⟩
  change row ∈ rows
  apply List.mem_map.2
  refine ⟨⟨data, hdata⟩, ?_, rfl⟩
  simp [rows]

/-! The bundled form is the preferred boundary for generated Table 6.6 data.
    A caller supplies one proof object per published coefficient row; the
    projections below are made once by this reusable assembler. -/
theorem hasDusartSymmetricThetaBoundsBelow_of_table66_formula_data
    {X : Real}
    (cover : ∀ x : Real, 2 ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (formula : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      DusartThetaTable66FormulaBounds data) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_table66_formula_bounds cover
  · intro data hdata
    exact (formula data hdata).lower_zero
  · intro data hdata
    exact (formula data hdata).upper_zero
  · intro data hdata
    exact (formula data hdata).lower_one
  · intro data hdata
    exact (formula data hdata).upper_one
  · intro data hdata
    exact (formula data hdata).lower_two
  · intro data hdata
      exact (formula data hdata).upper_two

theorem hasDusartSymmetricThetaBoundsBelow_of_table66_formula_data_with_constant_endpoints
    {X : Real}
    (cover : ∀ x : Real, 2 ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (lower_endpoint : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      data.a0 * (data.right : Real) ≤ Chebyshev.theta data.left)
    (upper_endpoint : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      Chebyshev.theta data.right ≤ data.b0 * (data.left : Real))
    (lower_one : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        x - data.a1 * x / Real.log x ≤ Chebyshev.theta x)
    (upper_one : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ x + data.b1 * x / Real.log x)
    (lower_two : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        x - data.a2 * x / Real.log x ^ 2 ≤ Chebyshev.theta x)
    (upper_two : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ x + data.b2 * x / Real.log x ^ 2) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_table66_formula_data cover
  intro data hdata
  refine {
    lower_zero := ?_
    upper_zero := ?_
    lower_one := lower_one data hdata
    upper_one := upper_one data hdata
    lower_two := lower_two data hdata
    upper_two := upper_two data hdata }
  · exact (dusartThetaTable66_constant_bounds_of_endpoints data
      (dusartThetaTable6_6CoefficientData_coefficients_nonneg data hdata).1
      (dusartThetaTable6_6CoefficientData_coefficients_nonneg data hdata).2
      (lower_endpoint data hdata) (upper_endpoint data hdata)).1
  · exact (dusartThetaTable66_constant_bounds_of_endpoints data
      (dusartThetaTable6_6CoefficientData_coefficients_nonneg data hdata).1
      (dusartThetaTable6_6CoefficientData_coefficients_nonneg data hdata).2
      (lower_endpoint data hdata) (upper_endpoint data hdata)).2

/-! The negative `b1` column also supplies the strict upper estimate used by
    Proposition 5.1.  This consumes the same bundled formula rows, so the
    strict prefix and the symmetric theta bounds cannot diverge. -/
theorem hasStrictThetaUpperBelow_of_table66_formula_data
    {X : Real}
    (cover : ∀ x : Real, 2 ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (formula : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      DusartThetaTable66FormulaBounds data) :
    HasStrictThetaUpperBelow X := by
  intro x hx hX
  by_cases hsmall : x < 2
  · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
    linarith
  · obtain ⟨data, hdata, hleft, hright⟩ := cover x
      (le_of_not_gt hsmall) hX
    exact strictThetaUpper_of_table66_formula_data data hdata
      (formula data hdata) hleft hright

theorem hasDusartSymmetricThetaBoundsBelow_of_prefix_and_table66_coefficient_bounds
    {x₀ X : Real} (h2x₀ : (2 : Real) ≤ x₀)
    (prefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (cover : ∀ x : Real, x₀ ≤ x → x ≤ X →
      ∃ data ∈ dusartThetaTable6_6CoefficientData,
        (data.left : Real) ≤ x ∧ x ≤ data.right)
    (lower : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        data.a0 * x ≤ Chebyshev.theta x)
    (upper : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ data.b0 * x) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact prefix.1 x hx hsmall
    · obtain ⟨data, hdata, hleft, hright⟩ := cover x
        (h2x₀.trans (le_of_not_ge hsmall)) hX
      let row := data.toVerifiedRow_of_table_bounds hdata
        (lower data hdata) (upper data hdata)
      exact (dusartThetaRelativeRow_provides row.toRelativeRow).upper
        x hleft hright
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact prefix.2 x hx hsmall
    · obtain ⟨data, hdata, hleft, hright⟩ := cover x
        (h2x₀.trans (le_of_not_ge hsmall)) hX
      let row := data.toVerifiedRow_of_table_bounds hdata
        (lower data hdata) (upper data hdata)
      exact (dusartThetaRelativeRow_provides row.toRelativeRow).lower
        x hx hleft hright

theorem hasDusartSymmetricThetaBoundsBelow_of_indexed_verified_table_rows
    {n : Nat} {X : Real} {rows : Fin n → DusartThetaTableVerifiedRow}
    (cover : DusartThetaTableVerifiedIndexedCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_indexed_relative_rows
  intro x hx hX
  obtain ⟨i, hleft, hright⟩ := cover x hx hX
  refine ⟨i, ?_⟩
  simpa [DusartThetaTableVerifiedRow.toRelativeRow] using
    And.intro hleft hright

theorem dusartThetaTableVerifiedRowsCoverUpTo_append
    {m X : Real} {left right : List DusartThetaTableVerifiedRow}
    (hleft : DusartThetaTableVerifiedRowsCoverUpTo left m)
    (hright : DusartThetaTableVerifiedRowsCoverUpTo right X) :
    DusartThetaTableVerifiedRowsCoverUpTo (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem dusartThetaTableVerifiedIndexedCoverUpTo_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → DusartThetaTableVerifiedRow}
    {right : Fin n₂ → DusartThetaTableVerifiedRow}
    (hleft : DusartThetaTableVerifiedIndexedCoverUpTo left m)
    (hright : DusartThetaTableVerifiedIndexedCoverUpTo right X) :
    DusartThetaTableVerifiedIndexedCoverUpTo (Fin.append left right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨i, hleft_lower, hleft_upper⟩ := hleft x hx hxm
    refine ⟨Fin.castAdd n₂ i, ?_⟩
    simpa [Fin.append_left] using And.intro hleft_lower hleft_upper
  · obtain ⟨i, hright_lower, hright_upper⟩ := hright x hx hX
    refine ⟨Fin.natAdd n₁ i, ?_⟩
    simpa [Fin.append_right] using And.intro hright_lower hright_upper

/-! The verified Table 6.4 rows can be supplied in compact indexed chunks.
    Adjacent generated bands are assembled here without duplicating their
    coverage proof or creating one declaration per endpoint. -/
structure DusartThetaTableVerifiedChunk where
  n : Nat
  cutoff : Real
  rows : Fin n → DusartThetaTableVerifiedRow
  cover : DusartThetaTableVerifiedIndexedCoverUpTo rows cutoff

def DusartThetaTableVerifiedChunk.of_list
    {rows : List DusartThetaTableVerifiedRow} {cutoff : Real}
    (cover : DusartThetaTableVerifiedRowsCoverUpTo rows cutoff) :
    DusartThetaTableVerifiedChunk :=
  { n := rows.length
    cutoff := cutoff
    rows := fun i => rows.get i
    cover := dusartThetaTableVerifiedIndexedCoverUpTo_of_list cover }

def DusartThetaTableVerifiedChunk.append
    (left right : DusartThetaTableVerifiedChunk) :
    DusartThetaTableVerifiedChunk :=
  { n := left.n + right.n
    cutoff := right.cutoff
    rows := Fin.append left.rows right.rows
    cover := dusartThetaTableVerifiedIndexedCoverUpTo_append
      left.cover right.cover }

def DusartThetaTableVerifiedChunk.appendMany
    (first : DusartThetaTableVerifiedChunk)
    (rest : List DusartThetaTableVerifiedChunk) :
    DusartThetaTableVerifiedChunk :=
  match rest with
  | [] => first
  | next :: tail =>
      DusartThetaTableVerifiedChunk.appendMany
        (DusartThetaTableVerifiedChunk.append first next) tail

theorem hasStrictThetaUpperBelow_of_verified_chunk
    (chunk : DusartThetaTableVerifiedChunk)
    (margin : ∀ i,
      (chunk.rows i).data.upper_coeff *
          ((chunk.rows i).data.right : Real) <
        (chunk.rows i).data.left) :
    HasStrictThetaUpperBelow chunk.cutoff := by
  exact hasStrictThetaUpperBelow_of_indexed_verified_table_rows
    chunk.cover margin

theorem hasStrictThetaUpperBelow_of_verified_chunks
    (first : DusartThetaTableVerifiedChunk)
    (rest : List DusartThetaTableVerifiedChunk)
    (margin : ∀ i,
      ((DusartThetaTableVerifiedChunk.appendMany first rest).rows i).data.upper_coeff *
          (((DusartThetaTableVerifiedChunk.appendMany first rest).rows i).data.right : Real) <
        ((DusartThetaTableVerifiedChunk.appendMany first rest).rows i).data.left) :
    HasStrictThetaUpperBelow
      (DusartThetaTableVerifiedChunk.appendMany first rest).cutoff := by
  exact hasStrictThetaUpperBelow_of_verified_chunk
    (DusartThetaTableVerifiedChunk.appendMany first rest) margin

theorem hasDusartSymmetricThetaBoundsBelow_of_verified_chunk
    (chunk : DusartThetaTableVerifiedChunk) :
    HasDusartSymmetricThetaBoundsBelow chunk.cutoff := by
  exact hasDusartSymmetricThetaBoundsBelow_of_indexed_verified_table_rows
    chunk.cover

theorem hasDusartSymmetricThetaBoundsBelow_of_verified_chunks
    (first : DusartThetaTableVerifiedChunk)
    (rest : List DusartThetaTableVerifiedChunk) :
    HasDusartSymmetricThetaBoundsBelow
      (DusartThetaTableVerifiedChunk.appendMany first rest).cutoff := by
  induction rest generalizing first with
  | nil =>
      exact hasDusartSymmetricThetaBoundsBelow_of_verified_chunk first
  | cons next tail ih =>
      exact ih (DusartThetaTableVerifiedChunk.append first next)

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

/-! Compact indexed chunks for the bounded prime-counting endpoint table. -/
structure DusartPrimeCountingEndpointChunk where
  n : Nat
  cutoff : Real
  rows : Fin n → DusartPrimeCountingEndpointRow
  cover : DusartPrimeCountingEndpointIndexedCoverFrom599 rows cutoff

def DusartPrimeCountingEndpointChunk.of_list
    {rows : List DusartPrimeCountingEndpointRow} {cutoff : Real}
    (cover : DusartPrimeCountingEndpointRowsCoverFrom599 rows cutoff) :
    DusartPrimeCountingEndpointChunk :=
  { n := rows.length
    cutoff := cutoff
    rows := fun i => rows.get i
    cover := dusartPrimeCountingEndpointIndexedCover_of_list cover }

def DusartPrimeCountingEndpointChunk.append
    (left right : DusartPrimeCountingEndpointChunk) :
    DusartPrimeCountingEndpointChunk :=
  { n := left.n + right.n
    cutoff := right.cutoff
    rows := Fin.append left.rows right.rows
    cover := dusartPrimeCountingEndpointIndexedCoverFrom599_append
      left.cover right.cover }

def DusartPrimeCountingEndpointChunk.appendMany
    (first : DusartPrimeCountingEndpointChunk)
    (rest : List DusartPrimeCountingEndpointChunk) :
    DusartPrimeCountingEndpointChunk :=
  match rest with
  | [] => first
  | next :: tail =>
      DusartPrimeCountingEndpointChunk.appendMany
        (DusartPrimeCountingEndpointChunk.append first next) tail

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

theorem hasDusartRealPrimeCountingBoundsBelow_of_endpoint_chunk
    (chunk : DusartPrimeCountingEndpointChunk)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow chunk.cutoff := by
  exact hasDusartRealPrimeCountingBoundsBelow_of_indexed_endpoint_rows
    chunk.cover smallUpper

theorem hasDusartRealPrimeCountingBoundsBelow_of_endpoint_chunks
    (first : DusartPrimeCountingEndpointChunk)
    (rest : List DusartPrimeCountingEndpointChunk)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow
      (DusartPrimeCountingEndpointChunk.appendMany first rest).cutoff := by
  induction rest generalizing first with
  | nil =>
      exact hasDusartRealPrimeCountingBoundsBelow_of_endpoint_chunk
        first smallUpper
  | cons next tail ih =>
      exact ih (DusartPrimeCountingEndpointChunk.append first next) smallUpper

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
