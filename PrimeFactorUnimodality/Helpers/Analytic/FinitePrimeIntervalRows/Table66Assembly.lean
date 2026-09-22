import PrimeFactorUnimodality.Helpers.Analytic.ElementaryLogBounds
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Rows

set_option autoImplicit false

/-! # Table66Assembly

Constant-column margins and finite-prefix assembly for the published theta table.
-/

namespace PrimeFactorUnimodality

noncomputable section

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
  exact dusartThetaTable6_6CoefficientDataNatRanges_length

theorem dusartThetaTable6_6NatRanges_nonempty :
    ∀ range ∈ dusartThetaTable6_6NatRanges, range.1 ≤ range.2 := by
  decide

theorem dusartThetaTable6_6NatRanges_strictly_ordered :
    dusartThetaTable6_6NatRanges.IsChain
      (fun first second => first.1 < second.1) := by
  decide

theorem dusartThetaTable6_6NatRanges_adjacent :
    dusartThetaTable6_6NatRanges.IsChain
      (fun first second => first.2 = second.1) := by
  decide

theorem dusartThetaTable6_6NatRanges_cover :
    ∀ n : Nat, 100000000 ≤ n → n ≤ 800000000000 →
      ∃ range ∈ dusartThetaTable6_6NatRanges,
        range.1 ≤ n ∧ n ≤ range.2 := by
  exact dusartThetaTable6_6CoefficientDataNatRanges_cover

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
    (hupper_error : row.upper_coeff ≤ 1)
    (hlower_error : ∀ x : Real, 2 < x → (row.left : Real) ≤ x →
      x ≤ row.right →
      (1 - row.lower_coeff) * x <
        (12323 / 10000 : Real) * x / Real.log x) :
    DusartThetaRelativeRow :=
  DusartThetaRelativeRow.of_coefficients hleft hle hupper_error hlower hupper hlower_error

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
    hupper_le
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
    hmeta.2.2.2.1 hmeta.2.2.2.2 lower_bound upper_bound

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
    (margin : ∀ row : DusartThetaTableVerifiedRow,
      row.data.upper_coeff * (row.data.right : Real) < row.data.left) : Prop :=
  StrictThetaUpperRowsCoverUpTo
    (rows.map fun row => row.toStrictUpperRow (margin row)) X

theorem hasStrictThetaUpperBelow_of_verified_table_rows
    {X : Real} {rows : List DusartThetaTableVerifiedRow}
    (cover : DusartThetaTableVerifiedRowsCoverUpTo rows X)
    (margin : ∀ row : DusartThetaTableVerifiedRow,
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
  · exact hleft
  · exact hright

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
        (dusartThetaTable6_6CoefficientData_row_bounds entry.1 entry.2).2.2.2.2
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
    (dusartThetaTable6_6CoefficientData_row_bounds data hdata).2.2.2.2
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

theorem hasDusartSymmetricThetaBoundsBelow_of_table66_published_endpoints
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
    (lower_one_endpoint : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      data.right - data.a1 * data.right / Real.log data.right ≤
        Chebyshev.theta data.left)
    (upper_one_endpoint : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      Chebyshev.theta data.right ≤
        data.left + data.b1 * data.left / Real.log data.left)
    (lower_two_endpoint : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      data.right - data.a2 * data.right / Real.log data.right ^ 2 ≤
        Chebyshev.theta data.left)
    (upper_two_endpoint : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      Chebyshev.theta data.right ≤
        data.left + data.b2 * data.left / Real.log data.left ^ 2) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_table66_formula_data cover
  intro data hdata
  exact dusartThetaTable66_formula_bounds_of_published_endpoints hdata
    (lower_zero data hdata) (upper_zero data hdata)
    (lower_one_endpoint data hdata) (upper_one_endpoint data hdata)
    (lower_two_endpoint data hdata) (upper_two_endpoint data hdata)

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
    (hprefix : HasDusartSymmetricThetaBoundsBelow x₀)
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
    · exact hprefix.1 x (by linarith) hsmall
    · obtain ⟨data, hdata, hleft, hright⟩ := cover x (le_of_not_ge hsmall) hX
      let row := data.toVerifiedRow_of_table_bounds hdata
        (lower data hdata) (upper data hdata)
      exact (dusartThetaRelativeRow_provides row.toRelativeRow).upper
        x hleft hright
  · intro x hx hX
    by_cases hsmall : x ≤ x₀
    · exact hprefix.2 x hx hsmall
    · obtain ⟨data, hdata, hleft, hright⟩ := cover x (le_of_not_ge hsmall) hX
      let row := data.toVerifiedRow_of_table_bounds hdata
        (lower data hdata) (upper data hdata)
      exact (dusartThetaRelativeRow_provides row.toRelativeRow).lower
        x hx hleft hright

theorem hasDusartSymmetricThetaBoundsBelow_of_indexed_verified_table_rows
    {n : Nat} {X : Real} {rows : Fin n → DusartThetaTableVerifiedRow}
    (cover : DusartThetaTableVerifiedIndexedCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_indexed_relative_rows
    (rows := fun i => (rows i).toRelativeRow)
  intro x hx hX
  obtain ⟨i, hleft, hright⟩ := cover x hx hX
  refine ⟨i, ?_⟩
  exact ⟨hleft, hright⟩

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
    upper_coeff_le_one := ?_
    lower_error := ?_ }
  · intro x hleft hright
    norm_num at hleft hright
    have hx : x = 2 := by linarith
    subst x
    dsimp [c]
    nlinarith
  · intro x hleft hright
    norm_num at hleft hright
    have hx : x = 2 := by linarith
    subst x
    dsimp [c]
    nlinarith
  · dsimp [c]
    rw [theta_two_eq_log_two]
    nlinarith [Real.log_two_lt_d9]
  · intro x hx hleft hright
    norm_num at hleft hright
    linarith

theorem dusartThetaRelativeRow_two_cover :
    DusartThetaRelativeRowsCoverUpTo [dusartThetaRelativeRow_two] 2 := by
  intro x hx hX
  refine ⟨dusartThetaRelativeRow_two, by simp, ?_, ?_⟩
  · simpa only [dusartThetaRelativeRow_two, Nat.cast_ofNat] using hx
  · simpa only [dusartThetaRelativeRow_two, Nat.cast_ofNat] using hX

end

end PrimeFactorUnimodality
