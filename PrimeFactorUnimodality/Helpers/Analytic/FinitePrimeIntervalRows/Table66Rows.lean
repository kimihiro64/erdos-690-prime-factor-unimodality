import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Data
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.ThetaEndpointRows

set_option autoImplicit false

/-! # Table66Rows

Six-column theta rows and reusable indexed chunk composition.
-/

namespace PrimeFactorUnimodality

noncomputable section

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
    (hupper_error : row.b0 ≤ 1)
    (hlower_error : ∀ x : Real, 2 < x → (row.left : Real) ≤ x →
      x ≤ row.right →
      (1 - row.a0) * x <
        (12323 / 10000 : Real) * x / Real.log x) :
    DusartThetaRelativeRow :=
  DusartThetaRelativeRow.of_coefficients hleft_large hleft_right hupper_error
    row.lower_zero row.upper_zero hlower_error

def dusartThetaTable66Row_provides_zero
    (row : DusartThetaTable66Row)
    (hleft_large : 2 ≤ row.left)
    (hleft_right : row.left ≤ row.right)
    (hupper_error : row.b0 ≤ 1)
    (hlower_error : ∀ x : Real, 2 < x → (row.left : Real) ≤ x →
      x ≤ row.right →
      (1 - row.a0) * x <
        (12323 / 10000 : Real) * x / Real.log x) :
    DusartThetaBoundsRow := by
  exact dusartThetaRelativeRow_provides
    (row.toRelativeZero hleft_large hleft_right hupper_error hlower_error)


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
def DusartThetaTable66Row.toRelativeRow
    (row : DusartThetaTable66Row)
    (hleft : 2 ≤ row.left) (hle : row.left ≤ row.right)
    (hupper_error : row.b0 ≤ 1)
    (_ha1_nonneg : 0 ≤ row.a1)
    (ha1 : row.a1 < (12323 : Real) / 10000) :
    DusartThetaRelativeRow := by
  let data : DusartThetaTable66CoefficientData :=
    ⟨row.left, row.right, row.a0, row.b0, row.a1, row.b1, row.a2, row.b2⟩
  let formula : DusartThetaTable66FormulaBounds data :=
    ⟨row.lower_zero, row.upper_zero, row.lower_one, row.upper_one,
      row.lower_two, row.upper_two⟩
  exact formula.toRelativeRow hleft hle hupper_error ha1

def DusartThetaTable66CoefficientData.toRelativeRow_of_formula_bounds
    (data : DusartThetaTable66CoefficientData)
    (hleft : 2 ≤ data.left) (hle : data.left ≤ data.right)
    (hupper_error : data.b0 ≤ 1)
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

def DusartThetaTable66RowsCoverUpTo
    (rows : List DusartThetaTable66Row) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasDusartSymmetricThetaBoundsBelow_of_table66_rows
    {X : Real} {rows : List DusartThetaTable66Row}
    (cover : DusartThetaTable66RowsCoverUpTo rows X)
    (hleft : ∀ row ∈ rows, 2 ≤ row.left)
    (hle : ∀ row ∈ rows, row.left ≤ row.right)
    (hupper_error : ∀ row ∈ rows, row.b0 ≤ 1)
    (ha1_nonneg : ∀ row ∈ rows, 0 ≤ row.a1)
    (ha1 : ∀ row ∈ rows, row.a1 < (12323 : Real) / 10000) :
    HasDusartSymmetricThetaBoundsBelow X := by
  let converted := rows.attach.map fun entry =>
    entry.1.toRelativeRow (hleft entry.1 entry.2) (hle entry.1 entry.2)
      (hupper_error entry.1 entry.2) (ha1_nonneg entry.1 entry.2) (ha1 entry.1 entry.2)
  apply hasDusartSymmetricThetaBoundsBelow_of_relative_rows (rows := converted)
  intro x hx hX
  obtain ⟨row, hrow, hleftx, hrightx⟩ := cover x hx hX
  refine ⟨row.toRelativeRow (hleft row hrow) (hle row hrow)
      (hupper_error row hrow) (ha1_nonneg row hrow) (ha1 row hrow),
    ?_, hleftx, hrightx⟩
  exact List.mem_map.mpr ⟨⟨row, hrow⟩, List.mem_attach _ _, rfl⟩

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
  upper_error : ∀ i, (rows i).b0 ≤ 1
  a1_nonneg : ∀ i, 0 ≤ (rows i).a1
  a1_bound : ∀ i, (rows i).a1 < (12323 : Real) / 10000

def DusartThetaTable66Chunk.of_list
    {rows : List DusartThetaTable66Row} {cutoff : Real}
    (cover : DusartThetaTable66RowsCoverUpTo rows cutoff)
    (left_large : ∀ row ∈ rows, 2 ≤ row.left)
    (left_le_right : ∀ row ∈ rows, row.left ≤ row.right)
    (upper_error : ∀ row ∈ rows, row.b0 ≤ 1)
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

end

end PrimeFactorUnimodality
