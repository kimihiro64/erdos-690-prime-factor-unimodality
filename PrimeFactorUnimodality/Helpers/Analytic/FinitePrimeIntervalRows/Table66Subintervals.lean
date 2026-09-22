import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Bounds

set_option autoImplicit false

/-! # Subinterval certificates for the six theta-table inequalities

One pair of rational theta enclosures is reused for all six columns on each
small cell. Coverage, not a whole-row endpoint comparison, transports the
verified cells across the published interval. No published decimal value is
assumed to be a theorem about theta.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-- Compact data shared by all six local comparisons. -/
structure DusartThetaTable66Cell where
  left : Nat
  right : Nat
  thetaLower : Rat
  thetaUpper : Rat

def DusartThetaTable66Cell.interval
    (cell : DusartThetaTable66Cell) (data : DusartThetaTable66CoefficientData) :
    DusartThetaTable66CoefficientData :=
  { data with left := cell.left, right := cell.right }

/-- The arithmetic obligations for one cell. Its theta enclosures must be
proved from the finite prime sum, independently of the published table. -/
structure DusartThetaTable66Cell.Valid
    (cell : DusartThetaTable66Cell) (data : DusartThetaTable66CoefficientData) : Prop where
  left_bound : data.left ≤ cell.left
  ordered : cell.left ≤ cell.right
  right_bound : cell.right ≤ data.right
  theta_lower : (cell.thetaLower : Real) ≤ Chebyshev.theta cell.left
  theta_upper : Chebyshev.theta cell.right ≤ (cell.thetaUpper : Real)
  lower_zero : data.a0 * cell.right ≤ (cell.thetaLower : Real)
  upper_zero : (cell.thetaUpper : Real) ≤ data.b0 * cell.left
  lower_one : cell.right - data.a1 * cell.right / Real.log cell.right ≤
    (cell.thetaLower : Real)
  upper_one : (cell.thetaUpper : Real) ≤
    cell.left + data.b1 * cell.left / Real.log cell.left
  lower_two : cell.right - data.a2 * cell.right / Real.log cell.right ^ 2 ≤
    (cell.thetaLower : Real)
  upper_two : (cell.thetaUpper : Real) ≤
    cell.left + data.b2 * cell.left / Real.log cell.left ^ 2

theorem DusartThetaTable66Cell.Valid.formulaBounds
    {cell : DusartThetaTable66Cell} {data : DusartThetaTable66CoefficientData}
    (valid : cell.Valid data) (hleft : 8 ≤ data.left)
    (hzero : 0 ≤ data.a0 ∧ 0 ≤ data.b0)
    (hcoeff : 0 ≤ data.a1 ∧ data.a1 ≤ 1 ∧ -1 ≤ data.b1 ∧ data.b1 ≤ 0 ∧
      0 ≤ data.a2 ∧ data.a2 ≤ 1 ∧ -1 ≤ data.b2 ∧ data.b2 ≤ 0) :
    DusartThetaTable66FormulaBounds (cell.interval data) := by
  have hl : (8 : Real) ≤ cell.left := by
    exact_mod_cast hleft.trans valid.left_bound
  have hconstant := dusartThetaTable66_constant_bounds_of_endpoints
    (cell.interval data) hzero.1 hzero.2
    (valid.lower_zero.trans valid.theta_lower)
    (valid.theta_upper.trans valid.upper_zero)
  exact dusartThetaTable66_formula_bounds_of_endpoints
    (cell.interval data) valid.ordered (by dsimp [interval]; linarith)
    (log_ge_two_of_eight_le hl) hconstant.1 hconstant.2 hcoeff
    (valid.lower_one.trans valid.theta_lower)
    (valid.theta_upper.trans valid.upper_one)
    (valid.lower_two.trans valid.theta_lower)
    (valid.theta_upper.trans valid.upper_two)

def DusartThetaTable66CellsCover (data : DusartThetaTable66CoefficientData)
    (cells : List DusartThetaTable66Cell) : Prop :=
  ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
    ∃ cell ∈ cells, (cell.left : Real) ≤ x ∧ x ≤ cell.right

/-- A computable coverage check; adjacent cells must share an endpoint. -/
def dusartThetaTable66CellsChain (left right : Nat) : List DusartThetaTable66Cell → Bool
  | [] => false
  | [cell] => (cell.left == left) && (cell.right == right) && decide (cell.left ≤ cell.right)
  | cell :: next :: rest => (cell.left == left) && decide (cell.left ≤ cell.right) &&
      dusartThetaTable66CellsChain cell.right right (next :: rest)

theorem dusartThetaTable66CellsChain_covers
    {cells : List DusartThetaTable66Cell} {left right : Nat}
    (chain : dusartThetaTable66CellsChain left right cells = true)
    {x : Real} (hx : (left : Real) ≤ x) (hy : x ≤ right) :
    ∃ cell ∈ cells, (cell.left : Real) ≤ x ∧ x ≤ cell.right := by
  induction cells generalizing left with
  | nil => simp [dusartThetaTable66CellsChain] at chain
  | cons cell rest ih =>
    cases rest with
    | nil =>
      simp only [dusartThetaTable66CellsChain, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq] at chain
      exact ⟨cell, by simp, by simpa only [chain.1.1] using hx,
        by simpa only [chain.1.2] using hy⟩
    | cons next rest =>
      simp only [dusartThetaTable66CellsChain, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq] at chain
      by_cases hcell : x ≤ cell.right
      · exact ⟨cell, by simp, by simpa only [chain.1.1] using hx, hcell⟩
      · obtain ⟨found, hfound, hfx, hxf⟩ := ih chain.2 (le_of_not_ge hcell)
        exact ⟨found, List.mem_cons_of_mem _ hfound, hfx, hxf⟩

theorem dusartThetaTable66CellsCover_of_chain
    {data : DusartThetaTable66CoefficientData} {cells : List DusartThetaTable66Cell}
    (chain : dusartThetaTable66CellsChain data.left data.right cells = true) :
    DusartThetaTable66CellsCover data cells := by
  intro x hx hy
  exact dusartThetaTable66CellsChain_covers chain hx hy

/-- Reuse the local six-column proof at the cell containing the argument. -/
theorem dusartThetaTable66_formula_bounds_of_cells
    {data : DusartThetaTable66CoefficientData} {cells : List DusartThetaTable66Cell}
    (hleft : 8 ≤ data.left) (hzero : 0 ≤ data.a0 ∧ 0 ≤ data.b0)
    (hcoeff : 0 ≤ data.a1 ∧ data.a1 ≤ 1 ∧ -1 ≤ data.b1 ∧ data.b1 ≤ 0 ∧
      0 ≤ data.a2 ∧ data.a2 ≤ 1 ∧ -1 ≤ data.b2 ∧ data.b2 ≤ 0)
    (cover : DusartThetaTable66CellsCover data cells)
    (valid : ∀ cell ∈ cells, cell.Valid data) :
    DusartThetaTable66FormulaBounds data := by
  constructor <;> intro x hx hy <;>
    obtain ⟨cell, hcell, hcx, hxc⟩ := cover x hx hy
  · exact ((valid cell hcell).formulaBounds hleft hzero hcoeff).lower_zero x hcx hxc
  · exact ((valid cell hcell).formulaBounds hleft hzero hcoeff).upper_zero x hcx hxc
  · exact ((valid cell hcell).formulaBounds hleft hzero hcoeff).lower_one x hcx hxc
  · exact ((valid cell hcell).formulaBounds hleft hzero hcoeff).upper_one x hcx hxc
  · exact ((valid cell hcell).formulaBounds hleft hzero hcoeff).lower_two x hcx hxc
  · exact ((valid cell hcell).formulaBounds hleft hzero hcoeff).upper_two x hcx hxc

/-- The old first-row endpoint obligations contradicted each other, without
needing any unproved numerical value of theta. Subdivision is essential. -/
theorem dusartTable66_first_row_whole_endpoint_impossible :
    ¬ (Chebyshev.theta (100000000 : Real) ≤ (99998 / 100000 : Real) * 100000000 ∧
      (200000000 : Real) - (275 / 100000 : Real) * 200000000 /
        Real.log 200000000 ≤ Chebyshev.theta (100000000 : Real)) := by
  rintro ⟨upper, lower⟩
  have hl : (1 : Real) ≤ Real.log 200000000 :=
    (by norm_num : (1 : Real) ≤ 2).trans (log_ge_two_of_eight_le (by norm_num))
  have hc : (550000 : Real) / Real.log 200000000 ≤ 550000 :=
    div_le_self (by norm_num) hl
  norm_num at upper lower
  linarith

end

end PrimeFactorUnimodality
