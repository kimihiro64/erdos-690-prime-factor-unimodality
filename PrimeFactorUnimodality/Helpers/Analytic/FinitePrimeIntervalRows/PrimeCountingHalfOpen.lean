import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingCertificates

set_option autoImplicit false

/-! # Half-open prime-counting rows

On `[left, right)` the upper count is `pi(right - 1)`. This avoids charging
the jump at a prime right endpoint to the preceding interval. Smooth integer
powers certify the logarithms; exact endpoint counts are supplied separately.
-/

namespace PrimeFactorUnimodality

/-- A compact interval with its two count and logarithm witnesses. -/
structure DusartHalfOpenPiRow where
  left : Nat
  right : Nat
  leftCount : Nat
  beforeRightCount : Nat
  lowerPower : DusartSmoothLogPower
  upperPower : DusartSmoothLogPower

/-- Only rational and integer comparisons occur in this local margin check. -/
def DusartHalfOpenPiRow.checkMargins (row : DusartHalfOpenPiRow) : Bool :=
  decide (599 ≤ row.left ∧ row.left < row.right ∧
    0 < row.lowerPower.s ∧ 0 < row.upperPower.s ∧ 0 < row.lowerPower.lower ∧
    row.lowerPower.value ≤ row.right ^ row.lowerPower.s ∧
    row.left ^ row.upperPower.s ≤ row.upperPower.value ∧
    (row.right : Rat) / row.lowerPower.lower * (1 + 1 / row.lowerPower.lower) ≤
      row.leftCount ∧
    (row.beforeRightCount : Rat) ≤
      row.left / row.upperPower.upper * (1 + (6381 / 5000 : Rat) / row.upperPower.upper))

/-- The existing adjacent-cell checker also describes half-open partitions. -/
def DusartHalfOpenPiRow.coverageCell (row : DusartHalfOpenPiRow) : DusartThetaTable66Cell :=
  ⟨row.left, row.right, 0, 0⟩

/-- Both desired inequalities on a half-open interval, including its left endpoint. -/
def DusartHalfOpenPiBounds (left right : Nat) : Prop :=
  ∀ x : Real, (left : Real) ≤ x → x < right →
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real) ∧
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x

/-- Exact counts turn the checked rational margins into real-variable bounds. -/
theorem DusartHalfOpenPiRow.provides (row : DusartHalfOpenPiRow)
    (countLeft : Nat.primeCounting row.left = row.leftCount)
    (countBefore : Nat.primeCounting (row.right - 1) = row.beforeRightCount)
    (valid : row.checkMargins = true) : DusartHalfOpenPiBounds row.left row.right := by
  simp only [checkMargins, decide_eq_true_eq] at valid
  rcases valid with ⟨hl, ho, hsl, hsu, hL, hpl, hpu, hlo, hup⟩
  have lowerEndpoint : dusartPiLower row.right ≤ (Nat.primeCounting row.left : Real) := by
    rw [countLeft]
    apply dusartPiLower_le_of_log_lower (Nat.cast_nonneg _) (by exact_mod_cast hL)
      (row.lowerPower.lower_le_log hsl hpl)
    exact_mod_cast hlo
  have upperEndpoint : (Nat.primeCounting (row.right - 1) : Real) ≤
      dusartPiUpper row.left := by
    rw [countBefore]
    have hlog : 0 < Real.log (row.left : Real) :=
      Real.log_pos (by exact_mod_cast (show 1 < row.left by omega))
    apply le_dusartPiUpper_of_log_upper (Nat.cast_nonneg _) hlog
      (row.upperPower.log_le_upper (by omega) hsu hpu)
    have castUpper := Rat.cast_mono (K := Real) hup
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one] using castUpper
  intro x hleft hright
  have hl599 : (599 : Real) ≤ row.left := by exact_mod_cast hl
  have hr599 : (599 : Real) ≤ row.right := by exact_mod_cast (hl.trans ho.le)
  have hfloorLeft : row.left ≤ ⌊x⌋₊ := Nat.le_floor hleft
  have hfloorLt : ⌊x⌋₊ < row.right :=
    (Nat.floor_lt ((Nat.cast_nonneg row.left).trans hleft)).mpr hright
  have hfloorBefore : ⌊x⌋₊ ≤ row.right - 1 := by omega
  have piLeft : (Nat.primeCounting row.left : Real) ≤ Nat.primeCounting ⌊x⌋₊ := by
    exact_mod_cast Nat.monotone_primeCounting hfloorLeft
  have piBefore : (Nat.primeCounting ⌊x⌋₊ : Real) ≤ Nat.primeCounting (row.right - 1) := by
    exact_mod_cast Nat.monotone_primeCounting hfloorBefore
  constructor
  · exact (dusartPiLower_monotoneOn (hl599.trans hleft) hr599 hright.le).trans
      (lowerEndpoint.trans piLeft)
  · exact piBefore.trans (upperEndpoint.trans
      (dusartPiUpper_monotoneOn (by change (10 : Real) ≤ row.left; linarith)
        (by change (10 : Real) ≤ x; linarith) hleft))

/-- Shared endpoints belong to the next cell; the final right endpoint is excluded. -/
theorem dusartThetaTable66CellsChain_covers_halfOpen
    {cells : List DusartThetaTable66Cell} {left right : Nat}
    (chain : dusartThetaTable66CellsChain left right cells = true)
    {x : Real} (hx : (left : Real) ≤ x) (hy : x < right) :
    ∃ cell ∈ cells, (cell.left : Real) ≤ x ∧ x < cell.right := by
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
      by_cases hcell : x < cell.right
      · exact ⟨cell, by simp, by simpa only [chain.1.1] using hx, hcell⟩
      · obtain ⟨found, hfound, hfx, hxf⟩ := ih chain.2 (le_of_not_gt hcell)
        exact ⟨found, List.mem_cons_of_mem _ hfound, hfx, hxf⟩

/-- Reuse each checked row over its whole real interval. -/
theorem dusartHalfOpenPiRows_provide {left right : Nat} (rows : List DusartHalfOpenPiRow)
    (valid : ∀ row ∈ rows, DusartHalfOpenPiBounds row.left row.right)
    (chain : dusartThetaTable66CellsChain left right
      (rows.map DusartHalfOpenPiRow.coverageCell) = true) : DusartHalfOpenPiBounds left right := by
  intro x hx hy
  obtain ⟨cell, hcell, hleft, hright⟩ := dusartThetaTable66CellsChain_covers_halfOpen chain hx hy
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hcell
  exact valid row hrow x hleft hright

/-- Adjacent checked batches compose without a gap or a double-counted boundary. -/
theorem DusartHalfOpenPiBounds.append {left middle right : Nat}
    (first : DusartHalfOpenPiBounds left middle)
    (second : DusartHalfOpenPiBounds middle right) : DusartHalfOpenPiBounds left right := by
  intro x hx hy
  by_cases hm : x < middle
  · exact first x hx hm
  · exact second x (le_of_not_gt hm) hy

/-- Preserve the closed small prefix; the extra right endpoint includes every
real input through the requested natural cutoff. -/
theorem hasDusartRealPrimeCountingBoundsBelow_of_halfOpen {N : Nat}
    (initial : HasDusartRealPrimeCountingBoundsBelow 1000)
    (suffix : DusartHalfOpenPiBounds 1000 (N + 1)) :
    HasDusartRealPrimeCountingBoundsBelow N := by
  have hN : (N : Real) < (N + 1 : Nat) := by exact_mod_cast Nat.lt_succ_self N
  constructor
  · intro x hx hX
    by_cases small : x ≤ 1000
    · exact initial.1 x hx small
    · exact (suffix x (le_of_not_ge small) (hX.trans_lt hN)).1
  · intro x hx hX
    by_cases small : x ≤ 1000
    · exact initial.2 x hx small
    · exact (suffix x (le_of_not_ge small) (hX.trans_lt hN)).2

end PrimeFactorUnimodality
