import PrimeCert.SieveCorrect
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingHalfOpen

set_option autoImplicit false

/-! # Sieve-backed half-open short-interval rows

One checked prime covers every real input to its left in the row. A smooth
power bounds its logarithm, leaving an exact rational width comparison.
Adjacent rows assign a prime boundary to the next witness, preserving strict
prime existence above the input without repeating primality calculations.
-/

namespace PrimeFactorUnimodality

/-- A left endpoint, a prime witness, its wheel index and a logarithm witness. -/
structure DusartShortSieveRow where
  left : Nat
  prime : Nat
  index : Nat
  logPower : DusartSmoothLogPower

/-- Integer and rational checks for primality, range and the complete width budget. -/
def DusartShortSieveRow.check (row : DusartShortSieveRow) (N bits : Nat) : Bool :=
  decide (3275 ≤ row.left ∧ row.left < row.prime ∧ row.prime ≤ N ∧ 0 < row.index ∧
    PrimeCert.Sieve.num row.index = row.prime ∧ bits.testBit row.index = true ∧
    0 < row.logPower.s ∧ 0 < row.logPower.upper ∧
    row.prime ^ row.logPower.s ≤ row.logPower.value ∧
    ((row.prime : Rat) - row.left) * (2 * row.logPower.upper ^ 2) ≤ row.left)

/-- A witness at the right endpoint covers only inputs strictly below it. -/
def DusartShortSieveRow.coverageCell (row : DusartShortSieveRow) : DusartThetaTable66Cell :=
  ⟨row.left, row.prime, 0, 0⟩

/-- The desired real-variable short-interval statement on a half-open interval. -/
def DusartHalfOpenShortBounds (left right : Nat) : Prop :=
  ∀ x : Real, (left : Real) ≤ x → x < right →
    ∃ q : Nat, q.Prime ∧ x < q ∧
      (q : Real) ≤ x * (1 + 1 / (2 * (Real.log x) ^ 2))

/-- An accepted row provides the actual prime, not merely a count or an approximate bound. -/
theorem DusartShortSieveRow.provides (row : DusartShortSieveRow)
    {N bits : Nat} (sieve : PrimeCert.Sieve.IsSieve N bits)
    (valid : row.check N bits = true) : DusartHalfOpenShortBounds row.left row.prime := by
  simp only [check, decide_eq_true_eq] at valid
  rcases valid with ⟨hleft, hlt, hN, hi, hnum, hbit, hs, hL, hpower, hproduct⟩
  have hprime : row.prime.Prime := by
    have hp := (sieve row.index (by omega) (by simpa only [hnum] using hN)).mp hbit
    simpa only [hnum] using hp
  have hlogPrime := row.logPower.log_le_upper (show 0 < row.prime by omega) hs hpower
  have product : ((row.prime : Real) - row.left) *
      (2 * (row.logPower.upper : Real) ^ 2) ≤ row.left := by exact_mod_cast hproduct
  have hlarge : (3275 : Real) ≤ row.left := by exact_mod_cast hleft
  intro x hx hy
  refine ⟨row.prime, hprime, hy, ?_⟩
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx : Real.log x ≤ (row.logPower.upper : Real) :=
    (Real.log_le_log hxpos hy.le).trans hlogPrime
  have hdenL : 0 < 2 * (row.logPower.upper : Real) ^ 2 := by
    have : (0 : Real) < row.logPower.upper := by exact_mod_cast hL
    positivity
  have hden : 0 < 2 * (Real.log x) ^ 2 := by positivity
  have hsq : 2 * (Real.log x) ^ 2 ≤ 2 * (row.logPower.upper : Real) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogpos.le hlogx 2) (by norm_num)
  have gap := (le_div_iff₀ hdenL).mpr product
  have step : (row.left : Real) / (2 * (row.logPower.upper : Real) ^ 2) ≤
      x / (2 * (Real.log x) ^ 2) :=
    (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden hsq).trans
      (div_le_div_of_nonneg_right hx hden.le)
  calc
    (row.prime : Real) ≤ x + x / (2 * (Real.log x) ^ 2) := by linarith
    _ = x * (1 + 1 / (2 * (Real.log x) ^ 2)) := by ring

/-- Reuse each checked prime over its whole interval and compose gap-free coverage. -/
theorem dusartShortSieveRows_provide {N bits left right : Nat}
    (sieve : PrimeCert.Sieve.IsSieve N bits) (rows : List DusartShortSieveRow)
    (valid : rows.all (fun row => row.check N bits) = true)
    (chain : dusartThetaTable66CellsChain left right
      (rows.map DusartShortSieveRow.coverageCell) = true) :
    DusartHalfOpenShortBounds left right := by
  intro x hx hy
  obtain ⟨cell, hcell, hleft, hright⟩ := dusartThetaTable66CellsChain_covers_halfOpen chain hx hy
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hcell
  exact row.provides sieve (List.all_eq_true.mp valid row hrow) x hleft hright

/-- Adjacent batches preserve the strict lower inequality at prime boundaries. -/
theorem DusartHalfOpenShortBounds.append {left middle right : Nat}
    (first : DusartHalfOpenShortBounds left middle)
    (second : DusartHalfOpenShortBounds middle right) : DusartHalfOpenShortBounds left right := by
  intro x hx hy
  by_cases hm : x < middle
  · exact first x hx hm
  · exact second x (le_of_not_gt hm) hy

/-- An exclusive endpoint past the cutoff covers the complete required closed prefix. -/
theorem hasDusartShortIntervalPrimeBelow_of_halfOpen {N stop : Nat} (hstop : N < stop)
    (bounds : DusartHalfOpenShortBounds 3275 stop) : HasDusartShortIntervalPrimeBelow N := by
  intro x hx hN
  exact bounds x hx (hN.trans_lt (by exact_mod_cast hstop))

end PrimeFactorUnimodality
