import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingLogBounds
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingRows
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Table66Subintervals
import PrimeFactorUnimodality.Helpers.FiniteCertificates.PrimePrefixCounts

set_option autoImplicit false

/-! # Compact prime-counting endpoint certificates

Every row reuses one proved prime list. Integer-power comparisons provide
rational log enclosures, and the same assembler proves both endpoint bounds.
-/

namespace PrimeFactorUnimodality

structure DusartSmoothLogPower where
  s : Nat
  a : Nat
  b : Nat
  c : Nat

def DusartSmoothLogPower.value (p : DusartSmoothLogPower) : Nat :=
  2 ^ p.a * 3 ^ p.b * 5 ^ p.c

def DusartSmoothLogPower.lower (p : DusartSmoothLogPower) : Rat :=
  (p.a * (693147 / 1000000) + p.b * (1098612 / 1000000) +
    p.c * (1609437 / 1000000)) / p.s

def DusartSmoothLogPower.upper (p : DusartSmoothLogPower) : Rat :=
  (p.a * (693148 / 1000000) + p.b * (1098613 / 1000000) +
    p.c * (1609438 / 1000000)) / p.s

theorem DusartSmoothLogPower.lower_le_log (p : DusartSmoothLogPower)
    {n : Nat} (hs : 0 < p.s) (h : p.value ≤ n ^ p.s) :
    (p.lower : Real) ≤ Real.log n := by
  simpa only [lower, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_ofNat] using log_nat_lower_of_smooth_power hs h

theorem DusartSmoothLogPower.log_le_upper (p : DusartSmoothLogPower)
    {n : Nat} (hn : 0 < n) (hs : 0 < p.s) (h : n ^ p.s ≤ p.value) :
    Real.log n ≤ (p.upper : Real) := by
  simpa only [upper, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_ofNat] using log_nat_upper_of_smooth_power hn hs h

structure DusartPrimeCountingCertificateRow where
  left : Nat
  right : Nat
  lowerPower : DusartSmoothLogPower
  upperPower : DusartSmoothLogPower

def dusartPrefixCount (ps : List Nat) (n : Nat) : Nat :=
  (ps.filter (fun p => decide (p ≤ n))).length

def DusartPrimeCountingCertificateRow.check
    (row : DusartPrimeCountingCertificateRow) (N : Nat) (ps : List Nat) : Bool :=
  decide (599 ≤ row.left ∧ row.left ≤ row.right ∧ row.right ≤ N ∧
    0 < row.lowerPower.s ∧ 0 < row.upperPower.s ∧ 0 < row.lowerPower.lower ∧
    row.lowerPower.value ≤ row.right ^ row.lowerPower.s ∧
    row.left ^ row.upperPower.s ≤ row.upperPower.value ∧
    (row.right : Rat) / row.lowerPower.lower * (1 + 1 / row.lowerPower.lower) ≤
      dusartPrefixCount ps row.left ∧
    (dusartPrefixCount ps row.right : Rat) ≤
      row.left / row.upperPower.upper * (1 + (6381 / 5000 : Rat) / row.upperPower.upper))

noncomputable def DusartPrimeCountingCertificateRow.toEndpointRow
    (row : DusartPrimeCountingCertificateRow) {N : Nat} {ps : List Nat}
    (hps : computablePrimesBelow (N + 1) = ps) (valid : row.check N ps = true) :
    DusartPrimeCountingEndpointRow := by
  simp only [check, decide_eq_true_eq] at valid
  refine {
    left := row.left
    right := row.right
    left_large := valid.1
    left_le_right := valid.2.1
    lower_endpoint := ?_
    upper_endpoint := ?_ }
  · rcases valid with ⟨hl, ho, hN, hsl, hsu, hL, hpl, hpu, hlo, hup⟩
    rw [primeCounting_eq_filter_length_of_prime_prefix (ho.trans hN) hps]
    change _ ≤ (dusartPrefixCount ps row.left : Real)
    apply dusartPiLower_le_of_log_lower (Nat.cast_nonneg _) (by exact_mod_cast hL)
      (row.lowerPower.lower_le_log hsl hpl)
    exact_mod_cast hlo
  · rcases valid with ⟨hl, ho, hN, hsl, hsu, hL, hpl, hpu, hlo, hup⟩
    rw [primeCounting_eq_filter_length_of_prime_prefix hN hps]
    change (dusartPrefixCount ps row.right : Real) ≤ _
    have hlog : 0 < Real.log (row.left : Real) :=
      Real.log_pos (by exact_mod_cast (show 1 < row.left by omega))
    apply le_dusartPiUpper_of_log_upper (Nat.cast_nonneg _) hlog
      (row.upperPower.log_le_upper (by omega) hsu hpu)
    have h := Rat.cast_mono (K := Real) hup
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one] using h

/-- Coverage is checked separately from the prime and logarithm arithmetic. -/
def DusartPrimeCountingCertificateRow.coverageCell
    (row : DusartPrimeCountingCertificateRow) : DusartThetaTable66Cell :=
  ⟨row.left, row.right, 0, 0⟩

theorem dusartPrimeCountingCertificateRows_provide
    {N right : Nat} {ps : List Nat} (hps : computablePrimesBelow (N + 1) = ps)
    (rows : List DusartPrimeCountingCertificateRow)
    (valid : rows.all (fun row => row.check N ps) = true)
    (chain : dusartThetaTable66CellsChain 599 right
      (rows.map DusartPrimeCountingCertificateRow.coverageCell) = true) :
    ∀ x : Real, 599 ≤ x → x ≤ right →
      dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real) ∧
        (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x := by
  intro x hx hright
  obtain ⟨cell, hcell, hleft, hright⟩ := dusartThetaTable66CellsChain_covers chain hx hright
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hcell
  have hv : row.check N ps = true := List.all_eq_true.mp valid row hrow
  exact dusartPrimeCountingEndpointRow_provides (row.toEndpointRow hps hv) hleft hright

end PrimeFactorUnimodality
