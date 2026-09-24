import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingHalfOpen
import PrimeFactorUnimodality.Helpers.Arithmetic.SievePrimeCountIncrements

set_option autoImplicit false

/-! # Shared-sieve checking for half-open prime-count rows

Every row carries just two counts and two smooth-power logarithm witnesses.
All rows reuse one certified packed sieve, independently of its representation.
-/

namespace PrimeFactorUnimodality

/-- Check the endpoint counts against the shared sieve and the local rational margins. -/
def DusartHalfOpenPiRow.checkSieve (row : DusartHalfOpenPiRow) (N k bits : Nat) : Bool :=
  row.checkMargins && checkSievePrimeCount N k bits row.left row.leftCount &&
    checkSievePrimeCount N k bits (row.right - 1) row.beforeRightCount

/-- An accepted row has its claimed real-variable meaning, with no prime-count premise. -/
theorem DusartHalfOpenPiRow.provides_of_sieve (row : DusartHalfOpenPiRow)
    {N k bits : Nat} (sieve : PrimeCert.Sieve.IsSieve N bits)
    (valid : row.checkSieve N k bits = true) : DusartHalfOpenPiBounds row.left row.right := by
  simp only [checkSieve, Bool.and_eq_true] at valid
  exact row.provides (primeCounting_eq_of_sieve_check sieve valid.1.2)
    (primeCounting_eq_of_sieve_check sieve valid.2) valid.1.1

/-- A whole bounded batch is checked once, then reused over its covered real interval. -/
theorem dusartSievePiRows_provide {N k bits left right : Nat}
    (sieve : PrimeCert.Sieve.IsSieve N bits) (rows : List DusartHalfOpenPiRow)
    (valid : rows.all (fun row => row.checkSieve N k bits) = true)
    (chain : dusartThetaTable66CellsChain left right
      (rows.map DusartHalfOpenPiRow.coverageCell) = true) : DusartHalfOpenPiBounds left right := by
  apply dusartHalfOpenPiRows_provide rows _ chain
  intro row hrow
  exact row.provides_of_sieve sieve (List.all_eq_true.mp valid row hrow)

/-- Advance through adjacent count checkpoints, never recounting earlier bits. -/
def checkDusartSievePiSteps (N k bits : Nat) : Nat → Nat → List DusartHalfOpenPiRow → Bool
  | _, _, [] => true
  | point, count, row :: rest =>
      row.checkMargins && checkSieveCountStep N k bits point count row.left row.leftCount &&
        checkSieveCountStep N k bits row.left row.leftCount (row.right - 1) row.beforeRightCount &&
          checkDusartSievePiSteps N k bits (row.right - 1) row.beforeRightCount rest

/-- Each local count transition preserves the actual prime-counting function. -/
theorem checkDusartSievePiSteps_sound {N k bits point count : Nat}
    (sieve : PrimeCert.Sieve.IsSieve N bits) (initial : Nat.primeCounting point = count)
    {rows : List DusartHalfOpenPiRow}
    (valid : checkDusartSievePiSteps N k bits point count rows = true) :
    ∀ row ∈ rows, DusartHalfOpenPiBounds row.left row.right := by
  induction rows generalizing point count with
  | nil => simp
  | cons row rest ih =>
    simp only [checkDusartSievePiSteps, Bool.and_eq_true] at valid
    have countLeft := primeCounting_eq_of_sieve_step sieve initial valid.1.1.2
    have countBefore := primeCounting_eq_of_sieve_step sieve countLeft valid.1.2
    intro found hfound
    rcases List.mem_cons.mp hfound with rfl | hrest
    · exact DusartHalfOpenPiRow.provides _ countLeft countBefore valid.1.1.1
    · exact ih countBefore valid.2 found hrest

/-- Checked local increments and gap-free coverage supply the whole real interval. -/
theorem dusartSievePiSteps_provide {N k bits point count left right : Nat}
    (sieve : PrimeCert.Sieve.IsSieve N bits) (initial : Nat.primeCounting point = count)
    (rows : List DusartHalfOpenPiRow)
    (valid : checkDusartSievePiSteps N k bits point count rows = true)
    (chain : dusartThetaTable66CellsChain left right
      (rows.map DusartHalfOpenPiRow.coverageCell) = true) : DusartHalfOpenPiBounds left right :=
  dusartHalfOpenPiRows_provide rows (checkDusartSievePiSteps_sound sieve initial valid) chain

end PrimeFactorUnimodality
