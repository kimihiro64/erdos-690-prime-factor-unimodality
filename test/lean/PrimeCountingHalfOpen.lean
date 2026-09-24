import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.PrimeCountingSieveRows

/-! Check the prime jump at 1627, half-open coverage and batch composition. -/

open PrimeFactorUnimodality

private def criticalRow : DusartHalfOpenPiRow :=
  ⟨1626, 1627, 257, 257, ⟨8, 49, 20, 2⟩, ⟨8, 3, 8, 30⟩⟩

private noncomputable def smallSieve : Nat := PrimeCert.Sieve.sieveK 1700 42

private theorem smallSieve_valid : PrimeCert.Sieve.IsSieve 1700 smallSieve :=
  PrimeCert.Sieve.isSieve_of_sieveK_eq
    (show PrimeCert.Sieve.sieveK 1700 42 = smallSieve from rfl) (by decide) (by decide)

example : DusartHalfOpenPiBounds 1626 1627 :=
  criticalRow.provides_of_sieve smallSieve_valid (k := 10) (by decide +kernel)

private theorem initialCount : Nat.primeCounting 1625 = 257 :=
  primeCounting_eq_of_sieve_check smallSieve_valid (k := 10) (by decide +kernel)

example : DusartHalfOpenPiBounds 1626 1627 :=
  dusartSievePiSteps_provide smallSieve_valid initialCount [criticalRow]
    (k := 3) (by decide +kernel) (by decide +kernel)

example : checkDusartSievePiSteps 1700 3 smallSieve 1625 256 [criticalRow] = false := by
  decide +kernel

example : checkDusartSievePiSteps 1700 3 smallSieve 1627 258 [criticalRow] = false := by
  decide +kernel

example : checkDusartSievePiSteps 1700 0 smallSieve 1600 251 [criticalRow] = false := by
  decide +kernel

-- The count at the excluded prime endpoint is not a valid count for this row.
example : ({ criticalRow with beforeRightCount := 258 }.checkSieve 1700 10 smallSieve) =
    false := by decide +kernel

example : dusartThetaTable66CellsChain 1626 1627
    ([criticalRow].map DusartHalfOpenPiRow.coverageCell) = true := by decide +kernel

example : dusartThetaTable66CellsChain 1625 1627
    ([criticalRow].map DusartHalfOpenPiRow.coverageCell) = false := by decide +kernel

example (first : DusartHalfOpenPiBounds 1000 1627)
    (second : DusartHalfOpenPiBounds 1627 3594642) : DusartHalfOpenPiBounds 1000 3594642 :=
  first.append second

example (initial : HasDusartRealPrimeCountingBoundsBelow 1000)
    (suffix : DusartHalfOpenPiBounds 1000 3594642) :
    HasDusartRealPrimeCountingBoundsBelow 3594641 :=
  hasDusartRealPrimeCountingBoundsBelow_of_halfOpen initial suffix
