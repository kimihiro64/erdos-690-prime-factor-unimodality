import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.ThetaSieveTrace

/-! Check the closed seed, trace endpoints, count corruption and consumer-threshold crossing. -/

open PrimeFactorUnimodality

private noncomputable def sieve : Nat := PrimeCert.Sieve.sieveK 4000 64

private theorem sieve_valid : PrimeCert.Sieve.IsSieve 4000 sieve :=
  PrimeCert.Sieve.isSieve_of_sieveK_eq
    (show PrimeCert.Sieve.sieveK 4000 64 = sieve from rfl) (by decide) (by decide)

private def first : DusartThetaSieveStep :=
  ⟨⟨4, 2, 14334072 / 8000000, 14334088 / 8000000⟩, ⟨8, 0, 8, 0⟩, ⟨8, 16, 0, 0⟩⟩

private def second : DusartThetaSieveStep :=
  ⟨⟨5, 3, 25424424 / 8000000, 27209592 / 8000000⟩, ⟨8, 16, 0, 0⟩, ⟨8, 0, 0, 8⟩⟩

example : second.next.Valid ∧ DusartTailThetaSegment 3 5 :=
  checkDusartThetaTrace_sound sieve_valid dusartThetaSeed_valid
    (rows := [first, second]) (k := 2) (by decide +kernel)

example : checkDusartThetaTrace 4000 2 sieve dusartThetaSeed second.next [first] = false := by
  decide +kernel

example : checkDusartThetaTrace 4000 2 sieve dusartThetaSeed
    { second.next with count := 4 } [first, second] = false := by decide +kernel

example : ({ second with next := { second.next with count := 4 } }.check
    4000 2 sieve first.next) = false := by decide +kernel

private def crossingStart : DusartThetaState := ⟨3500, 489, 0, 100000⟩
private def crossing : DusartThetaSieveStep :=
  ⟨⟨3502, 489, 0, 100000⟩, ⟨1, 0, 0, 0⟩, ⟨1, 13, 0, 0⟩⟩

-- The transport alone is valid, but a cell crossing 3501 must check the tail margins.
example : crossing.check 4000 2 sieve crossingStart = true := by decide +kernel

example : checkDusartThetaTrace 4000 2 sieve crossingStart crossing.next [crossing] = false := by
  decide +kernel

example (first : DusartTailThetaSegment 3 3504)
    (second : DusartTailThetaSegment 3504 3594641) : DusartTailThetaSegment 3 3594641 :=
  first.append second
