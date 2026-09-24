import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.ShortIntervalSieveRows

/-! Check strict prime endpoints, malformed witnesses and complete batch coverage. -/

open PrimeFactorUnimodality

private def first : DusartShortSieveRow := ⟨3275, 3299, 1099, ⟨8, 37, 21, 10⟩⟩
private def second : DusartShortSieveRow := ⟨3299, 3323, 1107, ⟨8, 77, 9, 1⟩⟩

private noncomputable def sieve : Nat := PrimeCert.Sieve.sieveK 4000 64

private theorem sieve_valid : PrimeCert.Sieve.IsSieve 4000 sieve :=
  PrimeCert.Sieve.isSieve_of_sieveK_eq
    (show PrimeCert.Sieve.sieveK 4000 64 = sieve from rfl) (by decide) (by decide)

private theorem bounds : DusartHalfOpenShortBounds 3275 3323 :=
  dusartShortSieveRows_provide sieve_valid [first, second]
    (by decide +kernel) (by decide +kernel)

example : ∃ q : Nat, q.Prime ∧ (3299 : Real) < q ∧
    (q : Real) ≤ 3299 * (1 + 1 / (2 * (Real.log 3299) ^ 2)) :=
  bounds 3299 (by norm_num) (by norm_num)

example : ({ first with prime := 3295, index := 1098 }.check 4000 sieve) = false := by
  decide +kernel

example : ({ first with index := 1100 }.check 4000 sieve) = false := by decide +kernel

example : ({ first with logPower := ⟨0, 37, 21, 10⟩ }.check 4000 sieve) = false := by
  decide +kernel

example : ({ second with left := 3275 }.check 4000 sieve) = false := by decide +kernel

example : dusartThetaTable66CellsChain 3275 3323
    ([first].map DusartShortSieveRow.coverageCell) = false := by decide +kernel

example : HasDusartShortIntervalPrimeBelow 3322 :=
  hasDusartShortIntervalPrimeBelow_of_halfOpen (by decide : 3322 < 3323) bounds

example (a : DusartHalfOpenShortBounds 3275 3323)
    (b : DusartHalfOpenShortBounds 3323 3601993) : DusartHalfOpenShortBounds 3275 3601993 :=
  a.append b
