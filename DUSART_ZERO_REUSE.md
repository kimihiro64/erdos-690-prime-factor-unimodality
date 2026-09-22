# Reuse audit for the Dusart zero-sum layer

This focused source review was performed on 2026-09-22 before extending the
same-height, multiplicity-counted xi pairing. It is not a claim that no other
useful sibling theorem exists. Check this record before repeating discovery.

## Published revisions inspected

| Repository | Exact revision | Toolchain | Licence |
| --- | --- | --- | --- |
| Robin1984 | `acab1a31f31e0499518a4416b63281e0b4838f9c` | Lean 4.33.1 | Apache-2.0 |
| bombieri-vinogradov | `7a1748306e026825ed6a5555516cc2f28989b2ac` | Lean 4.33.1 | Apache-2.0 |
| WIPResearch | `bdc46941c4f2e13fb84e0a338b905bb10e711357` | Lean 4.33.1 | Apache-2.0 |
| PNT dependency | `f6147e7572ab3abe5428101bc0b13627bcb005df` | Lean 4.33.1 | Apache-2.0 |

The first three were resolved from their published main branches; the last
is the locked dependency. No additional checkout or worktree was created.
Project declarations are checked here with Lean 4.34.0.

## Directly reusable analytic-order proof

BV's [AnalyticOrderConjugation](https://github.com/kimihiro64/bombieri-vinogradov/blob/7a1748306e026825ed6a5555516cc2f28989b2ac/BombieriVinogradov/Helpers/ComplexAnalysis/AnalyticOrderConjugation.lean)
contains `ComplexAnalysis.AnalyticAt.conj_conj`,
`analyticOrderAt_conj_conj`, and `analyticOrderNatAt_conj_conj`.
These are general complex-analysis statements, with only local analyticity
as a hypothesis. Its direct imports are Mathlib modules; its private
derivative helper and three public proofs have explicit proof bodies.

The pinned PNT [KadiriZeroCounting](https://github.com/kimihiro64/PrimeNumberTheoremAnd/blob/f6147e7572ab3abe5428101bc0b13627bcb005df/PrimeNumberTheoremAnd/IEANTN/KadiriZeroCounting.lean)
also has the private `Kadiri.analyticAt_conj_conj` and
`Kadiri.analyticOrderAt_conj_conj` proofs. The surrounding zero-counting
results have additional hypotheses; those are not imported by the extraction.

Their local-factorization argument is reused in
`Mathlib/Analysis/Analytic/Order/Conjugation.lean`, under the `Complex`
namespace. Its only imports are Mathlib's analytic order, complex Cauchy
integral, and derivative-star modules. Mathlib's existing
`differentiableAt_conj_conj_iff` replaces the older derivative helper.
The candidate records both sources and renamings, and is built independently
before its xi consumer. No zero-free region or RH premise is added.

## Other inspected source and applicability

| Source | What is already proved | Applicability here |
| --- | --- | --- |
| BV `Helpers/ComplexAnalysis/DivisorIndexTransport` | Existence of an index at equal multiplicity, carrying a `Fin.cast` label | Useful transport pattern; not itself an equivalence under `ρ -> 1-conj(ρ)` |
| BV `ZeroFree/QuadraticConjugateZeroIndex` | Existence of a conjugate zero index for a primitive quadratic character | Does not establish a bijection preserving every multiplicity label |
| BV `ZeroFree/PairSubtypeTsum` | Exact sum over two distinct indices | Applicable when retaining a distinguished pair; currently no extraction needed for the whole-series reindexing |
| BV `ZeroFree/RiemannXiZeroSumPositivity` | Nonnegativity of the xi logarithmic-derivative series for `Re(s)>1` | Not the compact smoothed comparison for `1/2<σ<=1`; preserve its domain |
| Robin `NicolasLandau/WeightedZeroPairing` | Exact weighted zero atoms and a vertical resolvent estimate | Existing project contour/transform infrastructure already adapts the Robin route |
| Robin `NicolasLandau/XiZeroConstant` | Inverse-square summability and an exact xi mass under RH | Reuse the unconditional summability leaf; do not import the RH-dependent mass evaluation as unconditional |
| WIP `NumberField/Proof/PairedDirichletZeroIndex` | Value-preserving equivalence between a product divisor and two factor divisors | Reuses sigma/fiber/subtype equivalences; its carrier is a Dirichlet product, not this xi reflection |
| WIP `NumberField/Proof/QuadraticLZeroSymmetry` | Reflection of primitive quadratic L-zeros | Different carrier; the xi function-level reflection/conjugation is already proved here |
| WIP `NumberField/Proof/RiemannShiftedZeroMass` | Exact shifted xi mass and bounds under RH | Cannot supply the unconditional Dusart tail estimate without discharging RH |

BV paths abbreviated `ZeroFree/...` are under
`BombieriVinogradov/Proof/SiegelWalfisz/ZeroFree/`. WIP paths start at
`RobinBV/`. The modules in this table were source-inspected, not wholesale
added as dependencies or claimed to have been rebuilt here. Further reuse
requires checking the particular declaration's full closure and axioms.

## Project-specific assembly now implemented

The existing `ZetaXiStechkin.riemannXi_conj` and
`ZetaXiDivisorReflection` already provide xi function conjugation and
the multiplicity-preserving map `ρ -> 1-ρ`. The extracted order theorem
supplies the conjugate multiplicity equality. `ZetaXiDivisorConjugation`
combines these into a same-height equivalence preserving the finite label.

Whole-series and reflection-stable-subtype pairing uses Mathlib's
`Equiv.tsum_eq`, `Summable.comp_injective`, `Summable.subtype`, and
`Summable.tsum_subtype_add_tsum_subtype_compl`. These do not need reproof.
`KadiriZeroSummability` instantiates the already-proved smoothed summability
theorem with the actual paper weight. The resulting central-strip
elimination leaves the outer-strip series explicit; quantitative outer-zero
and gamma bounds remain required for Dusart's unconditional constants.

For retaining one distinguished off-critical pair, the new general lemma
`Summable.pair_le_tsum_of_involution` applies Mathlib's existing
`Summable.sum_le_tsum` to the symmetrized series and reindexes it. Individual
summands may be negative. The nonfixed-orbit hypothesis prevents counting a
critical-line zero twice. `ZetaXiDivisorPairing` and `KadiriZeroSums` apply
this to the actual divisor, retaining the complete outer-strip remainder.
`KadiriOuterMaster` also integrates central-strip elimination into the
paper-weight master inequality. The later `KadiriRetainedZeros` and
`KadiriRetainedMaster` retain one pair at the selected harmonic.
`KadiriRetainedBounds` proves equation (34) directly using monotonicity and
the existing cubic transform bound, and `KadiriDistinguishedZero` inserts
that quantitative estimate into the actual master. These symbolic results
do not certify the remaining numerical zero-free-region constants.

## Verification and remaining boundary

The later `XiHeightTail` layer also reuses
`SmoothedXiRemainder.summable_xi_divisor_shift_inv_sq`, ultimately the
unconditional PNT xi inverse-square theorem, rather than the RH-dependent
mass evaluations. A bounded-strip comparison proves summability of the
actual Mossinghoff--Trudgian absolute-height tail. `KadiriOuterPairs`,
`KadiriOuterTail`, and `KadiriTailMaster` then assemble the weighted error
with the existing reflection and retained-zero machinery. The numerical
tail estimate and the proof of absolute-height separation remain open;
neither follows merely from this reuse of summability.

The subsequent `XiHeightTailPairing` reuses the same actual conjugation
equivalence to obtain the positive-ordinate formula. `XiLowReciprocalMass`
and `XiHeightTailZero` instead use the project's independently established
unconditional real Hadamard constant and the locally finite divisor to
bound the height-zero tail by a finite reciprocal-mass subtraction. This
does not use the RH-dependent sibling evaluations. The finite low-zero
lower sum and the numerical tail budget still require verification.

Both general candidates, their xi consumers, actual-weight summability,
zero sums, and outer master compile against the pinned project environment.
The 28 declarations audited by `.research/DusartXiPairingAxioms.lean` use
only `propext`, `Classical.choice`, and `Quot.sound`. The Lean regression
`test/lean/KadiriZeroSums.lean` passes, including negative individual
summands, infinite analytic order, fixed critical-line labels, preserved
multiplicity labels, and the actual retained-pair sum. CI builds these
modules serially in `lean-foundations`, before certificate jobs.

Still required: outer-zero, pole, and gamma estimates, the numerical parameters giving
`R=5.573412`, and the remaining unconditional PNT/finite analytic inputs.
This reuse increment does not finish the three final Dusart providers or
the all-`k` theorem.
