# Reuse audit for the Dusart zero-sum layer

Current follow-up: the unconditional high counting envelope and closed
Lehman tail are now proved; see the final section. Earlier sections record
the obligations at each increment and are superseded where explicitly noted.

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

## Counting-to-integral follow-up

The additional BV leaf `ExplicitFormula/Horizontal/ZeroHeightWindowCountBound`
proves a logarithmic window bound, but for nonprincipal primitive characters
and with an existential constant. It is not the numerical zeta counting
estimate required here. PNT's `Backlund/ZeroCountCrude` proves an
unconditional `|N(T)| <= A*T^(3/2)` bound with existential `A`, which supports
convergence. `IEANTN/KadiriZeroCounting` explicitly distinguishes that route
from its conditional, sharper Backlund-constant route.

Mathlib's existing Abel formula and Robin's prime-log application use
natural locations. The new Mathlib-only `MeasureTheory.Integral.FinsetAbel`
instead integrates each atom's indicator using the existing FTC to obtain
the finite identity at arbitrary real heights. `XiZeroCountingAbel` applies
it to the already-established actual divisor and local finiteness, not to
a newly assumed enumeration. `XiZeroCountingRemainder` subtracts the smooth
main term exactly. These are analytic identities, not a replacement claim
that the quantitative counting error has been proved.

For the subsequent infinite passage, no new zero-count growth theorem is
needed. `InfiniteSum.Sublevel` uses Mathlib's dominated convergence for
series to derive the vanishing counting boundary directly from the
already-proved summability and decreasing kernel. `XiZeroCountingImproper`
then proves genuine improper integrability from the finite identity.
`XiLehmanAbel` specializes this unconditionally to the actual xi pair,
including the closed-cutoff atom. The explicit counting discrepancy bound
is still required for numerical control, not for this convergence step.

`XiLehmanSmoothTerm` and `XiLehmanRemainder` now complete smooth subtraction
and the infinite discrepancy identity. Their quantitative tail estimate
explicitly requires the actual bound `|R(x)|<=2log(x)`; this is not supplied
by the inspected sibling counting results. The 21 exports in this increment
were built and audited with only the three standard logical axioms.

There is a further endpoint distinction when reusing PNT's counting API:
at the pinned revision, `IEANTN/ZetaDefinitions.lean` defines
`riemannZeta.N T` using `Set.Ioo 0 T`, while this project's `xiZeroCount T`
uses `0<gamma<=T`. A bridge requires the full cutoff multiplicity or an
explicit right-limit argument, as well as conversion of the `7/8` offset.
No equality of these two counting functions at zero heights is claimed.

The endpoint bridge is now implemented in `XiZeroCountingEndpoints` and
`XiZetaCountingBridge`: strict xi counts equal PNT's `N(T)`; closed counts
add the entire cutoff multiplicity and are right-hand limits of `N`.
`ZetaXiMultiplicity` proves that the xi divisor weight equals PNT's integer
zeta order. The finite grouping reuses
`Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt`
from the pinned `Mathlib/Analysis/Complex/DivisorFiber` module. Its original
authorship and licence remain in the dependency. The bridge needs neither
the RH-dependent mass formulas nor the `KadiriZeroCounting` import.

`XiZetaCountingBounds` now also converts the `7/8` offset explicitly.
Under the stated RvM hypothesis, its constants give the `2log(T)` envelope
for `T>=2, log(T)>=5`, and then the actual Lehman bound. The hypothesis is
still open. All 21 public results in this increment build and have only
`propext`, `Classical.choice`, and `Quot.sound` in their axiom closures.

## Backlund auxiliary reuse

`BacklundAuxiliary` now imports the pinned `Backlund/ZeroCountCrude` directly
and uses its `zetaSurrogate` and `zetaSurrogate_differentiable`, including the
residue patch at one. The attribution to Robby Sneiderman and the full pinned
revision are in the consumer. Its differentiability axiom audit has only the
three standard logical axioms. The new symmetrized-power real-part identities
therefore extend an existing entire-function proof rather than reconstruct it.

`BacklundJensen` likewise applies Mathlib's existing `sum_divisor_le`; the new
compactness recurrence and finite-cardinality comparison supply the missing
interfaces for the real crossings. `BacklundRealZeros` proves the actual
crossing bound at arbitrarily large powers. This does not claim that the
coarse PNT growth estimate supplies the explicit logarithmic discrepancy:
argument variation, the counting identity, and sharp enough magnitude and
gamma estimates remain separate proof obligations.

The horizontal comparison is now completed in `BacklundArgument` and
`BacklundArgumentIntegral`. These reuse Mathlib's intermediate value theorem,
integer interval cardinality, exponential covering, continuous-map lifting,
inverse differentiation, and FTC. The new glue proves the actual endpoint
phase bound and its logarithmic-derivative integral form; it does not rebuild
those underlying topological and analytic tools. Its remaining explicit
circle magnitude hypotheses are not presented as a proved sharp count bound.

## Actual rectangle counting and gamma separation

The pinned PNT `RectangleArgumentPrinciple` now supplies the actual residue
calculation. Its `rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt`,
companion argument-change theorem, and logarithmic-derivative residue
theorem compile and have only the three standard logical axioms. The
project uses the integral theorem directly: `XiCountingRectangle` identifies
its support and weights with the existing zeta count. It does not assume
the companion theorem's separate `hargumentChange` premise.

For the real boundary, Robin's published
`Robin1984.Mathlib.NumberTheory.LSeries.RiemannZetaReal` proves nonvanishing
on the whole positive real axis through its Euler remainder and moment
generating continuation. This project's already-pinned Abel continuation
gives the needed negativity on `[1/2,1)` directly; xi reflection supplies
the rest. `ZetaXiRealNonvanishing` therefore reuses that existing continuation
instead of extracting Robin's much larger independent continuation closure.

`XiHalfContour` reuses the existing xi functional and conjugation identities
and Mathlib's exact interval substitution/conjugation theorems. The existing
gamma-product differentiation is generalized in place to the nonvanishing
right half-plane, retaining its old export unchanged; `BacklundXiLogDerivative`
then reuses it to connect the actual counting integrand to the surrogate.
`XiCountingDecomposition` uses PNT's existing `continuousAt_digamma_of_re_pos`
to justify integrability, splits both contour segments, and applies the
earlier horizontal Jensen estimate to the actual count. The sharp integrated
gamma, vertical surrogate, and circle magnitude estimates are still required.

## Euler logarithm and vertical-argument follow-up

The vertical argument no longer needs an estimate. The Mathlib-only
`RiemannZetaEulerLog` candidate directly uses
`riemannZeta_eulerProduct_exp_log`,
`DirichletCharacter.eulerProduct_log_eq_LSeries`, and `LSeries_hasDerivAt`.
The required coefficient comparison is just `vonMangoldt_le_log`.
No Euler product or Dirichlet-series differentiation is reconstructed.
The positive-coefficient norm comparison follows the same Mathlib-series
argument already used by the project's `ZetaTrigonometric` candidate.

`BacklundVerticalArgument` uses this analytic logarithm to obtain the exact
vertical integral and its height-independent argument bound, as well as
the centre lower bound. `BacklundCountingEstimate` combines them with the
previous actual contour, Jensen bound, and real-axis Abel estimate.
The 21 new theorems compile and have only the three standard logical axioms.
Sharp integrated gamma and explicit circle bounds are still needed for the
numerical counting error; the all-`k` theorem is not yet established.

## Gamma branch and uniform phase follow-up

The sharp gamma contribution is now proved. `GammaLogBranch` directly
imports the pinned PNT `DigammaSeries` module and reuses its `logGammaSeq`,
`cauchySeq_logGammaSeq`, `exp_logGammaSeq`, packet norm majorant, summable
majorant, and `hasSum_digamma_of_re_pos`. The derivative-of-limit argument
was previously local to the last theorem. Only that portion is adapted
and exported here; Robby Sneiderman's copyright and Apache-2.0 attribution
are preserved alongside the exact revision. The exponential identity and
positive-real phase fix the branch used in the contour, rather than
identifying it with a potentially discontinuous principal Gamma logarithm.

The required quantitative remainder is new: the generic complex trapezoid
identity follows from Mathlib's FTC, and its logarithm specialization has
telescoping norm bound `1/(8*Re z)`. Mathlib's existing
`Complex.tendsto_nat_mul_log_one_add_of_tendsto` supplies the far-endpoint
limit. No real Stirling constant or new Gamma convergence theorem is needed.
Robin's real `robin_log_step_trapezoid` and BV's Fourier trapezoid cutoff
do not state this complex second-derivative remainder. The PNT theorem
`stirling_bound_re_ge_zero` controls Gamma's norm with an existential
growth constant, not the branch's uniformly bounded phase error.

The new branch, phase, exact gamma contours, and actual main-term counting
estimate compile. All 26 theorem closures have only the three standard
logical axioms. The numerical circle estimates remain open; the resulting
counting theorem explicitly retains those hypotheses and does not yet
establish the final numerical zero-free region or the all-`k` result.

## Unconditional high counting and exact closed-cutoff tail

`BacklundCircleBounds` directly reuses the pinned PNT `Zeta0EqZeta` and
`ZetaBnd_aux1b` at `N=1`. These supply an actual Euler remainder on `Re(s)>0`;
the leftmost circle point is `Re(s)=1/10`, so the proof does not incorrectly
apply the other Abel continuation's strict `Re(s)>1/10` hypothesis there.
The right semicircle reuses the already-proved Euler logarithm comparison.
No new Euler continuation or zeta surrogate is reconstructed.

The new mean-value Jensen candidate adapts Mathlib's proved divisor-mass
comparison, with its original attribution and exact pinned revision.
Antipodal averaging uses Mathlib's existing radius-negation invariance.
The resulting circle estimate feeds the existing power-limit argument and
the already-proved actual counting and Gamma contours. It proves the
unconditional `log(T)+17` counting error for `T>=10` and hence `2log(T)`
for `T>=10^9`, not merely an existential growth estimate.

Both count conventions are controlled at arbitrary cutoffs. The new
left-limit transfer bounds the strict count, while the previous right-limit
transfer bounds the closed count. In the exact infinite Abel identity, the
closed-cutoff atom and closed boundary count combine into the strict count.
`xiHeightTail_le_main_add_correction_high` in `XiLehmanHigh` therefore has no
residual cutoff-multiplicity term and no assumed counting envelope.
The module's declarations are in namespace `PrimeFactorUnimodality`.

All 32 new theorems and the preserved horizontal Jensen export were built
and audited with only the three standard logical axioms. The new regression
also checks every positive natural harmonic at the paper's high cutoff.
The zero-harmonic finite mass, outer-zero separation, separate smoothed
pole/Gamma errors, and final numerical zero-free parameters remain open;
this does not finish the three Dusart providers or the all-`k` theorem.

## Weighted master and pole-bound follow-up

The same actual conjugation pairing now proves evenness of `xiHeightTail`,
including transport between the two subtype predicates; no new zero
symmetry is proved from scratch. `XiLehmanBudget` uses the existing exact
integral evaluation and correction bound for nonzero heights, and the
existing unconditional low-reciprocal-mass subtraction at height zero.
Every natural harmonic is covered, not only a fixed finite list.

`KadiriPoleBounds` directly uses
`abs_re_kadiriWeight_laplace_sub_pole_le_mass_im` and the existing
`KadiriLaplacePositivity.re_kadiriWeight_laplace_nonneg`. The latter applies
at complex points throughout the closed right half-plane: it removes the
entire shifted transform, giving the sharper error `eta^2*M(z,theta)/y^2`
without a shifted cubic loss. The new work is the unshifted rational pole's
sign comparison and weighted assembly. It does not rederive integration by
parts, correlation positivity, or the kernel's derivative bound. The
combined master replaces both the pole terms and infinite zero tails.

The separate smoothed Gamma estimates are not implied by the counting
Gamma-phase theorem. They, the separation argument, finite low-zero
numerics, and final numerical zero-free parameters remain required.
