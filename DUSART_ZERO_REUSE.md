# Reuse audit for the Dusart zero-sum layer

## Newest follow-up: complete high-zero tail (2026-09-23)

The quantitative high-height obligation from the earlier sections is now
proved for the actual box weight. Mathlib's existing `fwdDiff`, complex-power
derivative, and FTC give the exact averaged-power identity at every natural
order, with denominator `h^n*s*(s+1)*...*(s+n)`. The resulting norm bound
gains inverse height to power `n+1`. Five reusable candidate modules expose
the local recurrence, primitive identity, and norm estimates.

`DusartBoxHeightDecay` applies these results to the actual paired atoms.
`XiHeightTailZeroHigh` reduces the zero-height inverse-square tail to four
times the existing tail at half the cutoff. `DusartBoxHighTail` then applies
the proved Lehman counting bound for `T>=10^9`. This controls the entire
high-zero series, with multiplicities, both ordinate signs, and zeros
exactly at the cutoff. It does not need RH or an assumed low-zero mass.

`DusartBoxZeroSplit` proves the exact strict-low/closed-high decomposition
and combines that high bound with the previously adapted BV finite-gap
bound. The low-gap and reciprocal-norm mass inputs remain explicit: this
does not establish the missing numerical low-height facts or the final
Dusart providers. The negative-even correction budget and fixed-cutoff
scalar certification also remain to be completed.

All nine new modules compile. Eighteen new regression examples pass;
twenty-eight audited exports use only `propext`, `Classical.choice`, and
`Quot.sound`. CI builds the candidates and consumers serially before tests.
The sibling audit below remains authoritative; no broader sibling import
or RH-dependent evaluation was added for this increment.

Previous follow-up (2026-09-22): BV's generic power-decay leaf has now been
adapted and connected to the actual Dusart box atoms and finite xi sums.
The exact averaged-power identity and absolute summability also reuse the
existing paired explicit-formula infrastructure. Details follow here;
older sections retain the obligations as they stood at each increment.

## Complex-power bound and actual box-transform follow-up

The reviewed BV file `Helpers/ComplexAnalysis/CpowDecayBound.lean`, at
`7a1748306e026825ed6a5555516cc2f28989b2ac`, proves
`BombieriVinogradov.ComplexAnalysis.norm_real_cpow_div_le_exp_gap_mul_reciprocal`
using only Mathlib. Its hypotheses are `1<=y` and `Re(s)<=1-delta`;
there is no RH, character, or assumed zero-free-region theorem in this
leaf. The proof is adapted under namespace `Complex` in the new
`Mathlib/Analysis/SpecialFunctions/Pow/ComplexDecay.lean` candidate.
Its exact source, licence, original name, and renaming are recorded there.

`DusartBoxZeroBounds` now applies that inequality to every point in the
actual averaging support. `DusartBoxSpectralFormula` sums it over arbitrary
finite selections of the actual xi divisor, preserving multiplicities.
The coefficient is `(x+(m+3)*h)*exp(-delta*log(x))`, with the reciprocal
norm sum kept explicit. This adapts BV's finite-sum assembly without
importing its nonprincipal-character or existential-constant interfaces.

The new primitive-transform identities use Mathlib's Fubini, substitution,
FTC, and complex-power derivative directly. They prove
`F_w(-s)+1/s=average(t^s/s)` and its exact exponent-one main term.
The existing `summable_smoothedXiPaired` proves absolute convergence of
these actual averaged powers. The new full psi spectral formula therefore
does not rebuild contour integration, Hadamard factorization, or zero
enumeration, and never splits a divergent unpaired reciprocal series.

Still needed: quantitative high-height decay and tails, the negative-even
correction estimate, actual low-height zero information, and fixed-cutoff
scalar certification. The RH-dependent Robin/WIP mass evaluations remain
inapplicable as unconditional numerical bounds. This increment does not
finish the three Dusart providers or the all-`k` classification.

The ten new modules compile in the pinned Lean 4.34 environment. Nineteen
new regression examples and five preserved explicit-formula examples pass.
All twenty-six audited new exports have only `propext`, `Classical.choice`,
and `Quot.sound` in their closures. No RH-dependent mass evaluation is in
the new theorem statements or axiom closures.

Current follow-up: the unconditional high counting envelope, closed
Lehman tail, pole estimates, and explicit smoothed Gamma bounds are proved
and connected to the master inequality; see the final sections. Earlier sections record
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

## Explicit smoothed Gamma follow-up

`DigammaEulerBounds` directly applies the pinned PNT declarations
`sum_eq_integral_add_integral_deriv` and `abs_B1_le_half`, with
`f(x)=1/(z+x)`. Its derivative integral telescopes, giving the uniform
finite bound `1/Re(z)`. `DigammaLogBounds` then uses PNT's actual
`hasSum_digamma_of_re_pos`, Mathlib's harmonic-minus-log limit, and the
extended Mathlib-only `LogShiftLimit` candidate. The result is the
two-sided complex estimate `norm(digamma(z)-log(z))<=1/Re(z)`.

The inspected BV Gamma-growth leaves and PNT norm-growth estimates use
existential constants; they do not supply this explicit two-sided error.
The new proof nevertheless reuses their underlying proved PNT digamma
series rather than reconstructing Gamma or its convergence. The positive
real shift increases the norm and decreases the reciprocal error, so the
shifted Gamma bound retains the required leading coefficient `1-kappa`.

For the separate smoothed remainder, `SmoothedGammaBounds` reuses
`smoothedGammaRemainder_eq_neg_trivialZeroSum` and the existing twofold
integration-by-parts estimate. PNT's inverse-square summability and tail
bound sum the resulting majorant. The actual Kadiri derivative bound
supplies its cubic constant. There is no new contour interchange,
summability premise, or Gamma convergence assumption.

`KadiriExplicitMaster` inserts both estimates into the actual weighted
inequality, including the zero harmonic and arbitrary finite degree.
All 13 new theorem closures and both reused Euler--Maclaurin inputs were
audited with only `propext`, `Classical.choice`, and `Quot.sound`.
Outer-zero separation, finite low-zero numerics, the remaining parameter
budget, and the final Dusart providers are not discharged by this step.

## Initial numerical region and separation

The existing `xi_zero_three_four_one_constraint` now yields an actual
initial numerical region, not merely an inequality awaiting optimization.
`ZetaZeroFreeInitial` uses Mathlib's Euler-constant and logarithm bounds to
bound its remainder by `4*log(abs(t))` for `abs(t)>=10^9`. Substituting
`sigma=1+1/(8*log(abs(t)))` proves the gap `1/(56*log(abs(t)))`.
The inspected sibling results with unspecified constants are not imported
as a substitute for this numerical starting bound.

`KadiriOuterSeparation` reuses the actual same-height divisor reflection
and logarithmic monotonicity to derive the cutoff condition for every
finite set of harmonics. `KadiriInitialMaster` connects it to the actual
smoothed inequality, also deriving the distinguished zero's upper strip
bound. Only the low-height upper bound below `10^9` remains as a separate
zero-location premise. The general separation lemma supports replacing
the initial constant by subsequent proved improvements.

All eight exports compile and their axiom closures contain only
`propext`, `Classical.choice`, and `Quot.sound`. The seven regression
examples include both signs, the exact high cutoff, and arbitrary degree.

The [Mossinghoff--Trudgian paper](https://arxiv.org/pdf/1410.3926),
sections 2--3, requires an established region and low-height information
before its numerical iterations. Its final iterations start at `5.7`.
Our proved starting constant `56` is not that input and is not the desired
`5.573412`: the intervening improvements and complete numerical budget
must still be proved. No RH verification or final provider is claimed here.

## Exact transform gap and bootstrap normalization

`KadiriTransformGap` directly reuses the project's existing
`kadiriWeight_laplace_eq_rescale` and `re_finiteLaplace_ofReal`. The result
is the paper's exact integral `K(w,theta)`, not a newly assumed transform
identity. Mathlib's finite-sum erase identity extracts the unique zero
natural frequency without dropping its pole contribution.

`KadiriGammaBudget` separates the nonzero frequencies' leading logarithm
from the explicit residual, whose height monotonicity follows from the
existing logarithm and reciprocal comparisons. The complete budget is
then normalized into its leading term and a cubic-scale correction by
exact algebra, retaining the actual derivative mass and low-zero subtraction.

The general region master reuses `kadiri_outer_separation_of_region` for
successive established constants. The preserved constant-56 specialization
supplies its high-height premise from `xi_zero_gap_initial`. The new actual
bootstrap theorem invokes this master before applying the transform and
budget identities; it does not assume the master inequality. Numerical
margin verification, low-height inputs, and final provider construction
are still required. No global monotonicity of the signed `K` integrand or
nonpositivity of the entire correction is asserted without proof.

All 14 new exports and the preserved initial master compile and were
audited with only `propext`, `Classical.choice`, and `Quot.sound`.
The 12 regression examples include the zero-only set and arbitrary degree.

## Height-decaying Gamma follow-up

`DigammaEulerIdentity` factors the existing exact application of PNT's
`sum_eq_integral_add_integral_deriv`; both error bounds now share it.
`DigammaHeightBounds` bounds its derivative integral using
`norm(z+x)^2 >= (norm(z)+x)^2/2` on the right half-plane, then applies
the already-proved digamma limit. This gives the explicit error
`2/norm(z)`, reusing the same actual Gamma series and Bernoulli bound.
The prior `1/Re(z)` estimate remains available unchanged.

The actual shifted Gamma majorant now takes the better error at nonzero
height, with `2*(1+kappa)/abs(t)` as an explicit height bound. The zero
harmonic keeps its previous bound. `KadiriGammaBudget` carries these
individual errors through its exact logarithmic decomposition, residual
monotonicity, and the existing normalized actual bootstrap. No assumed
numerical zero-free region or new Gamma series is introduced by this step.

The new leaves and actual bootstrap compile; 24 audited exports use only
the three standard logical axioms. The height-error, updated bootstrap,
and preserved Gamma and initial-region regressions pass. This does not
verify the target numerical margins or finish the final Dusart providers.

## Exact transform evaluation and interval margins

The finite transform does not require a new integration theory. The
Mathlib-only `ExpLinear` candidate directly uses Mathlib's existing
`integral_exp_mul_complex` for the unweighted term. An explicit primitive
and the existing FTC handle the linear weight, including its zero-exponent
case. `ExpTrig` takes real and imaginary parts using Mathlib's integral
projections and complex arithmetic to obtain purely real endpoint formulas.

`KadiriKernelNormalForm` applies the existing sine addition formulas to
the actual kernel. `KadiriTransformClosedForm` integrates that identity
term by term, producing the exact signed `K`, not a new assumed or
approximate transform. `KadiriTransformBounds` then uses the already-proved
`kadiriKernel_nonneg` and integral comparison to obtain uniform endpoint
bounds. It does not reprove correlation positivity or assert monotonicity
of the signed difference. The actual bootstrap consumes these bounds via
`xi_zero_gap_of_endpoint_bootstrap_margin`; numerical margins remain open.

The independent candidates and actual bootstrap compile, with all 24
audited exports using only the three standard logical axioms. The 20 new
endpoint/transform examples and 14 preserved bootstrap examples pass.

## Uniform complete correction follow-up

The new affine tail bound uses the already-proved `xiLehmanHighBound` and
elementary logarithm and reciprocal comparisons. It retains logarithmic
growth at nonzero heights and exact finite low-mass subtraction at zero.
Nonnegativity of the latter comes from `xiHeightTail_nonneg` and the
existing actual Lehman bound, not an RH-dependent mass formula.

The complete correction now directly applies
`kadiriDerivativeMass_le_majorant` and
`kadiriDerivativeMassMajorant_le_of_moment_bounds`; the moments and their
underlying analytic comparison are not reconstructed. Proved pole and
Gamma monotonicity replace their moving parameters by a fixed corner.
The signed linear term remains in the cubic envelope. The actual bootstrap
derives the upper scale-log bound from failure of its target gap and then
uses a verified maximum-scale budget, rather than assuming global
correction nonpositivity. The numerical inputs remain explicit obligations.

The actual bootstrap and all five envelope modules compile. The 20 new
examples and 65 preserved analytic examples pass; all 20 audited theorem
closures use only the three standard logical axioms.

## Exact polynomial and uniform parameter follow-up

The source of the polynomial construction is Mossinghoff--Trudgian,
[arXiv:1410.3926](https://arxiv.org/pdf/1410.3926), section 5 and table 5.
The new `Trigonometric.Autocorrelation` candidate uses Mathlib's finite
sum multiplication, trigonometric subtraction, and frequency regrouping;
the focused sibling checks did not supply this exact cosine-coefficient
identity. The published generating decimals are treated as exact rationals,
and their cosine coefficients are recomputed, not identified with another
rounded column. The proof covers every phase, with signed input sequences.

`Log.AffineRatio` uses logarithmic monotonicity and elementary reciprocal
comparison. Its uniform parameter consumer and the actual region theorem
reuse the existing bootstrap and divisor conjugation; no zero indexing,
reflection, or numerical region is reconstructed or silently assumed.
The final numerical admissibility and low-height obligations remain open.

Both Mathlib-only candidates and the actual uniform bootstrap compile.
The actual band-budget variant also retains the negative correction,
using monotonicity of the normalized cubic and the existing moment bound.
Its small-scale companion derives the higher height from the previous
region. No monotonicity of the signed transform or the unnormalized
correction is silently assumed. The 20 polynomial/parameter examples and
34 preserved moment/bootstrap examples pass; all 26 audited new exports
have only the three standard logical axioms in their theorem closures.

## Single-crossing and split-bootstrap follow-up

`FiniteLaplace.SingleCrossing` directly applies the existing
`hasDerivAt_finiteLaplace`, `HasDerivAt.real_of_complex`, and
`re_finiteLaplace_ofReal`; no parametric integration proof is reconstructed.
Exponential reweighting of a source with one positive-to-negative crossing
shows that derivative nonpositivity persists. The small generic endpoint
lemma uses Mathlib's proved mean-value monotonicity theorems. Focused
Mathlib and sibling candidate searches did not supply this exact signed
transform endpoint-minimum interface.

The actual Kadiri source crosses at `log(a1/a0)`, so its interval lower
bound is the smaller of two whole-transform values. The actual split
bootstrap reuses the existing scale, higher-height, negative-correction,
and divisor-conjugation proofs. The 13 audited theorem closures contain
only the standard logical axioms; 13 new and 74 preserved analytic examples
pass. Numerical iteration and low-height inputs remain unproved here.

## Real-axis Gamma improvement

The sharper `Re(digamma(x))<=log(x)` bound does not require another Gamma
series proof. `DigammaRealBounds` applies Mathlib's
`AntitoneOn.integral_le_sum` and `integral_inv_of_pos`, then the existing
`tendsto_sum_inv_add_sub_log` and fixed-shift logarithm limit. The PNT
series at the pinned revision remains the analytic foundation.

`SmoothedGammaRealBounds` combines this upper bound with the existing
lower logarithmic error at the shifted argument. Only the coefficient
`kappa` remains in the zero-height error. `SmoothedGammaFactorBounds`
uses that theorem in its actual majorant; `KadiriGammaBudget` and the
complete moment correction inherit the improvement. No zero-counting,
conjugation, summability, or assumed zero-free-region input is reintroduced.

Both new leaves and the complete explicit, uniform, and split bootstrap
consumers compile. All 110 examples in the eight affected analytic
regression modules pass. The 14 audited exports, including the actual
region theorems, use only `propext`, `Classical.choice`, and `Quot.sound`.

## Arbitrary scale covers and grid specialization

`KadiriScaleCoverBootstrap` factors out the actual zero argument from the
two-regime theorem. The previous theorem now specializes that proof to a
Boolean-indexed family. The general theorem accepts any covering family,
retaining both the improved height and the negative correction per band.

For a uniform grid, `KadiriGridBootstrap` directly reuses Mathlib's
`Monotone.biUnion_Ico_Ioc_map_succ` from `Order/SuccPred/IntervalSucc`.
No floor, ceiling, or interval-union infrastructure is reconstructed.
Every positive band count is allowed, and the normalized correction weight
is exactly `j/m`. Numerical margins and low-height zero inputs remain
explicit hypotheses; the grid assembler alone is not a numerical region.

The cover, grid, and preserved two-band theorem compile with only the
three standard logical axioms. The thirteen existing transform regressions
and the new sixteen-band actual-region interface regression pass.

## Elementary budget and derivative-moment substitution

`KadiriConservativeBudget` directly uses Mathlib's proved
`Real.eulerMascheroniConstant_lt_two_thirds` and the project's existing
`re_xi_divisor_reciprocal_nonneg`. No new Euler-constant series or numerical
zero-mass evaluation is needed. Monotonicity of the quadratic and cubic
tail terms propagates this upper bound through the complete correction.
The conservative grid theorem then invokes the actual grid bootstrap;
it retains the low-height zero-location hypothesis unchanged.

`KadiriElementaryMoments` reuses `abs_kadiriKernel₂_le_neg_zero`, proved
earlier using autocorrelation, and Mathlib's `integral_pow`. This yields
the full-support monomial upper bound at every natural degree. Its actual
bootstrap consumer supplies all four required moment bounds directly,
eliminating separate quadrature obligations without a sampled maximum.

All four modules compile. Eleven audited declarations, including the
Mathlib Euler bound and the actual elementary region theorem, have only
`propext`, `Classical.choice`, and `Quot.sound` in their closures. The
numerical zero-free region, low-height locations, and fixed-cutoff
Chebyshev-error theorem are still required for the final Dusart providers.

## Iterated Chebyshev smoothing

The next non-certificate step follows Dusart's HDR (2022), section 2.2,
Theorem 35. The Mathlib-only `IntervalIntegral.IteratedAverage` candidate
uses the existing `Monotone.intervalIntegrable`, interval integral
comparison, linearity, and the exact integral of the identity function.
Induction gives the support enclosure and exact mean shift at every
natural averaging order. `DusartPsiSmoothing` then directly applies
Mathlib's `Chebyshev.psi_mono`, retaining discontinuities and both sides
of the pointwise error estimate.

The inspected sibling `CharacterChebyshevDecay` applies BV's primitive
nonprincipal-character formula with existential constants; it does not
provide these fixed-constant zeta averages. Robin's inspected
`robinPrimePowerSum_eq_weighted_explicit_series` explicitly assumes RH.
Neither is treated as an unconditional numerical Dusart theorem. The
averaged explicit formula and its quantitative zero contributions remain
open; the new smoothing layer supplies only the pointwise recovery step.
Both modules compile, the eight regression examples pass, and all eight
audited exports have only the three standard logical axioms.

## Concrete box weight and actual averaged explicit formula

No replacement contour or zero-enumeration proof is necessary.
`DusartBoxExplicitFormula` applies the existing
`smoothedVonMangoldt_entire_explicitFormula` to the actual additive box
cutoff, discharging every hypothesis. The generic regularity candidate uses
Mathlib's `continuous_primitive`, `integral_interval_sub_left`, and FTC;
the exact derivative is the difference of the two endpoint values divided
by the interval width. Successive averaging therefore gives the required
two continuous derivatives without an assumed smooth cutoff.

The support candidate uses interval-integral congruence and continuity on
the closure to include the exact cutoff boundary. Endpoint derivatives
vanish by Mathlib's `IsLocalMax.deriv_eq_zero` and `IsLocalMin.deriv_eq_zero`.
A compactness bound on the second derivative is used only for convergence,
not as an unspecified constant in a claimed numerical estimate.

The arithmetic identification directly reuses `Chebyshev.psi_eq_sum_Icc`,
the natural floor/ceiling order equivalences, finite-sum integration, and
`tsum_eq_sum`. The resulting `DusartBoxAverageFormula` is an unconditional
identity for the actual averaged psi error, not a conditional replacement
formula. The xi index, multiplicities, and paired summability are unchanged.
Numerical bounds on its transforms and zero sums remain separate obligations.
All seven modules compile, 23 new and eight preserved regression examples
pass, and all 27 audited theorem closures use only the three standard
logical axioms. CI builds the candidate leaves and their consumers serially.
