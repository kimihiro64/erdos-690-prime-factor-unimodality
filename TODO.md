# Completion checklist

- [x] Verify the exact all-`k` classification against the Wang--Crapis proof:
  unimodal exactly for `k ≤ 3`, non-unimodal for every `k ≥ 4`.
- [x] Audit the three sibling repositories before adding new infrastructure.
- [x] Formalize the finite recursion, density bridge, positive cases, and the
  complete classification through `k = 48`.
- [x] Build closed divisor/Fermat certificates for the current record-gap
  sub-block and kernel-replayable residue certificates for the record twin.
- [x] Recover and hash-verify the published full 1,113,106-gap factor and
  Fermat-residue archives.
- [ ] Finish and build the generated finite prime-prefix, reciprocal-sum, and
  record-twin certificates without `native_decide`.
- [ ] Complete the non-certificate and certificate redesign work in
  `LEAN_COMPLETION_HANDOFF.md`.  In particular, split the finite interval
  monolith before replay and replace the 2,175-file record-gap owner forest
  with compact owner rows using `RecordGapOwnerRows.lean`.
- [x] Replace the full-record-gap branch with the uniform CRT tail from
  `k = 38001`. Finite Abel summation supplies the descent and the ordinary
  Mertens estimate supplies the ascent, retaining the existing prime-counting,
  theta, and short-interval assumptions. The tail and generic all-`k`
  reduction compile; their axiom audits contain only Lean's standard logical
  axioms. The 10,918-test full-gap replay is no longer a classification or CI
  dependency. Its sources, archive audit, and caches remain preserved.
- [ ] Discharge the explicit theta, prime-counting, and short-interval
  analytic interfaces from kernel-checked theorems.
  The prime-counting tail is now reduced by a proved adapter from Dusart's
  explicit asymptotic formula (with remainder `7.32 / log^3 x`); the remaining
  obligation is the asymptotic provider itself together with the finite
  cutoff providers.
  The reciprocal-prime interface is now discharged throughout the uniform
  tail `k ≥ 38,001` by the finite prime-counting shell and ordinary Mertens
  upper bound; the focused reduction and tail compile without that hypothesis.
  The proved elementary Chebyshev core from `PrimeNumberTheoremAnd` is now
  ported through `psi_upper`, without its `native_decide`-based later check.
  Its compiled consequences give `0.86 x ≤ theta x ≤ 1.11 x` from `250000`
  and a prime in `(n, floor (13n/10)]`.  Above one million the sharper
  bounds give `(n, floor (5n/4)]`; a consecutive-prime selector using the
  `13/10` bound is compiled at the post-record scale `r / floor(log₂ r)` for every
  `r ≥ 8,600,001`, with the sharper `5/4` selector available from `2^25`.
  These selectors are now packaged as `HasElementaryTailPrimePair`; their
  wider ratios are not yet sufficient for the current CRT descent/ascent
  numerics, so the sharper `HasUniformTailPrimePair` remains the actual open
  tail input.
- [x] Replace the old fixed-`k` Challenge/Solution surface with the exact
  all-`k` statement. The Solution proof remains pending until the analytic
  interfaces and full generated certificates are closed.
- [ ] Run the research and release profiles, inspect the axiom surface, and
  run Comparator on a clean tree.
- [ ] Commit and push the completed proof to preserve timestamped provenance.
- [ ] Build the Justin Sun Prize issue-submission skill, verify the current JSP
  and registry requirements, and port the skill back to the template repo.
- [ ] Audit in-flight work on the next candidate before starting its child repo.
