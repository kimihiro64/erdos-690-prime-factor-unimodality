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
- [ ] Extend the record-gap certificate to the full published block and raise
  the finite record range to the source proof's cutoff `k = 8,600,001`.
  The archive leaves 10,918 interior terms without a listed factor; closing
  this item requires kernel replay of their published Fermat tests or new
  divisor certificates, not merely trusting the 64-bit residue log.
  `scripts/audit_full_record_gap.py` now independently accounts for every one
  of the 1,113,105 interior offsets: 1,087,142 have cheap primorial owners,
  15,045 use listed factors, and exactly 10,918 remain in the replay queue
  (manifest semantic SHA-256 `aa4dbd835d585be69cbc8d4529cfef5e72f19b13f21dfdafcc5359e4e0d403fd`).
- [ ] Discharge the explicit theta, prime-counting, and short-interval
  analytic interfaces from kernel-checked theorems.
  The reciprocal-prime interface is now discharged by the proved Mertens
  estimate throughout the uniform tail `k ≥ 8,600,002`; the focused closed
  reduction and tail theorem both compile without that hypothesis.
  The proved elementary Chebyshev core from `PrimeNumberTheoremAnd` is now
  ported through `psi_upper`, without its `native_decide`-based later check.
  Its compiled consequences give `0.86 x ≤ theta x ≤ 1.11 x` from `250000`
  and a prime in `(n, floor (13n/10)]`.  Above one million the sharper
  bounds give `(n, floor (5n/4)]`; a consecutive-prime selector using the
  `13/10` bound is compiled at the post-record scale `r / floor(log₂ r)` for every
  `r ≥ 8,600,001`, with the sharper `5/4` selector available from `2^25`.
  Use these closed selectors to replace the remaining short-interval
  interface before formalizing any deeper Dusart input.
- [x] Replace the old fixed-`k` Challenge/Solution surface with the exact
  all-`k` statement. The Solution proof remains pending until the analytic
  interfaces and full generated certificates are closed.
- [ ] Run the research and release profiles, inspect the axiom surface, and
  run Comparator on a clean tree.
- [ ] Commit and push the completed proof to preserve timestamped provenance.
- [ ] Build the Justin Sun Prize issue-submission skill, verify the current JSP
  and registry requirements, and port the skill back to the template repo.
- [ ] Audit in-flight work on the next candidate before starting its child repo.
