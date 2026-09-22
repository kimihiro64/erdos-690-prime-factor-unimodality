import PrimeFactorUnimodality.Helpers.Analytic.DusartRootBounds

set_option autoImplicit false

/-! # Assembly of the bounded and unbounded Lemma 3.3 ranges

Analytic estimates and assemblers with no generated endpoint dependencies.
-/

namespace PrimeFactorUnimodality

noncomputable section

/-! Global Lemma 3.3 assembled from the paper's bounded direct computation
and the analytic tail above. -/
theorem dusart_lemma_3_3_of_finite_and_theta_upper
    {X : Real} (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (finite : ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)))
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  intro x hx
  by_cases hle : x ≤ X
  · exact finite x hx hle
  · have hcut : ¬ x ≤ (10 ^ 11 : Real) ^ 3 := by
      intro hcut
      exact hle (hcut.trans hX)
    exact dusart_lemma_3_3_large (le_of_not_ge hcut) theta_upper

theorem dusart_lemma_3_3_of_rows_and_theta_upper
    {rows : List DusartLemma33FiniteRow} {X : Real}
    (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (cover : DusartLemma33FiniteRowsCover rows X)
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_finite_and_theta_upper hX
    (dusart_lemma_3_3_finite_of_rows cover) theta_upper

/-! The paper's theta hypothesis is exported in the project's bundled
Proposition 5.1 interface.  This adapter keeps the Lemma 3.3 proof connected
to that interface without weakening the finite-range obligation. -/
theorem dusart_lemma_3_3_of_rows_and_theta_bounds
    {rows : List DusartLemma33FiniteRow} {X : Real}
    (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (cover : DusartLemma33FiniteRowsCover rows X)
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  apply dusart_lemma_3_3_of_rows_and_theta_upper hX cover
  exact dusart_theta_upper_1000081_of_bounds thetaBounds

/-! Indexed form for the compact bounded computation.  The proof is kept at
the source boundary so a generated table can be assembled from reusable rows
without first materializing an equivalent list. -/
theorem dusart_lemma_3_3_of_indexed_rows_and_theta_bounds
    {n : Nat} {rows : Fin n → DusartLemma33FiniteRow} {X : Real}
    (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (cover : DusartLemma33FiniteRowsIndexedCover rows X)
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_finite_and_theta_upper hX
    (dusart_lemma_3_3_finite_of_indexed_rows cover) (by
      intro y hy
      have hupper := thetaBounds.1 y hy
      nlinarith)

/-! The compact chunk boundary is the provider-facing form of the bounded
    computation.  Once generated chunks cover the full published finite range,
    the analytic tail is applied exactly once here. -/
theorem dusart_lemma_3_3_of_chunk_and_theta_bounds
    (chunk : DusartLemma33FiniteChunk)
    (hX : (10 ^ 11 : Real) ^ 3 ≤ chunk.cutoff)
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_finite_and_theta_upper hX
    chunk.provides (by
      intro y hy
      have hupper := thetaBounds.1 y hy
      nlinarith)

theorem dusart_lemma_3_3_of_proof_chunk_and_theta_bounds
    (chunk : DusartLemma33FiniteProofChunk)
    (hX : (10 ^ 11 : Real) ^ 3 ≤ chunk.cutoff)
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_finite_and_theta_upper hX chunk.valid (by
    intro y hy
    have hupper := thetaBounds.1 y hy
    nlinarith)

/-! The published bounded computation may be split into independently
    cacheable proof chunks.  Their assembled validity is consumed here once,
    before the analytic power-sum tail is applied. -/
theorem dusart_lemma_3_3_of_proof_chunks_and_theta_bounds
    (first : DusartLemma33FiniteProofChunk)
    (rest : List DusartLemma33FiniteProofChunk)
    (hX : (10 ^ 11 : Real) ^ 3 ≤
      (DusartLemma33FiniteProofChunk.appendMany first rest).cutoff)
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_proof_chunk_and_theta_bounds
    (DusartLemma33FiniteProofChunk.appendMany first rest) hX thetaBounds

/-! The paper's Lemma 3.3 depends on the independent global estimate
`theta y < 1.000081 * y`, not on Proposition 5.1 itself.  Keep that
dependency explicit so a Proposition 5.1 construction cannot accidentally
become circular. -/
theorem dusart_lemma_3_3_of_proof_chunks_and_theta_upper
    (first : DusartLemma33FiniteProofChunk)
    (rest : List DusartLemma33FiniteProofChunk)
    (hX : (10 ^ 11 : Real) ^ 3 ≤
      (DusartLemma33FiniteProofChunk.appendMany first rest).cutoff)
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_finite_and_theta_upper hX
    (DusartLemma33FiniteProofChunk.appendMany first rest).valid theta_upper

theorem dusart_lemma_3_3_of_paper_finite_check_and_theta_upper
    (finite : ∀ x : Real, 0 < x →
      x ≤ (10 ^ 11 : Real) ^ 3 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)))
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_finite_and_theta_upper
    (by norm_num) finite theta_upper

/-! This is the exact finite/analytic split stated in Dusart's proof: the
bounded computation ends at `(10^11)^3`, while the displayed power-sum
estimate handles the tail. -/
theorem dusart_lemma_3_3_of_paper_finite_check
    (finite : ∀ x : Real, 0 < x →
      x ≤ (10 ^ 11 : Real) ^ 3 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)))
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_finite_and_theta_upper
    (by norm_num) finite (by
      intro y hy
      have hupper := thetaBounds.1 y hy
      nlinarith)

/-! The paper-shaped finite obligation can be supplied by integer endpoint
checks.  This is the boundary consumed by a compact bounded computation. -/
theorem dusart_lemma_3_3_of_paper_integer_endpoint_check
    (endpoint : ∀ n : Nat, 1 ≤ n →
      (n : Real) ≤ (10 ^ 11 : Real) ^ 3 →
      Chebyshev.psi (n : Real) - Chebyshev.theta n -
          Chebyshev.theta (Real.sqrt n) <
        (1777745 : Real) / 1000000 * (n : Real) ^ (1 / (3 : Real)))
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x -
      Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_of_paper_finite_check
    (dusart_lemma_3_3_finite_of_integer_endpoints endpoint) thetaBounds

/-! Proposition 3.2 can now consume the paper-shaped finite Lemma 3.3 input
and the bundled Proposition 5.1 theta estimate directly. -/
theorem dusart_proposition_3_2_of_paper_finite_lemma_and_theta_bounds
    (finite : ∀ x : Real, 0 < x →
      x ≤ (10 ^ 11 : Real) ^ 3 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)))
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / (3 : Real)) := by
  exact dusart_proposition_3_2_of_paper_lemma_and_theta_bounds
    (dusart_lemma_3_3_of_paper_finite_check finite thetaBounds) thetaBounds

/-! Compact-row form of the paper's Proposition 3.2 boundary. The indexed
Lemma 3.3 rows discharge only the bounded computation; the theta provider is
still an explicit theorem input and the analytic tail is supplied by
`dusart_lemma_3_3_large`. -/
theorem dusart_proposition_3_2_of_indexed_rows_and_theta_bounds
    {n : Nat} {rows : Fin n → DusartLemma33FiniteRow} {X : Real}
    (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (cover : DusartLemma33FiniteRowsIndexedCover rows X)
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  exact dusart_proposition_3_2_of_paper_finite_lemma_and_theta_bounds
    (fun x hx hX' => dusart_lemma_3_3_finite_of_indexed_rows cover x hx (hX'.trans hX))
    thetaBounds

theorem dusart_proposition_3_2_of_paper_integer_endpoint_check
    (endpoint : ∀ n : Nat, 1 ≤ n →
      (n : Real) ≤ (10 ^ 11 : Real) ^ 3 →
      Chebyshev.psi (n : Real) - Chebyshev.theta n -
          Chebyshev.theta (Real.sqrt n) <
        (1777745 : Real) / 1000000 * (n : Real) ^ (1 / (3 : Real)))
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / (3 : Real)) := by
  exact dusart_proposition_3_2_of_paper_finite_lemma_and_theta_bounds
    (fun x hx hX =>
      dusart_lemma_3_3_finite_of_integer_endpoints endpoint x hx hX)
    thetaBounds

theorem dusart_proposition_3_2_of_finite_lemma_and_theta_upper
    {X : Real} (hX : (10 ^ 11 : Real) ^ 3 ≤ X)
    (finite : ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)))
    (theta_error : ∀ y : Real, 0 < y →
      Chebyshev.theta y - y < y / 36260) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / (3 : Real)) := by
  apply dusart_proposition_3_2_of_paper_lemma_and_theta_upper
  · apply dusart_lemma_3_3_of_finite_and_theta_upper hX finite
    intro y hy
    have h := theta_error y hy
    nlinarith
  · exact theta_error

theorem dusart_proposition_3_2_of_proof_chunks_and_theta_error
    (first : DusartLemma33FiniteProofChunk)
    (rest : List DusartLemma33FiniteProofChunk)
    (hX : (10 ^ 11 : Real) ^ 3 ≤
      (DusartLemma33FiniteProofChunk.appendMany first rest).cutoff)
    (theta_error : ∀ y : Real, 0 < y →
      Chebyshev.theta y - y < y / 36260) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  exact dusart_proposition_3_2_of_finite_lemma_and_theta_upper hX
    (DusartLemma33FiniteProofChunk.appendMany first rest).valid theta_error

theorem dusart_proposition_3_2_of_proof_chunks_and_theta_bounds
    (first : DusartLemma33FiniteProofChunk)
    (rest : List DusartLemma33FiniteProofChunk)
    (hX : (10 ^ 11 : Real) ^ 3 ≤
      (DusartLemma33FiniteProofChunk.appendMany first rest).cutoff)
    (thetaBounds : HasDusartThetaBounds) :
    ∀ x : Real, 0 < x →
      Chebyshev.psi x - Chebyshev.theta x <
        (100007 : Real) / 100000 * Real.sqrt x +
          (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  apply dusart_proposition_3_2_of_paper_lemma_and_theta_bounds
  · exact dusart_lemma_3_3_of_proof_chunks_and_theta_bounds
      first rest hX thetaBounds
  · exact thetaBounds

end

end PrimeFactorUnimodality
