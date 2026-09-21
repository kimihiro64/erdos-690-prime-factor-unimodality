import PrimeFactorUnimodality.Helpers.Analytic.DusartProofPart05


set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/- The finite boundary in Dusart's Lemma 3.3 is exactly 10^33. -/

theorem dusart_lemma_3_3_large
    {x : Real} (hx : (10 ^ 11 : Real) ^ 3 ≤ x)
    (theta_upper : ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y) :
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
      (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_large_of_count hx
    (dusart_floor_log_div_two_le_rpow hx) theta_upper

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

/-! The upper half of Proposition 5.1 is stronger than the relaxed uniform
estimate used in the large-range part of Lemma 3.3.  Export the numerical
conversion once so downstream source proofs use the paper's displayed
constant rather than repeating an arithmetic adapter. -/
theorem dusart_theta_upper_1000081_of_bounds
    (thetaBounds : HasDusartThetaBounds) :
    ∀ y : Real, 0 < y →
      Chebyshev.theta y < (1000081 : Real) / 1000000 * y := by
  intro y hy
  have hupper := thetaBounds.1 y hy
  nlinarith

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
    (fun x hx hX' => dusart_lemma_3_3_finite_of_indexed_rows cover x hx hX')
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
  exact dusart_lemma_3_3_of_proof_chunks_and_theta_bounds
    first rest hX thetaBounds

theorem dusart_gap_upper_from_uniform_root_bound
    {x : Real} (hx : (64 : Real) ≤ x)
    (hroot : ∀ y : Real, 0 ≤ y →
      Chebyshev.psi y ≤ (100007 : Real) / 100000 * y) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have hdecomp := psi_sub_theta_le_of_root_bound
    (x := x) (c := (100007 : Real) / 100000) (by linarith) (by norm_num) hroot
  have hfive := fifth_rpow_le_three_fifths_cube_rpow hx
  have hscaled := mul_le_mul_of_nonneg_left hfive
    (by norm_num : (0 : Real) ≤ (100007 : Real) / 100000)
  have hsqrt : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt] at hdecomp
  have hdecomp' : Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    nlinarith [hdecomp]
  have hscaled' : (100007 : Real) / 100000 * x ^ (1 / 5 : Real) ≤
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) := by
    nlinarith [hscaled]
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  have hcoeff : (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) ≤ (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
    nlinarith
  nlinarith [hdecomp', hscaled', hcoeff]

theorem psi_upper_of_theta_upper_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (htheta : Chebyshev.theta y ≤ y + y / 36260) :
    Chebyshev.psi y ≤ (100007 : Real) / 100000 * y := by
  have hy_pos : 0 < y := by linarith
  have hlog : (42 : Real) ≤ Real.log y := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hy)
  have hlog_pos : 0 < Real.log y := by linarith
  have hpow : (42 : Real) ^ (4 : Nat) ≤ (Real.log y) ^ (4 : Nat) := by
    exact pow_le_pow_left₀ (by norm_num) hlog 4
  have hcor : Chebyshev.psi y - Chebyshev.theta y ≤
      y / (Real.log y) ^ 4 := by
    have habs := theta_sub_psi_abs_le_logFourth hy
    have hnonneg : 0 ≤ Chebyshev.psi y - Chebyshev.theta y := by
      linarith [Chebyshev.theta_le_psi y]
    rw [abs_sub_comm, abs_of_nonneg hnonneg] at habs
    exact habs
  have hscaled : y / (Real.log y) ^ 4 ≤ y / (42 : Real) ^ 4 := by
    exact div_le_div_of_nonneg_left hy_pos.le (by positivity) hpow
  nlinarith [hcor, hscaled, htheta]

theorem psi_upper_of_strict_theta_upper_at_large
    {y : Real} (hy : (4e18 : Real) ≤ y)
    (htheta : Chebyshev.theta y < y + y / 36260) :
    Chebyshev.psi y < (100007 : Real) / 100000 * y := by
  have hy_pos : 0 < y := by linarith
  have hlog : (42 : Real) ≤ Real.log y := by
    exact forty_two_lt_log_four_e18.le.trans
      (Real.log_le_log (by norm_num) hy)
  have hlog_pos : 0 < Real.log y := by linarith
  have hpow : (42 : Real) ^ (4 : Nat) ≤ (Real.log y) ^ (4 : Nat) := by
    exact pow_le_pow_left₀ (by norm_num) hlog 4
  have hcor : Chebyshev.psi y - Chebyshev.theta y ≤
      y / (Real.log y) ^ 4 := by
    have habs := theta_sub_psi_abs_le_logFourth hy
    have hnonneg : 0 ≤ Chebyshev.psi y - Chebyshev.theta y := by
      linarith [Chebyshev.theta_le_psi y]
    rw [abs_sub_comm, abs_of_nonneg hnonneg] at habs
    exact habs
  have hscaled : y / (Real.log y) ^ 4 ≤ y / (42 : Real) ^ 4 := by
    exact div_le_div_of_nonneg_left hy_pos.le (by positivity) hpow
  have hsum : Chebyshev.psi y <
      y + y / 36260 + y / (42 : Real) ^ 4 := by
    nlinarith [hcor, hscaled]
  have hbound : y + y / 36260 + y / (42 : Real) ^ 4 ≤
      (100007 : Real) / 100000 * y := by
    nlinarith [hy_pos]
  exact hsum.trans_le hbound

theorem dusart_gap_upper_from_three_large_theta_bounds
    {x : Real} (hx : (64 : Real) ≤ x)
    (h2cut : (4e18 : Real) ≤ x ^ (2 : Real)⁻¹)
    (h3cut : (4e18 : Real) ≤ x ^ (3 : Real)⁻¹)
    (h5cut : (4e18 : Real) ≤ x ^ (5 : Real)⁻¹)
    (h2theta : Chebyshev.theta (x ^ (2 : Real)⁻¹) ≤
      x ^ (2 : Real)⁻¹ + x ^ (2 : Real)⁻¹ / 36260)
    (h3theta : Chebyshev.theta (x ^ (3 : Real)⁻¹) ≤
      x ^ (3 : Real)⁻¹ + x ^ (3 : Real)⁻¹ / 36260)
    (h5theta : Chebyshev.theta (x ^ (5 : Real)⁻¹) ≤
      x ^ (5 : Real)⁻¹ + x ^ (5 : Real)⁻¹ / 36260) :
    Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have h2psi := psi_upper_of_theta_upper_at_large h2cut h2theta
  have h3psi := psi_upper_of_theta_upper_at_large h3cut h3theta
  have h5psi := psi_upper_of_theta_upper_at_large h5cut h5theta
  have h2psi' : Chebyshev.psi (x ^ (2 : Real)⁻¹) ≤
      (100007 : Real) / 100000 * x ^ (1 / 2 : Real) := by
    simpa only [show (2 : Real)⁻¹ = 1 / 2 by norm_num] using h2psi
  have h3psi' : Chebyshev.psi (x ^ (3 : Real)⁻¹) ≤
      (100007 : Real) / 100000 * x ^ (1 / 3 : Real) := by
    simpa only [show (3 : Real)⁻¹ = 1 / 3 by norm_num] using h3psi
  have h5psi' : Chebyshev.psi (x ^ (5 : Real)⁻¹) ≤
      (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    simpa only [show (5 : Real)⁻¹ = 1 / 5 by norm_num] using h5psi
  have hdecomp := psi_sub_theta_le_of_three_root_bounds
    (x := x) (c := (100007 : Real) / 100000) (by linarith) (by norm_num)
    h2psi' h3psi' h5psi'
  have hfive := fifth_rpow_le_three_fifths_cube_rpow hx
  have hscaled := mul_le_mul_of_nonneg_left hfive
    (by norm_num : (0 : Real) ≤ (100007 : Real) / 100000)
  have hsqrt : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt] at hdecomp
  have hdecomp' : Chebyshev.psi x - Chebyshev.theta x ≤
      (100007 : Real) / 100000 * Real.sqrt x +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    nlinarith [hdecomp]
  have hscaled' : (100007 : Real) / 100000 * x ^ (1 / 5 : Real) ≤
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) := by
    nlinarith [hscaled]
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  have hcoeff : (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) ≤ (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
    nlinarith
  nlinarith [hdecomp', hscaled', hcoeff]

theorem dusart_gap_upper_from_three_strict_large_theta_bounds
    {x : Real} (hx : (64 : Real) ≤ x)
    (h2cut : (4e18 : Real) ≤ x ^ (2 : Real)⁻¹)
    (h3cut : (4e18 : Real) ≤ x ^ (3 : Real)⁻¹)
    (h5cut : (4e18 : Real) ≤ x ^ (5 : Real)⁻¹)
    (h2theta : Chebyshev.theta (x ^ (2 : Real)⁻¹) <
      x ^ (2 : Real)⁻¹ + x ^ (2 : Real)⁻¹ / 36260)
    (h3theta : Chebyshev.theta (x ^ (3 : Real)⁻¹) <
      x ^ (3 : Real)⁻¹ + x ^ (3 : Real)⁻¹ / 36260)
    (h5theta : Chebyshev.theta (x ^ (5 : Real)⁻¹) <
      x ^ (5 : Real)⁻¹ + x ^ (5 : Real)⁻¹ / 36260) :
    Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
  have h2psi := psi_upper_of_strict_theta_upper_at_large h2cut h2theta
  have h3psi := psi_upper_of_strict_theta_upper_at_large h3cut h3theta
  have h5psi := psi_upper_of_strict_theta_upper_at_large h5cut h5theta
  have h2psi' : Chebyshev.psi (x ^ (2 : Real)⁻¹) <
      (100007 : Real) / 100000 * x ^ (1 / 2 : Real) := by
    simpa only [show (2 : Real)⁻¹ = 1 / 2 by norm_num] using h2psi
  have h3psi' : Chebyshev.psi (x ^ (3 : Real)⁻¹) <
      (100007 : Real) / 100000 * x ^ (1 / 3 : Real) := by
    simpa only [show (3 : Real)⁻¹ = 1 / 3 by norm_num] using h3psi
  have h5psi' : Chebyshev.psi (x ^ (5 : Real)⁻¹) <
      (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    simpa only [show (5 : Real)⁻¹ = 1 / 5 by norm_num] using h5psi
  have hdecomp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hfive := fifth_rpow_le_three_fifths_cube_rpow hx
  have hscaled := mul_le_mul_of_nonneg_left hfive
    (by norm_num : (0 : Real) ≤ (100007 : Real) / 100000)
  have hsqrt : x ^ (1 / 2 : Real) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
  have hdecomp'' : Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * x ^ (1 / 2 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    nlinarith [hdecomp, h2psi', h3psi', h5psi']
  have hdecomp' : Chebyshev.psi x - Chebyshev.theta x <
      (100007 : Real) / 100000 * Real.sqrt x +
        (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
        (100007 : Real) / 100000 * x ^ (1 / 5 : Real) := by
    simpa only [hsqrt] using hdecomp''
  have hscaled' : (100007 : Real) / 100000 * x ^ (1 / 5 : Real) ≤
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) := by
    nlinarith [hscaled]
  have hcuberoot : 0 ≤ x ^ (1 / 3 : Real) := by positivity
  have hcoeff : (100007 : Real) / 100000 * x ^ (1 / 3 : Real) +
      (100007 : Real) / 100000 * (3 / 5 : Real) *
        x ^ (1 / 3 : Real) ≤ (178 : Real) / 100 * x ^ (1 / 3 : Real) := by
    nlinarith
  nlinarith [hdecomp', hscaled', hcoeff]

theorem psi_sub_theta_ge_elementary_sqrt_gap
    {x : Real} (hx : (62500000000 : Real) ≤ x) :
    (86 : Real) / 100 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hx_pos : 0 < x := by linarith
  have hroot_lower : (250000 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by norm_num : (0 : Real) < 250000)).2
    nlinarith
  have htheta := elementary_theta_lower_from_250000 hroot_lower
  have hdecomp := psi_sub_theta_ge_theta_sqrt (by linarith : (2 : Real) ≤ x)
  have htheta' : (86 : Real) / 100 * Real.sqrt x ≤
      Chebyshev.theta (Real.sqrt x) := by
    simpa only [Real.sqrt_eq_rpow] using htheta
  have hdecomp' : Chebyshev.theta (Real.sqrt x) ≤
      Chebyshev.psi x - Chebyshev.theta x := by
    simpa only [Real.sqrt_eq_rpow] using hdecomp
  exact htheta'.trans hdecomp'

theorem dusart_theta_upper_tail_step
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_upper : x ≤ (1446257067000 : Real))
    (hpsi : Chebyshev.psi x ≤ (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  have hx_pos : 0 < x := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := by
    simpa using Real.sq_sqrt (le_of_lt hx_pos)
  have hmain := theta_le_one_plus_dusart_error_of_psi_upper_and_gap hpsi hgap
  have hlinear :
      (100002841 : Real) / 100000000 * x -
          (9999 : Real) / 10000 * Real.sqrt x - x ≤ x / 36260 := by
    have hsqrt_lower : (894000 : Real) ≤ Real.sqrt x := by
      apply (Real.le_sqrt' (by norm_num : (0 : Real) < 894000)).2
      nlinarith
    have hsqrt_upper : Real.sqrt x ≤ (12026689 : Real) / 10 := by
      apply (Real.sqrt_le_iff).2
      constructor
      · norm_num
      · nlinarith
    have hxs : x ≤ (12026689 : Real) / 10 * Real.sqrt x := by
      calc
        x = Real.sqrt x * Real.sqrt x := by nlinarith [hsqrt_sq]
        _ ≤ (12026689 : Real) / 10 * Real.sqrt x :=
          mul_le_mul_of_nonneg_right hsqrt_upper hsqrt_nonneg
    nlinarith
  linarith

theorem dusart_theta_upper_e28_step
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi : Chebyshev.psi x ≤ (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  apply dusart_theta_upper_tail_step hx ?_ hpsi hgap
  exact hx_exp.trans (le_of_lt exp_twentyEight_lt_dusart_endpoint)

theorem dusart_theta_upper_e28_from_absolute_psi_error
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi_error : |Chebyshev.psi x - x| ≤
      (2841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  have hpsi : Chebyshev.psi x ≤
      (100002841 : Real) / 100000000 * x := by
    have hupper := (abs_le.mp hpsi_error).2
    nlinarith
  exact dusart_theta_upper_e28_step hx hx_exp hpsi hgap

/-! The strict form is the one consumed by the published theta interface.
The paper's two strict input estimates are retained here instead of being
weakened to a closed inequality at this boundary. -/
theorem dusart_theta_upper_e28_step_strict
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi : Chebyshev.psi x < (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x < x / 36260 := by
  have hx_pos : 0 < x := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt_sq : (Real.sqrt x) ^ 2 = x := by
    simpa using Real.sq_sqrt (le_of_lt hx_pos)
  have hx_upper : x ≤ (1446257067000 : Real) := by
    exact hx_exp.trans (le_of_lt exp_twentyEight_lt_dusart_endpoint)
  have hsqrt_lower : (894000 : Real) ≤ Real.sqrt x := by
    apply (Real.le_sqrt' (by norm_num : (0 : Real) < 894000)).2
    nlinarith
  have hsqrt_upper : Real.sqrt x ≤ (12026689 : Real) / 10 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith
  have hxs : x ≤ (12026689 : Real) / 10 * Real.sqrt x := by
    calc
      x = Real.sqrt x * Real.sqrt x := by nlinarith [hsqrt_sq]
      _ ≤ (12026689 : Real) / 10 * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hsqrt_upper hsqrt_nonneg
  have hlinear :
      (100002841 : Real) / 100000000 * x -
          (9999 : Real) / 10000 * Real.sqrt x - x ≤ x / 36260 := by
    nlinarith
  have hmain : Chebyshev.theta x - x <
      (100002841 : Real) / 100000000 * x -
        (9999 : Real) / 10000 * Real.sqrt x - x := by
    linarith
  exact hmain.trans_le hlinear

end

end PrimeFactorUnimodality
