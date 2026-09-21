import PrimeFactorUnimodality.Helpers.Analytic.DusartThetaClosedPart01
set_option autoImplicit false
namespace PrimeFactorUnimodality
noncomputable section
/-! # Closed explicit theta estimates (continued) -/
    ∃ A C : Real, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧
      LogDerivZetaHasBound A C := by
  obtain ⟨A, C, hC, hA, hbound, _⟩ :=
    zetaLogDeriv_explicit_bounded_and_holo
  exact ⟨A, C, hC, hA, hbound⟩
theorem wangCrapis_theta_upper_e28_from_paper_inputs
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi_error : |Chebyshev.psi x - x| ≤
      (2841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x ≤
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x ≤ x / 36260 := by
  exact dusart_theta_upper_e28_from_absolute_psi_error
    hx hx_exp hpsi_error hgap
theorem wangCrapis_theta_upper_e28_from_strict_paper_inputs
    {x : Real} (hx : (8e11 : Real) ≤ x)
    (hx_exp : x ≤ Real.exp 28)
    (hpsi : Chebyshev.psi x <
      (100002841 : Real) / 100000000 * x)
    (hgap : (9999 : Real) / 10000 * Real.sqrt x <
      Chebyshev.psi x - Chebyshev.theta x) :
    Chebyshev.theta x - x < x / 36260 := by
  exact dusart_theta_upper_e28_step_strict hx hx_exp hpsi hgap
/-! The finite upper half of Proposition 5.1 needs only the constant upper
    column of Table 6.6.  Keeping this one-sided assembler separate avoids
    making the finite upper estimate depend on the lower and correction
    columns, which are used by the independent lower-error argument. -/
theorem dusart_proposition_5_1_finite_upper_of_table66
    (prefix : ∀ x : Real, 0 < x → x ≤ (100000000 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (upper_zero : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ data.b0 * x) :
    ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260 := by
  intro x hx hX
  by_cases hsmall : x ≤ (100000000 : Real)
  · exact prefix x hx hsmall
  · obtain ⟨data, hdata, hleft, hright⟩ :=
      dusartThetaTable6_6CoefficientData_cover_real x
        (by linarith) hX
    have hupper := upper_zero data hdata x hleft hright
    have hb0 := (dusartThetaTable6_6CoefficientData_row_bounds data hdata).2.2.2.2
    have hxpos : 0 ≤ x := hx.le
    nlinarith
theorem dusart_proposition_5_1_finite_lower_error_of_table66
    (prefix : ∀ x : Real, 2 < x → x ≤ (100000000 : Real) →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x)
    (lower_one : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        x - data.a1 * x / Real.log x ≤ Chebyshev.theta x)
    (upper_zero : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ data.b0 * x) :
    ∀ x : Real, 2 < x → x ≤ (8e11 : Real) →
      |Chebyshev.theta x - x| <
        (12323 / 10000 : Real) * x / Real.log x := by
  intro x hx hX
  by_cases hsmall : x ≤ (100000000 : Real)
  · exact prefix x hx hsmall
  · obtain ⟨data, hdata, hleft, hright⟩ :=
      dusartThetaTable6_6CoefficientData_cover_real x
        (by linarith) hX
    have hlower := lower_one data hdata x hleft hright
    have hupper := upper_zero data hdata x hleft hright
    have ha1 := (dusartThetaTable6_6CoefficientData_side_conditions data hdata).2.1
    have hb0 := (dusartThetaTable6_6CoefficientData_row_bounds data hdata).2.2.2.2
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hupper_error : Chebyshev.theta x - x <
        (12323 / 10000 : Real) * x / Real.log x := by
      have htarget : 0 <
          (12323 / 10000 : Real) * x / Real.log x := by positivity
      nlinarith
    have hlower_error : -((12323 / 10000 : Real) * x /
        Real.log x) < Chebyshev.theta x - x := by
      have hcoef : data.a1 * x / Real.log x <
          (12323 / 10000 : Real) * x / Real.log x := by
        apply (div_lt_div_iff_of_pos_right hlogpos).2
        exact mul_lt_mul_of_pos_right ha1 hxpos
      nlinarith
    exact (abs_lt).2 ⟨hlower_error, hupper_error⟩
theorem hasDusartSymmetricThetaBoundsBelow_of_table66_one_zero
    (prefix : HasDusartSymmetricThetaBoundsBelow (100000000 : Real))
    (lower_one : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        x - data.a1 * x / Real.log x ≤ Chebyshev.theta x)
    (upper_zero : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ data.b0 * x) :
    HasDusartSymmetricThetaBoundsBelow (8e11 : Real) := by
  constructor
  · exact dusart_proposition_5_1_finite_upper_of_table66
      (fun x hx hX => prefix.1 x hx hX) upper_zero
  · exact dusart_proposition_5_1_finite_lower_error_of_table66
      (fun x hx hX => prefix.2 x hx hX) lower_one upper_zero
/-! Paper-facing assembly with the Table 6.6 finite range attached.  The
    middle psi estimate, Proposition 3.1 gap estimate, and global lower
    estimate remain explicit arguments because they arise from different
    parts of the published proof. -/
theorem wangCrapis_thetaBounds_of_table66_and_prop31_thetaError
    (prefix : HasDusartSymmetricThetaBoundsBelow (100000000 : Real))
    (lower_one : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        x - data.a1 * x / Real.log x ≤ Chebyshev.theta x)
    (upper_zero : ∀ data ∈ dusartThetaTable6_6CoefficientData,
      ∀ x : Real, (data.left : Real) ≤ x → x ≤ data.right →
        Chebyshev.theta x ≤ data.b0 * x)
    (middlePsi : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x)
    (finiteGap : ∀ x : Real, (121 : Real) < x →
      x < (4e18 : Real) ^ 2 →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (Real.exp 28))
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  have finite := hasDusartSymmetricThetaBoundsBelow_of_table66_one_zero
    prefix lower_one upper_zero
  exact wangCrapis_thetaBounds_of_paper_ranges_and_prop31_thetaError
    (fun x hx hX => finite.1 x hx hX) middlePsi finiteGap thetaError lower
/-! Paper-facing Proposition 5.1 assembler.  The three hypotheses correspond
to Dusart's finite table, middle explicit psi estimate, and large-range theta
estimate; none of the range-specific obligations is hidden in this glue. -/
theorem dusart_proposition_5_1_of_paper_ranges
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middle : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x ∧
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (tail : ∀ x : Real, Real.exp 28 ≤ x →
      Chebyshev.theta x - x < x / 36260) :
    ∀ x : Real, 0 < x →
      Chebyshev.theta x - x < x / 36260 := by
  intro x hx
  by_cases hfinite : x ≤ (8e11 : Real)
  · exact finite x hx hfinite
  by_cases hmiddle : x ≤ Real.exp 28
  · obtain ⟨herror, hgap⟩ := middle x (le_of_not_ge hfinite) hmiddle
    have hpsi : Chebyshev.psi x <
        (100002841 : Real) / 100000000 * x := by
      have hupper := (abs_lt.mp herror).2
      nlinarith
    exact dusart_theta_upper_e28_step_strict
      (le_of_not_ge hfinite) hmiddle hpsi hgap
  · exact tail x (le_of_not_ge hmiddle)
/-! Translate the paper's one-sided Proposition 5.1 estimate together with
its independent lower estimate into the exact theta-provider interface. -/
theorem wangCrapis_thetaBounds_of_paper_upper_and_lower
    (upper : ∀ x : Real, 0 < x →
      Chebyshev.theta x - x < x / 36260)
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  constructor
  · intro x hx
    have h := upper x hx
    nlinarith
  · exact lower
theorem wangCrapis_thetaBounds_of_paper_ranges
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middle : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x ∧
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (tail : ∀ x : Real, Real.exp 28 ≤ x →
      Chebyshev.theta x - x < x / 36260)
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_paper_upper_and_lower
  · exact dusart_proposition_5_1_of_paper_ranges finite middle tail
  · exact lower
/-! The large-range clause in Proposition 5.1 follows directly from the
explicit logarithm-fourth error once its cutoff is placed at `exp 28`. -/
theorem dusart_proposition_5_1_tail_of_logFourthError
    {A : Real}
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log (Real.exp 28) ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A (Real.exp 28)) :
    ∀ x : Real, Real.exp 28 ≤ x →
      Chebyshev.theta x - x < x / 36260 := by
  have hlog : (10 : Real) < Real.log (Real.exp 28) := by
    rw [Real.log_exp]
    norm_num
  have tail : HasDusartSymmetricThetaBoundsAbove (Real.exp 28) :=
    hasDusartSymmetricThetaBoundsAbove_of_logFourthError
      (by positivity) hlog hA_nonneg hA thetaError
  exact tail.1
/-! Paper-facing Proposition 5.1 assembly with the large-range analytic input
made explicit at its actual `exp 28` cutoff. -/
theorem wangCrapis_thetaBounds_of_paper_ranges_and_logFourthTail
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middle : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x ∧
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x)
    {A : Real}
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log (Real.exp 28) ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A (Real.exp 28)) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_paper_ranges finite middle
    (dusart_proposition_5_1_tail_of_logFourthError
      hA_nonneg hA thetaError) lower
/-! The middle-range gap in Proposition 5.1 is supplied by Proposition 3.1.
Its bounded verification remains a separate finite obligation; the analytic
tail and the conversion from the paper's `psi` error are assembled here. -/
theorem wangCrapis_thetaBounds_of_paper_ranges_and_prop31
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middlePsi : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x)
    (finiteGap : ∀ x : Real, (121 : Real) < x →
      x < (4e18 : Real) ^ 2 →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    {A : Real}
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log (Real.exp 28) ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A (Real.exp 28))
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_paper_ranges_and_logFourthTail
    finite
  · intro x hx hx_exp
    refine ⟨middlePsi x hx hx_exp, ?_⟩
    apply finiteGap x (by linarith)
    calc
      x ≤ Real.exp 28 := hx_exp
      _ < (1446257067000 : Real) := exp_twentyEight_lt_dusart_endpoint
      _ < (4e18 : Real) ^ 2 := by norm_num
  · exact lower
  · exact hA_nonneg
  · exact hA
  · exact thetaError
/-! A single published-size error input supplies both analytic tails: its
`exp 28` instance feeds Proposition 5.1, while monotonicity of the cutoff
feeds the square-root argument in Proposition 3.1. -/
theorem wangCrapis_thetaBounds_of_paper_ranges_and_prop31_thetaError
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middlePsi : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x)
    (finiteGap : ∀ x : Real, (121 : Real) < x →
      x < (4e18 : Real) ^ 2 →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (Real.exp 28))
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  have hA : (648 / 1000 : Real) / Real.log (Real.exp 28) ≤
      12167 / 500000 := by
    rw [Real.log_exp]
    norm_num
  have hcut : Real.exp 28 ≤ (4e18 : Real) := by
    calc
      Real.exp 28 < (1446257067000 : Real) :=
        exp_twentyEight_lt_dusart_endpoint
      _ ≤ (4e18 : Real) := by norm_num
  have thetaErrorLarge : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (4e18 : Real) := by
    exact hasThetaLogFourthErrorAbove_mono hcut thetaError
  have prop31 : ∀ x : Real, (121 : Real) < x →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x :=
    dusart_proposition_3_1_of_finite_and_thetaErrorAbove
      finiteGap thetaErrorLarge
  apply wangCrapis_thetaBounds_of_paper_ranges
    finite
  · intro x hx hx_exp
    refine ⟨middlePsi x hx hx_exp, ?_⟩
    apply prop31 x
    · linarith
    · calc
        x ≤ Real.exp 28 := hx_exp
        _ < (1446257067000 : Real) :=
          exp_twentyEight_lt_dusart_endpoint
        _ < (4e18 : Real) ^ 2 := by norm_num
  · exact dusart_proposition_5_1_tail_of_logFourthError
      (by norm_num) hA thetaError
  · exact lower
theorem wangCrapis_thetaBounds_of_indexed_prop31_rows_and_thetaError
    {X : Real} {n : Nat}
    (hX : (4e18 : Real) ^ 2 ≤ X)
    (rows : Fin n → DusartProposition31FiniteRow)
    (cover : DusartProposition31FiniteIndexedRowsCover rows X)
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middlePsi : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (Real.exp 28))
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_paper_ranges_and_prop31_thetaError
    finite middlePsi
  · intro x hx hxc
    exact dusartProposition31Finite_of_indexed_rows cover x hx
      (le_trans (le_of_lt hxc) hX)
  · exact thetaError
  · exact lower
theorem wangCrapis_thetaBounds_of_prop31_chunk_and_thetaError
    (chunk : DusartProposition31FiniteChunk)
    (hX : (4e18 : Real) ^ 2 ≤ chunk.cutoff)
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middlePsi : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (Real.exp 28))
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_indexed_prop31_rows_and_thetaError
    (X := chunk.cutoff) hX chunk.rows chunk.cover finite middlePsi
    thetaError lower
theorem wangCrapis_thetaBounds_of_prop31_chunks_and_thetaError
    (first : DusartProposition31FiniteChunk)
    (rest : List DusartProposition31FiniteChunk)
    (hX : (4e18 : Real) ^ 2 ≤
      (DusartProposition31FiniteChunk.appendMany first rest).cutoff)
    (finite : ∀ x : Real, 0 < x → x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middlePsi : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      |Chebyshev.psi x - x| < (2841 : Real) / 100000000 * x)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (Real.exp 28))
    (lower : ∀ x : Real, 2 < x →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_prop31_chunk_and_thetaError
    (DusartProposition31FiniteChunk.appendMany first rest) hX finite
    middlePsi thetaError lower
/-! Direct finite-prefix assembly for the provider interface.  The finite
upper and lower estimates are kept as separate obligations, as in the paper;
only the unbounded tail is converted from the explicit error estimate. -/
theorem wangCrapis_thetaBounds_of_paper_finite_prefix_and_logFourthTail
    {A X : Real}
    (hXpos : 0 < X)
    (hlogX : (10 : Real) < Real.log X)
    (finiteUpper : ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.theta x - x < x / 36260)
    (finiteLower : ∀ x : Real, 2 < x → x ≤ X →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthErrorAbove A X) :
    HasDusartThetaBounds := by
  have tail : HasDusartSymmetricThetaBoundsAbove X :=
    hasDusartSymmetricThetaBoundsAbove_of_logFourthError
      hXpos hlogX hA_nonneg hA thetaError
  constructor
  · intro x hx
    by_cases hsmall : x ≤ X
    · have h := finiteUpper x hx hsmall
      nlinarith
    · have h := tail.1 x (le_of_not_ge hsmall)
      nlinarith
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finiteLower x hx hsmall
    · have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
      have hlow := (abs_lt.mp (tail.2 x hx (le_of_not_ge hsmall))).1
      have htarget :
          x * (1 - (12323 / 10000 : Real) / Real.log x) =
            x - (12323 / 10000 : Real) * x / Real.log x := by
        field_simp [hlog_pos.ne']
      rw [htarget]
      linarith
/-! Specialization at the cutoff used in Dusart's Proposition 5.1. -/
theorem wangCrapis_thetaBounds_of_paper_finite_exp28
    (finiteUpper : ∀ x : Real, 0 < x → x ≤ Real.exp 28 →
      Chebyshev.theta x - x < x / 36260)
    (finiteLower : ∀ x : Real, 2 < x → x ≤ Real.exp 28 →
      x * (1 - (12323 / 10000 : Real) / Real.log x) <
        Chebyshev.theta x)
    (thetaError : HasThetaLogFourthErrorAbove
      (648 / 1000 : Real) (Real.exp 28)) :
    HasDusartThetaBounds := by
  apply wangCrapis_thetaBounds_of_paper_finite_prefix_and_logFourthTail
    (X := Real.exp 28) (A := (648 / 1000 : Real))
    (Real.exp_pos 28)
  · rw [Real.log_exp]
    norm_num
  · exact finiteUpper
  · exact finiteLower
  · norm_num
  · rw [Real.log_exp]
    norm_num
  · exact thetaError
/-! Global Proposition 5.1 in the three ranges used by Dusart: the finite
Table 6.4 range, the explicit middle range ending at `exp 28`, and the
large-range theta-error tail. -/
theorem dusart_proposition_5_1_of_three_ranges
    (finite : ∀ x : Real, 0 < x →
      x ≤ (8e11 : Real) →
      Chebyshev.theta x - x < x / 36260)
    (middle : ∀ x : Real, (8e11 : Real) ≤ x →
      x ≤ Real.exp 28 →
      Chebyshev.theta x - x < x / 36260)
    (tail : ∀ x : Real, Real.exp 28 ≤ x →
      Chebyshev.theta x - x < x / 36260) :
    ∀ x : Real, 0 < x →
      Chebyshev.theta x - x < x / 36260 := by
  intro x hx
  by_cases hfinite : x ≤ (8e11 : Real)
  · exact finite x hx hfinite
  · by_cases hmiddle : x ≤ Real.exp 28
    · exact middle x (le_of_not_ge hfinite) hmiddle
    · exact tail x (le_of_not_ge hmiddle)
/-! The finite part of the paper's Table 6.4 is represented by compact indexed
endpoint rows. The assembler proves both theta inequalities on every real
point covered by those rows, including points between consecutive endpoints. -/
theorem wangCrapis_thetaBounds_of_indexed_endpoint_rows_and_tail
    {A X : Real} {n : Nat}
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (rows : Fin n → DusartThetaEndpointRow)
    (cover : DusartThetaEndpointIndexedCoverUpTo rows X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_indexed_endpoint_rows cover)
    hA_nonneg hA thetaError
/-! The same boundary consumes compact endpoint chunks directly.  This keeps
    the generated finite table independent of the analytic tail proof. -/
theorem wangCrapis_thetaBounds_of_endpoint_chunks_and_tail
    {A : Real} (first : DusartThetaEndpointChunk)
    (rest : List DusartThetaEndpointChunk)
    (hXpos : 0 <
      (DusartThetaEndpointChunk.appendMany first rest).cutoff)
    (hlogX : (10 : Real) < Real.log
      (DusartThetaEndpointChunk.appendMany first rest).cutoff)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log
      (DusartThetaEndpointChunk.appendMany first rest).cutoff ≤
      12167 / 500000)
    (thetaError : HasThetaLogFourthError A
      (DusartThetaEndpointChunk.appendMany first rest).cutoff) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_endpoint_chunks first rest)
    hA_nonneg hA thetaError
theorem wangCrapis_thetaBounds_of_prefix_and_endpoint_chunks_and_tail
    {A x₀ : Real} (hx₀ : (2 : Real) ≤ x₀)
    (prefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (first : DusartThetaEndpointChunk)
    (rest : List DusartThetaEndpointChunk)
    (hcutoff : x₀ ≤
      (DusartThetaEndpointChunk.appendMany first rest).cutoff)
    (hXpos : 0 <
      (DusartThetaEndpointChunk.appendMany first rest).cutoff)
    (hlogX : (10 : Real) < Real.log
      (DusartThetaEndpointChunk.appendMany first rest).cutoff)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log
      (DusartThetaEndpointChunk.appendMany first rest).cutoff ≤
      12167 / 500000)
    (thetaError : HasThetaLogFourthError A
      (DusartThetaEndpointChunk.appendMany first rest).cutoff) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_indexed_prefix_and_endpoint_rows
      hx₀ prefix
      (by
        intro x hx hX
        obtain ⟨i, hleft, hright⟩ :=
          (DusartThetaEndpointChunk.appendMany first rest).cover x
            (hx₀.trans hx) hX
        exact ⟨i, hleft, hright⟩))
    hA_nonneg hA thetaError
/-! Paper-facing form when a separately proved prefix is followed by an
indexed Table 6.4 suffix. -/
theorem wangCrapis_thetaBounds_of_indexed_prefix_endpoint_rows_and_tail
    {A X x₀ : Real} {n : Nat}
    (hXpos : 0 < X) (hlogX : (10 : Real) < Real.log X)
    (hx₀ : (2 : Real) ≤ x₀)
    (prefix : HasDusartSymmetricThetaBoundsBelow x₀)
    (rows : Fin n → DusartThetaEndpointRow)
    (cover : DusartThetaEndpointIndexedCoverFrom rows x₀ X)
    (hA_nonneg : 0 ≤ A)
    (hA : A / Real.log X ≤ 12167 / 500000)
    (thetaError : HasThetaLogFourthError A X) :
    HasDusartThetaBounds := by
  exact wangCrapis_thetaBounds_of_logFourthTail hXpos hlogX
    (hasDusartSymmetricThetaBoundsBelow_of_indexed_prefix_and_endpoint_rows
      hx₀ prefix cover)
    hA_nonneg hA thetaError
end
end
end
