import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCountingPart04


set_option autoImplicit false

/-! # Interfaces for explicit prime-counting estimates -/

namespace PrimeFactorUnimodality

noncomputable section

/-- Dusart's lower comparison function
`x / log x * (1 + 1 / log x)`. -/

def HasDusartPrimeCountingAsymptoticAbove (X : Real) : Prop :=
  ∀ x : Real, X ≤ x →
    ∃ E : Real,
      (Nat.primeCounting ⌊x⌋₊ : Real) =
        x / Real.log x *
          (1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E) ∧
        |E| ≤ (732 : Real) / 100 / (Real.log x) ^ 3

/-! The remaining quantitative statement can be supplied in the natural
unnormalized form produced by Abel summation.  This theorem performs the
normalization into Dusart's published `E` form entirely in Lean. -/
theorem hasDusartPrimeCountingAsymptoticAbove_of_explicitRemainder
    {X : Real} (hXpos : 0 < X) (hlogX : (20 : Real) < Real.log X)
    (hbound : ∀ x : Real, X ≤ x →
      |(Nat.primeCounting ⌊x⌋₊ : Real) -
          (x / Real.log x + x / (Real.log x) ^ 2 +
            2 * x / (Real.log x) ^ 3)| ≤
        (732 : Real) / 100 * x / (Real.log x) ^ 4) :
    HasDusartPrimeCountingAsymptoticAbove X := by
  intro x hx
  have hx_pos : 0 < x := by linarith
  have hlog_pos : 0 < Real.log x := by
    have hlogx : (20 : Real) < Real.log x :=
      lt_of_lt_of_le hlogX (Real.log_le_log hXpos hx)
    linarith
  let E : Real :=
    ((Nat.primeCounting ⌊x⌋₊ : Real) -
      (x / Real.log x + x / (Real.log x) ^ 2 +
        2 * x / (Real.log x) ^ 3)) * Real.log x / x
  refine ⟨E, ?_, ?_⟩
  · dsimp [E]
    field_simp [ne_of_gt hx_pos, ne_of_gt hlog_pos]
    ring
  · have hmain := hbound x hx
    have hscale : 0 ≤ Real.log x / x := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hmain hscale
    dsimp [E]
    rw [abs_div, abs_mul, abs_of_pos hlog_pos, abs_of_pos hx_pos]
    calc
      |(Nat.primeCounting ⌊x⌋₊ : Real) -
          (x / Real.log x + x / (Real.log x) ^ 2 +
            2 * x / (Real.log x) ^ 3)| * Real.log x / x ≤
          ((732 : Real) / 100 * x / (Real.log x) ^ 4) *
            (Real.log x / x) := by
              convert hscaled using 1 <;> ring
      _ = (732 : Real) / 100 / (Real.log x) ^ 3 := by
        field_simp [ne_of_gt hx_pos, ne_of_gt hlog_pos]

/-! The Abel-summation argument supplies the all-`x` remainder bound from the
explicit theta error and the finite core estimate.  This is the theorem that
connects those two analytic obligations to the Dusart asymptotic interface;
the latter is not imported as an external black box. -/
theorem hasDusartPrimeCountingAsymptoticAbove_of_core_and_theta_error
    {A C X : Real}
    (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (error : HasThetaLogFourthError A X) :
    HasDusartPrimeCountingAsymptoticAbove X := by
  have hX : 1 < X := by
    have hlog_pos : 0 < Real.log X := lt_of_lt_of_le (by norm_num) hlog
    exact (Real.log_pos_iff hXpos.le).mp hlog_pos
  apply hasDusartPrimeCountingAsymptoticAbove_of_explicitRemainder
    hXpos (by linarith [hlog])
  intro x hx
  exact primeCounting_remainder_abs_le_732
    hX h2X hx hA0 hA hC0 hC hlog hcore error

/-! Direct paper-facing form of Dusart Theorem 5.1.  The proof is the
kernel-checked Abel remainder estimate above followed by the elementary
normalization into the displayed error term; no declaration from the
unfinished IEANTN/Dusart file is used. -/
theorem dusartTheorem5_1_of_core_and_theta_error
    {A C X : Real}
    (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (error : HasThetaLogFourthError A X) :
    ∀ x : Real, X ≤ x → ∃ E : Real,
      ((Nat.primeCounting ⌊x⌋₊ : Real) =
        x / Real.log x *
          (1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E)) ∧
      |E| ≤ (732 : Real) / 100 / (Real.log x) ^ 3 := by
  exact hasDusartPrimeCountingAsymptoticAbove_of_core_and_theta_error
    hXpos h2X hA0 hA hC0 hC hlog hcore error

def HasDusartPublishedPrimeCountingBoundsAbove (X : Real) : Prop :=
  (∀ x : Real, X ≤ x →
    x / (Real.log x - 1) ≤ (Nat.primeCounting ⌊x⌋₊ : Real)) ∧
  (∀ x : Real, X ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤
      x / (Real.log x - (11 / 10 : Real)))

theorem hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic_from
    {X : Real} (hXpos : 0 < X) (hlogX : (20 : Real) < Real.log X)
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove X) :
    HasDusartPublishedPrimeCountingBoundsAbove X := by
  constructor
  · intro x hx
    obtain ⟨E, hformula, hE⟩ := asymptotic x hx
    have hlog : (20 : Real) < Real.log x :=
      lt_of_lt_of_le hlogX (Real.log_le_log hXpos hx)
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    rw [hformula]
    have hE_lower : -(732 : Real) / 100 / (Real.log x) ^ 3 ≤ E := by
      convert neg_le_of_abs_le hE using 1 <;> ring
    have hbracket :
        1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≥
          Real.log x / (Real.log x - 1) := by
      have hden : 0 < Real.log x - 1 := by linarith
      apply (div_le_iff₀ hden).2
      have hlog_cube : (0 : Real) < (Real.log x) ^ 3 := by positivity
      have hE_lower' : -(732 : Real) / 100 ≤ E * (Real.log x) ^ 3 :=
        (div_le_iff₀ hlog_cube).mp hE_lower
      have hE_prod := mul_le_mul_of_nonneg_right hE_lower' hden.le
      field_simp [hlog_pos.ne', hden.ne']
      nlinarith [hE_prod, sq_nonneg (Real.log x - 20)]
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbracket hfactor
    have htarget : x / Real.log x * (Real.log x / (Real.log x - 1)) =
        x / (Real.log x - 1) := by
      field_simp [hlog_pos.ne', (by linarith : Real.log x - 1 ≠ 0)]
    rw [htarget] at hmul
    exact hmul
  · intro x hx
    obtain ⟨E, hformula, hE⟩ := asymptotic x hx
    have hlog : (20 : Real) < Real.log x :=
      lt_of_lt_of_le hlogX (Real.log_le_log hXpos hx)
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    rw [hformula]
    have hE_upper : E ≤ (732 : Real) / 100 / (Real.log x) ^ 3 :=
      le_of_abs_le hE
    have hbracket :
        1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≤
          Real.log x / (Real.log x - (11 / 10 : Real)) := by
      have hden : 0 < Real.log x - (11 / 10 : Real) := by linarith
      apply (le_div_iff₀ hden).2
      have hlog_cube : (0 : Real) < (Real.log x) ^ 3 := by positivity
      have hE_upper' : E * (Real.log x) ^ 3 ≤ (732 : Real) / 100 :=
        (le_div_iff₀ hlog_cube).mp hE_upper
      have hE_prod := mul_le_mul_of_nonneg_right hE_upper' hden.le
      field_simp [hlog_pos.ne', hden.ne']
      nlinarith [hE_prod, sq_nonneg (Real.log x - 20)]
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbracket hfactor
    have htarget : x / Real.log x *
        (Real.log x / (Real.log x - (11 / 10 : Real))) =
        x / (Real.log x - (11 / 10 : Real)) := by
      field_simp [hlog_pos.ne', (by linarith : Real.log x - (11 / 10 : Real) ≠ 0)]
    rw [htarget] at hmul
    exact hmul

theorem hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartPublishedPrimeCountingBoundsAbove (4e9 : Real) :=
  hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic_from
    (by norm_num)
    (by
      apply (Real.lt_log_iff_exp_lt (by norm_num)).2
      have hexp_three : Real.exp 20 < (3 : Real) ^ 20 := by
        rw [show (20 : Real) = (20 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
        exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
          (by norm_num)
      have hthree : (3 : Real) ^ 20 < (4e9 : Real) := by norm_num
      exact hexp_three.trans hthree)
    asymptotic

theorem hasDusartPublishedPrimeCountingBounds_of_below_and_above
    {X : Real} (finite : HasDusartPublishedPrimeCountingBoundsBelow X)
    (tail : HasDusartPublishedPrimeCountingBoundsAbove X) :
    HasDusartPublishedPrimeCountingBounds := by
  constructor
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.1 x hx hsmall
    · exact tail.1 x (le_of_lt (lt_of_not_ge hsmall))
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.2 x hx hsmall
    · exact tail.2 x (le_of_lt (lt_of_not_ge hsmall))

theorem hasDusartPublishedPrimeCountingBounds_of_finite_and_asymptotic
    (finite : HasDusartPublishedPrimeCountingBoundsBelow (4e9 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartPublishedPrimeCountingBounds := by
  exact hasDusartPublishedPrimeCountingBounds_of_below_and_above finite
    (hasDusartPublishedPrimeCountingBoundsAbove_of_asymptotic asymptotic)

theorem hasDusartRealPrimeCountingBoundsAbove_of_asymptotic_from
    {X Y : Real} (hXpos : 0 < X) (hlogX : (20 : Real) < Real.log X)
    (hXY : X ≤ Y)
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove X) :
    HasDusartRealPrimeCountingBoundsAbove Y := by
  constructor
  · intro x hx
    have hXx : X ≤ x := hXY.trans hx
    obtain ⟨E, hformula, hE⟩ := asymptotic x hXx
    have hlog : (10 : Real) < Real.log x := by
      have hlog' := lt_of_lt_of_le hlogX (Real.log_le_log hXpos hXx)
      linarith
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    have hlog_sq : (100 : Real) < (Real.log x) ^ 2 := by
      nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog]
    have hlog_cube : (1000 : Real) < (Real.log x) ^ 3 := by
      nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog,
        mul_pos hlog_pos (show 0 < (Real.log x) ^ 2 by positivity)]
    rw [hformula]
    have hElower : -(732 : Real) / 100 / (Real.log x) ^ 3 ≤ E := by
      convert neg_le_of_abs_le hE using 1 <;> ring
    have hmain : (1 : Real) + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≥
        1 + 1 / Real.log x := by
      have hrem : (732 : Real) / 100 / (Real.log x) ^ 3 ≤
          2 / (Real.log x) ^ 2 := by
        field_simp
        nlinarith [hlog_cube]
      have hElower' : -(2 / (Real.log x) ^ 2) ≤ E := by
        calc
          -(2 / (Real.log x) ^ 2) ≤
              -((732 : Real) / 100 / (Real.log x) ^ 3) := by
                linarith
          _ ≤ E := by convert hElower using 1 <;> ring
      linarith
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have := mul_le_mul_of_nonneg_left hmain.le hfactor
    convert this using 1 <;> dsimp [dusartPiLower] <;> field_simp <;> ring
  · intro x hx
    have hXx : X ≤ x := hXY.trans hx
    obtain ⟨E, hformula, hE⟩ := asymptotic x hXx
    have hlog : (10 : Real) < Real.log x := by
      have hlog' := lt_of_lt_of_le hlogX (Real.log_le_log hXpos hXx)
      linarith
    have hlog_pos : 0 < Real.log x := by linarith
    have hx_pos : 0 < x := by linarith
    have hupper : (1 : Real) + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E ≤
        1 + (6381 : Real) / 5000 / Real.log x := by
      have hEupper : E ≤ (732 : Real) / 100 / (Real.log x) ^ 3 :=
        le_of_abs_le hE
      have hlog_sq : (100 : Real) < (Real.log x) ^ 2 := by
        nlinarith [mul_self_lt_mul_self (by norm_num : (0 : Real) ≤ 10) hlog]
      have hlog_pos' : 0 ≤ Real.log x := hlog_pos.le
      have hcoef :
          2 / (Real.log x) ^ 2 + (732 : Real) / 100 / (Real.log x) ^ 3 ≤
            (1381 : Real) / 5000 / Real.log x := by
        field_simp
        nlinarith
      calc
        1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 + E =
            1 + 1 / Real.log x + (2 / (Real.log x) ^ 2 + E) := by ring
        _ ≤ 1 + 1 / Real.log x +
            (2 / (Real.log x) ^ 2 + (732 : Real) / 100 /
              (Real.log x) ^ 3) := by linarith
        _ ≤ 1 + 1 / Real.log x + (1381 : Real) / 5000 / Real.log x :=
          by
            convert add_le_add_left hcoef (1 + 1 / Real.log x) using 1 <;> ring
        _ = 1 + (6381 : Real) / 5000 / Real.log x := by ring
    rw [hformula]
    dsimp [dusartPiUpper]
    have hfactor : 0 ≤ x / Real.log x := by positivity
    have := mul_le_mul_of_nonneg_left hupper hfactor
    convert this using 1 <;> dsimp [dusartPiUpper] <;> field_simp <;> ring

theorem hasDusartRealPrimeCountingBoundsAbove_of_asymptotic
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartRealPrimeCountingBoundsAbove (4e18 : Real) :=
  hasDusartRealPrimeCountingBoundsAbove_of_asymptotic_from
    (by norm_num)
    (by
      apply (Real.lt_log_iff_exp_lt (by norm_num)).2
      have hexp_three : Real.exp 20 < (3 : Real) ^ 20 := by
        rw [show (20 : Real) = (20 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
        exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
          (by norm_num)
      have hthree : (3 : Real) ^ 20 < (4e9 : Real) := by norm_num
      exact hexp_three.trans hthree)
    (by norm_num) asymptotic

/-! Direct composition of the kernel-checked Abel estimate with the published
comparison bounds.  This is the public all-cutoff theorem: the only analytic
inputs left are the explicit theta error and the finite core inequality. -/
theorem hasDusartRealPrimeCountingBoundsAbove_of_core_and_theta_error
    {A C X Y : Real}
    (hXpos : 0 < X) (h2X : 2 ≤ X) (hXY : X ≤ Y)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (error : HasThetaLogFourthError A X) :
    HasDusartRealPrimeCountingBoundsAbove Y := by
  have asymptotic : HasDusartPrimeCountingAsymptoticAbove X :=
    hasDusartPrimeCountingAsymptoticAbove_of_core_and_theta_error
      hXpos h2X hA0 hA hC0 hC hlog hcore error
  exact hasDusartRealPrimeCountingBoundsAbove_of_asymptotic_from
    hXpos (by linarith [hlog]) hXY asymptotic

/-! The finite theta-error interface is sufficient by itself for the real
prime-counting tail: the finite Abel core is derived at the same cutoff and
then fed into the explicit asymptotic conversion above. -/
theorem hasDusartRealPrimeCountingBoundsAbove_of_finite_theta_error
    {A X : Real} (hX : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (thetaErrorBelow : HasThetaLogFourthErrorBelow A X)
    (thetaErrorAbove : HasThetaLogFourthErrorAbove A X) :
    HasDusartRealPrimeCountingBoundsAbove X := by
  have thetaError : HasThetaLogFourthError A X := by
    intro x hx
    exact thetaErrorAbove x hx
  have hcore : |primeCountingCore X| ≤
      (3 / 5 : Real) * X / Real.log X ^ 4 :=
    primeCountingCore_abs_le_at_large_cutoff_of_theta_error
      hX hA0 hA1 thetaErrorBelow
  have hXpos : 0 < X := by linarith
  have h2X : 2 ≤ X := by linarith
  have hlogCut : (42 : Real) < Real.log (4e18 : Real) := by
    have hbase : Real.exp 1 < (2.72 : Real) := by
      linarith [Real.exp_one_lt_d9]
    have hexp : Real.exp 42 < (4e18 : Real) := by
      calc
        Real.exp 42 = Real.exp 1 ^ 42 := by
          rw [show (42 : Real) = (42 : ℕ) * 1 by norm_num,
            Real.exp_nat_mul]
        _ < (2.72 : Real) ^ 42 := by
          exact pow_lt_pow_left₀ hbase (Real.exp_pos 1).le (by norm_num)
        _ < (4e18 : Real) := by norm_num
    exact (Real.lt_log_iff_exp_lt (by norm_num)).2 hexp
  have hlogX : (42 : Real) ≤ Real.log X :=
    hlogCut.le.trans (Real.log_le_log (by norm_num) hX)
  exact hasDusartRealPrimeCountingBoundsAbove_of_core_and_theta_error
    hXpos h2X le_rfl hA0 hA1 (by norm_num) (by norm_num) hlogX hcore
    thetaError

theorem hasDusartRealPrimeCountingBounds_of_below_and_above
    {X : Real} (finite : HasDusartRealPrimeCountingBoundsBelow X)
    (tail : HasDusartRealPrimeCountingBoundsAbove X) :
    HasDusartRealPrimeCountingBounds := by
  constructor
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.1 x hx hsmall
    · exact tail.1 x (le_of_lt (lt_of_not_ge hsmall))
  · intro x hx
    by_cases hsmall : x ≤ X
    · exact finite.2 x hx hsmall
    · exact tail.2 x (le_of_lt (lt_of_not_ge hsmall))

theorem hasDusartRealPrimeCountingBounds_of_finite_and_core_and_theta_error
    {A C X Y : Real}
    (finite : HasDusartRealPrimeCountingBoundsBelow Y)
    (hXpos : 0 < X) (h2X : 2 ≤ X) (hXY : X ≤ Y)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (error : HasThetaLogFourthError A X) :
    HasDusartRealPrimeCountingBounds :=
  hasDusartRealPrimeCountingBounds_of_below_and_above finite
    (hasDusartRealPrimeCountingBoundsAbove_of_core_and_theta_error
      hXpos h2X hXY hA0 hA hC0 hC hlog hcore error)

theorem hasDusartRealPrimeCountingBounds_of_finite_and_asymptotic
    (finite : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartRealPrimeCountingBounds :=
  hasDusartRealPrimeCountingBounds_of_below_and_above finite
    (hasDusartRealPrimeCountingBoundsAbove_of_asymptotic asymptotic)

theorem hasDusartRealPrimeCountingBounds_of_finite_published_and_asymptotic
    (finite : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (finitePublished : HasDusartPublishedPrimeCountingBoundsBelow (4e9 : Real))
    (asymptotic : HasDusartPrimeCountingAsymptoticAbove (4e9 : Real)) :
    HasDusartRealPrimeCountingBounds := by
  have published : HasDusartPublishedPrimeCountingBounds :=
    hasDusartPublishedPrimeCountingBounds_of_finite_and_asymptotic
      finitePublished asymptotic
  exact hasDusartRealPrimeCountingBounds_of_below_and_above finite
    (hasDusartRealPrimeCountingBoundsAbove_of_published published)

theorem hasDusartRealPrimeCountingBounds_of_below_and_above_at_cutoff
    (finite : HasDusartRealPrimeCountingBoundsBelow (4e18 : Real))
    (tail : HasDusartRealPrimeCountingBoundsAbove (4e18 : Real)) :
    HasDusartRealPrimeCountingBounds :=
  hasDusartRealPrimeCountingBounds_of_below_and_above finite tail

theorem hasDusartPrimeCountingBounds_of_real
    (bounds : HasDusartRealPrimeCountingBounds) :
    HasDusartPrimeCountingBounds := by
  constructor
  · intro n hn
    simpa only [Nat.floor_natCast] using
      bounds.1 (n : Real) (by exact_mod_cast hn)
  · intro n hn
    simpa only [Nat.floor_natCast] using
      bounds.2 (n : Real) (by exact_mod_cast hn)

theorem hasDusartPrimeCountingBounds_of_finite_and_core_and_theta_error
    {A C X Y : Real}
    (finite : HasDusartRealPrimeCountingBoundsBelow Y)
    (hXpos : 0 < X) (h2X : 2 ≤ X) (hXY : X ≤ Y)
    (hA0 : 0 ≤ A) (hA : A ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (error : HasThetaLogFourthError A X) :
    HasDusartPrimeCountingBounds :=
  hasDusartPrimeCountingBounds_of_real
    (hasDusartRealPrimeCountingBounds_of_finite_and_core_and_theta_error
      finite hXpos h2X hXY hA0 hA hC0 hC hlog hcore error)

theorem hasDusartPrimeCountingBounds_of_finite_and_core_and_psiLogFourthError
    {A C X Y : Real}
    (finite : HasDusartRealPrimeCountingBoundsBelow Y)
    (hXpos : 0 < X) (h2X : 2 ≤ X) (hXY : X ≤ Y)
    (hXcutoff : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA_sharp : A + 148 / 1000 ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (psiError : HasPsiLogFourthError A X) :
    HasDusartPrimeCountingBounds := by
  apply hasDusartPrimeCountingBounds_of_finite_and_core_and_theta_error
    (A := A + 148 / 1000) finite hXpos h2X hXY (by linarith)
      hA_sharp hC0 hC hlog hcore
  exact hasThetaLogFourthError_of_psiLogFourthError_sharp hXcutoff psiError

theorem hasDusartPrimeCountingAsymptoticAbove_of_core_and_psiLogFourthError
    {A C X : Real}
    (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hXcutoff : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA_sharp : A + 148 / 1000 ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (psiError : HasPsiLogFourthError A X) :
    HasDusartPrimeCountingAsymptoticAbove X := by
  apply hasDusartPrimeCountingAsymptoticAbove_of_core_and_theta_error
    (A := A + 148 / 1000) hXpos h2X (by linarith) hA_sharp hC0 hC hlog hcore
  exact hasThetaLogFourthError_of_psiLogFourthError_sharp hXcutoff psiError

/-! The same prime-counting tail can consume a directly formalized
log-power decay estimate.  This keeps the analytic provider at the exact
cutoff instead of hiding it behind a published Dusart declaration. -/
theorem hasDusartPrimeCountingAsymptoticAbove_of_core_and_logRpowDecay
    {A C c α X : Real}
    (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hXcutoff : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA_sharp : A + 148 / 1000 ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (hdecay : HasPsiLogRpowDecay A c α X)
    (henvelope : ∀ x : Real, X ≤ x →
      A * Real.exp (-c * (Real.log x) ^ α) ≤
        A / (Real.log x) ^ (4 : ℕ)) :
    HasDusartPrimeCountingAsymptoticAbove X := by
  apply hasDusartPrimeCountingAsymptoticAbove_of_core_and_psiLogFourthError
    hXpos h2X hXcutoff hA0 hA_sharp hC0 hC hlog hcore
  exact hasPsiLogFourthError_of_logRpowDecay_of_envelope
    hXpos hdecay henvelope

theorem hasDusartPrimeCountingBounds_of_finite_and_core_and_relativePsiError
    {ε : Real → Real} {A C X Y : Real}
    (finite : HasDusartRealPrimeCountingBoundsBelow Y)
    (hXpos : 0 < X) (h2X : 2 ≤ X) (hXY : X ≤ Y)
    (hXcutoff : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA_sharp : A + 148 / 1000 ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (hε : HasPsiRelativeError ε)
    (hdecay : ∀ b : Real, Real.log X ≤ b → ε b ≤ A / b ^ 4) :
    HasDusartPrimeCountingBounds := by
  exact hasDusartPrimeCountingBounds_of_finite_and_core_and_psiLogFourthError
    finite hXpos h2X hXY hXcutoff hA0 hA_sharp hC0 hC hlog hcore
    (hasPsiLogFourthError_of_relativeError_decay hXpos (by linarith [hlog])
      hε hdecay)

theorem hasDusartPrimeCountingAsymptoticAbove_of_core_and_relativePsiError
    {ε : Real → Real} {A C X : Real}
    (hXpos : 0 < X) (h2X : 2 ≤ X)
    (hXcutoff : (4e18 : Real) ≤ X)
    (hA0 : 0 ≤ A) (hA_sharp : A + 148 / 1000 ≤ 1)
    (hC0 : 0 ≤ C) (hC : C ≤ 3 / 5)
    (hlog : (42 : Real) ≤ Real.log X)
    (hcore : |primeCountingCore X| ≤ C * X / Real.log X ^ 4)
    (hε : HasPsiRelativeError ε)
    (hdecay : ∀ b : Real, Real.log X ≤ b → ε b ≤ A / b ^ 4) :
    HasDusartPrimeCountingAsymptoticAbove X := by
  exact hasDusartPrimeCountingAsymptoticAbove_of_core_and_psiLogFourthError
    hXpos h2X hXcutoff hA0 hA_sharp hC0 hC hlog hcore
    (hasPsiLogFourthError_of_relativeError_decay hXpos (by linarith [hlog])
      hε hdecay)

theorem primeCounting_sub_lower_of_dusart
    (bounds : HasDusartPrimeCountingBounds)
    {x y : Nat} (hx : 2 ≤ x) (hy : 599 ≤ y) (hxy : x ≤ y) :
    dusartPiLower y - dusartPiUpper x ≤
      (Nat.primeCounting y - Nat.primeCounting x : Nat) := by
  have lower := bounds.1 y hy
  have upper := bounds.2 x hx
  have countMono := Nat.monotone_primeCounting hxy
  rw [Nat.cast_sub countMono]
  exact sub_le_sub lower upper

/-- A real lower bound exceeding a natural target yields the corresponding
natural lower bound on the number of primes in a shell. -/
theorem nat_le_primeCounting_sub_of_lt_dusart
    (bounds : HasDusartPrimeCountingBounds)
    {x y target : Nat} (hx : 2 ≤ x) (hy : 599 ≤ y) (hxy : x ≤ y)
    (numeric : (target : Real) < dusartPiLower y - dusartPiUpper x) :
    target + 1 ≤ Nat.primeCounting y - Nat.primeCounting x := by
  have lower := numeric.trans_le
    (primeCounting_sub_lower_of_dusart bounds hx hy hxy)
  exact_mod_cast lower

/-- A lower bound for a prime-counting shell, expressed in the same units as
an intended average-gap bound, directly supplies both discrete hypotheses of
the average-gap lemma.  This avoids introducing a rounded auxiliary target. -/
theorem count_and_width_of_dusart
    (bounds : HasDusartPrimeCountingBounds)
    {x y width bound : Nat} (hx : 2 ≤ x) (hy : 599 ≤ y) (hxy : x ≤ y)
    (bound_pos : 1 ≤ bound)
    (numeric : (width : Real) / bound + 1 <
      dusartPiLower y - dusartPiUpper x) :
    2 ≤ Nat.primeCounting y - Nat.primeCounting x ∧
      width < (Nat.primeCounting y - Nat.primeCounting x - 1) * bound := by
  let count := Nat.primeCounting y - Nat.primeCounting x
  have shellLower := primeCounting_sub_lower_of_dusart bounds hx hy hxy
  have countBound : (width : Real) / bound + 1 < (count : Real) := by
    exact numeric.trans_le (by simpa only [count] using shellLower)
  have boundRealPos : (0 : Real) < bound := by exact_mod_cast bound_pos
  have countGtOne : (1 : Real) < count := by
    have widthNonneg : (0 : Real) ≤ width := by positivity
    have divNonneg : (0 : Real) ≤ (width : Real) / bound :=
      div_nonneg widthNonneg boundRealPos.le
    linarith
  have countTwo : 2 ≤ count := by exact_mod_cast countGtOne
  refine ⟨by simpa only [count] using countTwo, ?_⟩
  have productBound : (width : Real) < ((count - 1) * bound : Nat) := by
    have divided : (width : Real) / bound < (count : Real) - 1 := by
      linarith
    rw [div_lt_iff₀ boundRealPos] at divided
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ count)]
    norm_num
    exact divided
  exact_mod_cast productBound

/-- A numerical lower bound for Dusart's comparison function converts
directly into an upper bound for an indexed prime. -/
theorem primeAt_le_of_dusart_lower
    (bounds : HasDusartPrimeCountingBounds) {i upper : Nat}
    (upper_large : 599 ≤ upper)
    (numeric : ((i + 1 : Nat) : Real) ≤ dusartPiLower upper) :
    primeAt i ≤ upper := by
  apply primeAt_le_of_succ_le_primeCounting'
  have castCount : ((i + 1 : Nat) : Real) ≤ Nat.primeCounting upper :=
    numeric.trans (bounds.1 upper upper_large)
  have natCount : i + 1 ≤ Nat.primeCounting upper := by exact_mod_cast castCount
  simpa only [Nat.primeCounting] using natCount

end

end PrimeFactorUnimodality
