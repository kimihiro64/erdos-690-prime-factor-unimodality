import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime

set_option autoImplicit false

/-! # Shared finite row coverage for short prime intervals

The medium numerical part of the explicit interval theorem is naturally a
finite cover.  This module keeps the cover data separate from its consumer:
one row supplies one verified prime, and the cover theorem propagates that
prime to every real point in the row.  Thus a table of rows can be checked as
one list rather than as a collection of one-file witness replays. -/

namespace PrimeFactorUnimodality

noncomputable section

def logCubedUpper (x : Real) : Real :=
  x + x / (Real.log x) ^ 3

theorem logCubedUpper_monotoneOn :
    MonotoneOn logCubedUpper (Set.Ici (3275 : Real)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (3275 : Real))
  · have hlog : ContinuousOn (fun y : Real => Real.log y)
        (Set.Ici (3275 : Real)) := by
      exact continuousOn_id.log (by
        intro x hx
        have hx_pos : (0 : Real) < x := by
          norm_num at hx ⊢
          linarith
        simpa only [id_eq] using hx_pos.ne')
    have hden : ContinuousOn (fun y : Real => (Real.log y) ^ 3)
        (Set.Ici (3275 : Real)) := hlog.pow 3
    exact continuousOn_id.add
      (continuousOn_id.div hden (by
        intro x hx
        exact pow_ne_zero 3
          (Real.log_pos (by norm_num at hx ⊢; linarith)).ne'))
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici (3275 : Real))) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : (3275 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        simpa only [id_eq] using (show x ≠ 0 by linarith))
    have hden : DifferentiableOn ℝ
        (fun y : Real => (Real.log y) ^ 3)
        (interior (Set.Ici (3275 : Real))) :=
      hlog.pow 3
    exact differentiableOn_id.add
      (differentiableOn_id.div hden (by
        intro x hx
        exact pow_ne_zero 3
          (Real.log_pos (by norm_num at hx ⊢; linarith)).ne'))
  · intro x hx
    simp only [interior_Ici, Set.mem_Ioi] at hx
    have x_pos : 0 < x := by linarith
    have x_ne : x ≠ 0 := ne_of_gt x_pos
    have log_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have log_gt_three : (3 : Real) < Real.log x := by
      apply (Real.lt_log_iff_exp_lt x_pos).2
      have exp_three : Real.exp 3 < (3 : Real) ^ 3 := by
        calc
          Real.exp 3 = Real.exp 1 ^ 3 := by
            rw [show (3 : Real) = (3 : ℕ) * 1 by norm_num,
              Real.exp_nat_mul]
          _ < (3 : Real) ^ 3 := by
            exact pow_lt_pow_left₀ Real.exp_one_lt_three
              (Real.exp_pos 1).le (by norm_num)
      have : (3 : Real) ^ 3 < x := by
        have hx' : (3275 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        norm_num at ⊢
        linarith
      exact exp_three.trans this
    have log_cube_pos : 0 < (Real.log x) ^ 3 := by positivity
    have hden_ne : (Real.log x) ^ 3 ≠ 0 := ne_of_gt log_cube_pos
    have hlog := Real.hasDerivAt_log x_ne
    have hderiv := (hasDerivAt_id x).add
      ((hasDerivAt_id x).div (hlog.pow 3) hden_ne)
    simp only [id_eq] at hderiv
    norm_num at hderiv
    change 0 ≤ deriv (id + id / Real.log ^ 3) x
    rw [hderiv.deriv]
    field_simp [x_ne, log_pos.ne']
    have log_sq_pos : 0 < (Real.log x) ^ 2 := by positivity
    have log_four_pos : 0 < (Real.log x) ^ 4 := by positivity
    nlinarith [mul_pos log_sq_pos (by nlinarith [log_gt_three])]

structure LogCubedPrimeRow where
  left : Nat
  right : Nat
  prime : Nat
  left_large : 3275 ≤ left
  right_lt_prime : right < prime
  prime_prime : prime.Prime
  prime_upper : (prime : Real) ≤ logCubedUpper left

def LogCubedPrimeRowsCover (rows : List LogCubedPrimeRow) : Prop :=
  ∀ x : Real, 3275 ≤ x →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

/-! A bounded cover is the form used when the explicit analytic argument is
split at a large cutoff.  Keeping the cutoff in the proposition means the
finite table has no obligation to describe the unbounded range handled by the
theta-error argument. -/
def LogCubedPrimeRowsCoverUpTo (rows : List LogCubedPrimeRow) (X : Real) : Prop :=
  ∀ x : Real, 3275 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem logCubedPrimeRow_provides
    (upper_mono : ∀ {a b : Real}, 3275 ≤ a → a ≤ b →
      logCubedUpper a ≤ logCubedUpper b)
    (row : LogCubedPrimeRow) {x : Real}
    (left_mem : (row.left : Real) ≤ x)
    (right_mem : x ≤ row.right) :
    ∃ q : Nat, q.Prime ∧ x < q ∧ (q : Real) ≤ logCubedUpper x := by
  refine ⟨row.prime, row.prime_prime, ?_, ?_⟩
  · have right_lt_prime : (row.right : Real) < row.prime := by
      exact_mod_cast row.right_lt_prime
    have x_lt_prime : x < (row.prime : Real) :=
      (right_mem.trans_lt right_lt_prime)
    exact_mod_cast x_lt_prime
  · exact row.prime_upper.trans (upper_mono
      (by exact_mod_cast row.left_large) left_mem)

theorem hasLogCubedShortIntervalPrime_of_rows
    (upper_mono : ∀ {a b : Real}, 3275 ≤ a → a ≤ b →
      logCubedUpper a ≤ logCubedUpper b)
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCover rows) :
    HasLogCubedShortIntervalPrime := by
  intro x x_large
  obtain ⟨row, row_mem, left_mem, right_mem⟩ := cover x x_large
  exact logCubedPrimeRow_provides upper_mono row left_mem right_mem

theorem hasLogCubedShortIntervalPrime_of_rows_closed
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCover rows) :
    HasLogCubedShortIntervalPrime := by
  refine hasLogCubedShortIntervalPrime_of_rows ?_ cover
  intro a b ha hab
  exact logCubedUpper_monotoneOn ha (le_trans ha hab) hab

theorem hasLogCubedShortIntervalPrime_of_bounded_rows_and_large_x
    {rows : List LogCubedPrimeRow}
    (X : Real) (hX : (4e18 : Real) ≤ X)
    (cover : LogCubedPrimeRowsCoverUpTo rows X)
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    HasLogCubedShortIntervalPrime := by
  intro x hx
  by_cases hsmall : x ≤ X
  · obtain ⟨row, row_mem, left_mem, right_mem⟩ := cover x hx hsmall
    exact logCubedPrimeRow_provides
      (fun {a b} ha hab => logCubedUpper_monotoneOn ha (le_trans ha hab) hab)
      row left_mem right_mem
  · exact large_x_logCubedShortIntervalPrime thetaError x
      (hX.trans (le_of_lt (lt_of_not_ge hsmall)))

end

end PrimeFactorUnimodality
