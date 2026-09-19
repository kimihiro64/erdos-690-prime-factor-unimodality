import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime
import PrimeFactorUnimodality.Helpers.Analytic.ThetaFromPsi
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitThetaBounds
import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCounting

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

def dusartUpper (x : Real) : Real :=
  x * (1 + (1 / 2 : Real) / (Real.log x) ^ 2)

theorem dusartUpper_monotoneOn :
    MonotoneOn dusartUpper (Set.Ici (3275 : Real)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (3275 : Real))
  · have hlog : ContinuousOn (fun y : Real => Real.log y)
        (Set.Ici (3275 : Real)) := by
      exact continuousOn_id.log (by
        intro x hx
        have hx_pos : (0 : Real) < x := by
          norm_num at hx ⊢
          linarith
        simpa only [id_eq] using hx_pos.ne')
    have hden : ContinuousOn (fun y : Real => (Real.log y) ^ 2)
        (Set.Ici (3275 : Real)) := hlog.pow 2
    exact continuousOn_id.mul
      (continuousOn_const.add
        (continuousOn_const.div hden (by
          intro x hx
          have : 0 < Real.log x := by
            exact Real.log_pos (by norm_num at hx ⊢; linarith)
          positivity)))
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici (3275 : Real))) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : (3275 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        simpa only [id_eq] using (show x ≠ 0 by linarith))
    have hden : DifferentiableOn ℝ
        (fun y : Real => (Real.log y) ^ 2)
        (interior (Set.Ici (3275 : Real))) := hlog.pow 2
    exact differentiableOn_id.mul
      ((differentiableOn_const (1 : Real)).add
        ((differentiableOn_const (1 / 2 : Real)).div hden (by
          intro x hx
          have : 0 < Real.log x := by
            exact Real.log_pos (by norm_num at hx ⊢; linarith)
          positivity)))
  · intro x hx
    simp only [interior_Ici, Set.mem_Ioi] at hx
    have x_ne : x ≠ 0 := by linarith
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog_gt_two : (2 : Real) < Real.log x := by
      apply (Real.lt_log_iff_exp_lt (by linarith)).2
      have hexp : Real.exp 2 < (9 : Real) := by
        rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
        have hone : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
        nlinarith [mul_self_lt_mul_self (Real.exp_pos 1).le hone]
      have : (9 : Real) < x := by linarith
      exact hexp.trans this
    have hderiv := (hasDerivAt_id x).mul
      ((hasDerivAt_const x (1 : Real)).add
        ((hasDerivAt_const x (1 / 2 : Real)).div
          ((Real.hasDerivAt_log x_ne).pow 2)
            (pow_ne_zero 2 hlog_pos.ne')))
    simp only [id_eq] at hderiv
    change 0 ≤ deriv (id * (fun y : Real =>
      1 + (1 / 2 : Real) / Real.log y ^ 2)) x
    have hfun : (id * (fun y : Real =>
        1 + (1 / 2 : Real) / Real.log y ^ 2)) =
        id * ((fun x : Real => 1) + (fun x : Real => 1 / 2) /
          Real.log ^ 2) := by
      funext y
      simp [Pi.mul_apply, Pi.add_apply, id_eq]
    rw [hfun]
    rw [hderiv.deriv]
    simp only [Pi.add_apply, Pi.div_apply, Pi.pow_apply]
    field_simp [x_ne, hlog_pos.ne']
    norm_num at *
    nlinarith [mul_pos (show 0 < Real.log x by linarith)
      (show 0 < (Real.log x) ^ 2 by positivity)]

structure DusartPrimeRow where
  left : Nat
  right : Nat
  prime : Nat
  left_large : 3275 ≤ left
  right_lt_prime : right < prime
  prime_prime : prime.Prime
  prime_upper : (prime : Real) ≤ dusartUpper left

def DusartPrimeRowsCoverBelow (rows : List DusartPrimeRow) : Prop :=
  ∀ x : Real, 3275 ≤ x → x ≤ 89693 →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem dusartPrimeRow_provides
    (row : DusartPrimeRow) {x : Real}
    (left_mem : (row.left : Real) ≤ x)
    (right_mem : x ≤ row.right) :
    ∃ q : Nat, q.Prime ∧ x < q ∧
      (q : Real) ≤ x * (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  refine ⟨row.prime, row.prime_prime, ?_, ?_⟩
  · have right_lt_prime : (row.right : Real) < row.prime := by
      exact_mod_cast row.right_lt_prime
    exact_mod_cast right_mem.trans_lt right_lt_prime
  · have hbound : (row.prime : Real) ≤ dusartUpper x :=
      row.prime_upper.trans (dusartUpper_monotoneOn
        (show (row.left : Real) ∈ Set.Ici (3275 : Real) by
          change (3275 : Real) ≤ row.left
          exact_mod_cast row.left_large)
        (show x ∈ Set.Ici (3275 : Real) by
          have hleft : (3275 : Real) ≤ row.left := by
            exact_mod_cast row.left_large
          norm_num at ⊢
          linarith [hleft, left_mem]) left_mem)
    have hrewrite : dusartUpper x =
        x * (1 + 1 / (2 * (Real.log x) ^ 2)) := by
      dsimp [dusartUpper]
      field_simp
    exact hrewrite ▸ hbound

theorem hasDusartShortIntervalPrimeBelow_of_rows
    {rows : List DusartPrimeRow}
    (cover : DusartPrimeRowsCoverBelow rows) :
    HasDusartShortIntervalPrimeBelow (89693 : Real) := by
  intro x hx hX
  obtain ⟨row, row_mem, left_mem, right_mem⟩ := cover x hx hX
  exact dusartPrimeRow_provides row left_mem right_mem

structure LogCubedPrimeRow where
  left : Nat
  right : Nat
  prime : Nat
  left_large : 89693 ≤ left
  right_lt_prime : right < prime
  prime_prime : prime.Prime
  prime_upper : (prime : Real) ≤ logCubedUpper left

def LogCubedPrimeRowsCover (rows : List LogCubedPrimeRow) : Prop :=
  ∀ x : Real, 89693 ≤ x →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

/-! A bounded cover is the form used when the explicit analytic argument is
split at a large cutoff.  Keeping the cutoff in the proposition means the
finite table has no obligation to describe the unbounded range handled by the
theta-error argument. -/
def LogCubedPrimeRowsCoverUpTo (rows : List LogCubedPrimeRow) (X : Real) : Prop :=
  ∀ x : Real, 89693 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

/-! A finite theta-error table has the same shape as the interval table, but
the row carries the analytic inequality which its (small) rational
certificate establishes.  Keeping this as a list-level interface is
important: the proof of the global estimate consumes one cover, while the
certificate generator may choose its own row width and arithmetic encoding.
No theorem about theta is imported here; every row must provide its own
kernel-checked local estimate. -/
structure ThetaLogFourthErrorRow (A : Real) where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  error : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    |Chebyshev.theta x - x| ≤ A * x / (Real.log x) ^ 4

def ThetaLogFourthErrorRowsCoverUpTo
    {A : Real} (rows : List (ThetaLogFourthErrorRow A)) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasThetaLogFourthErrorBelow_of_rows
    {A X : Real} {rows : List (ThetaLogFourthErrorRow A)}
    (cover : ThetaLogFourthErrorRowsCoverUpTo rows X) :
    HasThetaLogFourthErrorBelow A X := by
  intro x hx2 hxX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx2 hxX
  exact row.error x hleft hright

theorem hasThetaLogFourthError_of_rows_and_tail
    {A X : Real} {rows : List (ThetaLogFourthErrorRow A)}
    (cover : ThetaLogFourthErrorRowsCoverUpTo rows X)
    (tail : HasThetaLogFourthErrorAbove A X) :
    HasThetaLogFourthError A 2 := by
  exact hasThetaLogFourthError_of_below_and_above
    (hasThetaLogFourthErrorBelow_of_rows cover) tail

theorem hasThetaLogFourthError_of_rows_and_psiLogFourthError
    {A X : Real} {rows : List (ThetaLogFourthErrorRow (A + 148 / 1000))}
    (cover : ThetaLogFourthErrorRowsCoverUpTo rows X)
    (hXcutoff : (4e18 : Real) ≤ X)
    (psiError : HasPsiLogFourthError A X) :
    HasThetaLogFourthError (A + 148 / 1000) 2 := by
  apply hasThetaLogFourthError_of_rows_and_tail cover
  exact hasThetaLogFourthError_of_psiLogFourthError_sharp
    hXcutoff psiError

/-! Endpoint theta certificates are enough for an entire row.  The theta
function is monotone, while the logarithmic error envelope is handled by an
explicit numerator/denominator comparison. -/
structure ThetaLogFourthEndpointRow (A : Real) where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  theta_lower : Real
  theta_upper : Real
  theta_lower_le : theta_lower ≤ Chebyshev.theta left
  theta_right_le : Chebyshev.theta right ≤ theta_upper
  upper_error : theta_upper - left ≤
    A * (left : Real) / (Real.log right) ^ 4
  lower_error : right - theta_lower ≤
    A * (left : Real) / (Real.log right) ^ 4

def ThetaLogFourthEndpointRowsCoverUpTo
    {A : Real} (rows : List (ThetaLogFourthEndpointRow A)) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem thetaLogFourthEndpointRow_provides
    {A : Real} (hA0 : 0 ≤ A)
    (row : ThetaLogFourthEndpointRow A) {x : Real}
    (hleft : (row.left : Real) ≤ x) (hright : x ≤ row.right) :
    |Chebyshev.theta x - x| ≤ A * x / (Real.log x) ^ 4 := by
  have hleft2 : (2 : Real) ≤ row.left := by exact_mod_cast row.left_large
  have hright2 : (2 : Real) ≤ (row.right : Real) := by
    exact le_trans hleft2 (by exact_mod_cast row.left_le_right)
  have hx2 : (2 : Real) ≤ x := hleft2.trans hleft
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogr_pos : 0 < Real.log (row.right : Real) :=
    Real.log_pos (by linarith)
  have htheta_lower : row.theta_lower ≤ Chebyshev.theta x :=
    row.theta_lower_le.trans (Chebyshev.theta_mono hleft)
  have htheta_upper : Chebyshev.theta x ≤ row.theta_upper :=
    (Chebyshev.theta_mono hright).trans row.theta_right_le
  have hlog_mono : Real.log x ≤ Real.log (row.right : Real) :=
    Real.log_le_log (by linarith) hright
  have hlogsq : (Real.log x) ^ 4 ≤
      (Real.log (row.right : Real)) ^ 4 := by
    exact pow_le_pow_left' hlog_mono 4
  have hratio : (row.left : Real) /
      (Real.log (row.right : Real)) ^ 4 ≤
      x / (Real.log x) ^ 4 := by
    apply (div_le_div_iff₀ (pow_pos hlogr_pos 4)
      (pow_pos hlogx_pos 4)).2
    calc
      (row.left : Real) * (Real.log x) ^ 4 ≤
          (row.left : Real) * (Real.log (row.right : Real)) ^ 4 :=
        mul_le_mul_of_nonneg_left hlogsq (by positivity)
      _ ≤ x * (Real.log (row.right : Real)) ^ 4 :=
        mul_le_mul_of_nonneg_right hleft (by positivity)
  have henvelope : A * (row.left : Real) /
      (Real.log (row.right : Real)) ^ 4 ≤ A * x /
        (Real.log x) ^ 4 :=
    mul_le_mul_of_nonneg_left hratio hA0
  have hupper : Chebyshev.theta x - x ≤
      A * x / (Real.log x) ^ 4 := by
    calc
      Chebyshev.theta x - x ≤ row.theta_upper - row.left := by linarith
      _ ≤ A * (row.left : Real) /
          (Real.log (row.right : Real)) ^ 4 := row.upper_error
      _ ≤ A * x / (Real.log x) ^ 4 := henvelope
  have hlower : -(A * x / (Real.log x) ^ 4) ≤
      Chebyshev.theta x - x := by
    calc
      -(A * x / (Real.log x) ^ 4) ≤
          -(A * (row.left : Real) /
            (Real.log (row.right : Real)) ^ 4) := by linarith
      _ ≤ -(row.right - row.theta_lower) := by linarith [row.lower_error]
      _ ≤ Chebyshev.theta x - x := by linarith
  exact (abs_le).2 ⟨hlower, hupper⟩

theorem hasThetaLogFourthErrorBelow_of_endpoint_rows
    {A X : Real} (hA0 : 0 ≤ A)
    {rows : List (ThetaLogFourthEndpointRow A)}
    (cover : ThetaLogFourthEndpointRowsCoverUpTo rows X) :
    HasThetaLogFourthErrorBelow A X := by
  intro x hx2 hxX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx2 hxX
  exact thetaLogFourthEndpointRow_provides hA0 row hleft hright

theorem logCubedPrimeRow_provides
    (upper_mono : ∀ {a b : Real}, 89693 ≤ a → a ≤ b →
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
    (upper_mono : ∀ {a b : Real}, 89693 ≤ a → a ≤ b →
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
  exact logCubedUpper_monotoneOn (by norm_num at ⊢; linarith)
    (by norm_num at ⊢; linarith) hab

theorem hasLogCubedShortIntervalPrimeBelow_of_rows
    {X : Real} {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows X) :
    HasLogCubedShortIntervalPrimeBelow X := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  exact logCubedPrimeRow_provides
    (fun {a b} ha hab => logCubedUpper_monotoneOn
      (by norm_num at ⊢; linarith)
      (by norm_num at ⊢; linarith) hab)
    row hleft hright

structure DusartThetaBoundsRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  upper : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    Chebyshev.theta x - x < x / 36260
  lower : ∀ x : Real, 2 < x → (left : Real) ≤ x → x ≤ right →
    |Chebyshev.theta x - x| <
      (12323 / 10000 : Real) * x / Real.log x

def DusartThetaBoundsRowsCoverUpTo
    (rows : List DusartThetaBoundsRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasDusartSymmetricThetaBoundsBelow_of_rows
    {X : Real} {rows : List DusartThetaBoundsRow}
    (cover : DusartThetaBoundsRowsCoverUpTo rows X) :
    HasDusartSymmetricThetaBoundsBelow X := by
  apply hasDusartSymmetricThetaBoundsBelow_of_upper_lower
  · intro x hx hX
    by_cases hsmall : x < 2
    · rw [Chebyshev.theta_eq_zero_of_lt_two hsmall]
      nlinarith
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact row.upper x hleft hright
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x
      (by linarith) hX
    exact row.lower x hx hleft hright

structure DusartPrimeCountingRow where
  left : Nat
  right : Nat
  left_large : 2 ≤ left
  left_le_right : left ≤ right
  lower : ∀ x : Real, (599 : Real) ≤ x → (left : Real) ≤ x →
    x ≤ right →
    dusartPiLower x ≤ (Nat.primeCounting ⌊x⌋₊ : Real)
  upper : ∀ x : Real, (left : Real) ≤ x → x ≤ right →
    (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x

def DusartPrimeCountingRowsCoverUpTo
    (rows : List DusartPrimeCountingRow) (X : Real) : Prop :=
  ∀ x : Real, 2 ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

/-! The lower Dusart estimate starts only at `599`.  This variant keeps that
fact visible, so the finite table need not carry rows whose only purpose is
to establish the lower bound below `599`; the short upper range is supplied
by a separate elementary or computational lemma. -/
def DusartPrimeCountingRowsCoverFrom599
    (rows : List DusartPrimeCountingRow) (X : Real) : Prop :=
  ∀ x : Real, (599 : Real) ≤ x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x ≤ row.right

theorem hasDusartRealPrimeCountingBoundsBelow_of_rows_from599
    {X : Real} {rows : List DusartPrimeCountingRow}
    (cover : DusartPrimeCountingRowsCoverFrom599 rows X)
    (smallUpper : ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
    exact row.lower x hx hleft hright
  · intro x hx hX
    by_cases hsmall : x < 599
    · exact smallUpper x hx hsmall
    · obtain ⟨row, hrow, hleft, hright⟩ := cover x
        (le_of_not_gt hsmall) hX
      exact row.upper x hleft hright

theorem hasDusartRealPrimeCountingBoundsBelow_of_rows
    {X : Real} {rows : List DusartPrimeCountingRow}
    (cover : DusartPrimeCountingRowsCoverUpTo rows X) :
    HasDusartRealPrimeCountingBoundsBelow X := by
  constructor
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x (by linarith) hX
    exact row.lower x hx hleft hright
  · intro x hx hX
    obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
    exact row.upper x hleft hright

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
      (fun {a b} ha hab => logCubedUpper_monotoneOn (by norm_num at ⊢; linarith)
        (by norm_num at ⊢; linarith) hab)
      row left_mem right_mem
  · exact large_x_logCubedShortIntervalPrime thetaError x
      (hX.trans (le_of_lt (lt_of_not_ge hsmall)))

theorem hasLogCubedShortIntervalPrime_of_rows_at_large_cutoff
    {rows : List LogCubedPrimeRow}
    (cover : LogCubedPrimeRowsCoverUpTo rows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    HasLogCubedShortIntervalPrime :=
  hasLogCubedShortIntervalPrime_of_bounded_rows_and_large_x
    (4e18 : Real) le_rfl cover thetaError

theorem hasDusartShortIntervalPrime_of_rows_and_thetaError
    {dusartRows : List DusartPrimeRow}
    (dusartCover : DusartPrimeRowsCoverBelow dusartRows)
    {logRows : List LogCubedPrimeRow}
    (logCover : LogCubedPrimeRowsCoverUpTo logRows (4e18 : Real))
    (thetaError : HasThetaLogCubedError (12167 / 500000 : Real) (4e18 : Real)) :
    HasDusartShortIntervalPrime := by
  exact hasDusartShortIntervalPrime_of_below_and_logCubed
    (hasDusartShortIntervalPrimeBelow_of_rows dusartCover)
    (hasLogCubedShortIntervalPrime_of_rows_at_large_cutoff logCover thetaError)

end

end PrimeFactorUnimodality
