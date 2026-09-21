import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import PrimeFactorUnimodality.Helpers.Analytic.DecayToLogFourth
import PrimeFactorUnimodality.Helpers.Analytic.ElementaryLogBounds
import PrimeFactorUnimodality.Helpers.Analytic.RelativePsiTheta
import PrimeFactorUnimodality.Helpers.Analytic.ShortIntervalPrime
import PrimeFactorUnimodality.Helpers.Analytic.ThetaFromPsi
import PrimeFactorUnimodality.Helpers.PrimeSequence.AverageGap


set_option autoImplicit false

/-! # Interfaces for explicit prime-counting estimates -/

namespace PrimeFactorUnimodality

noncomputable section

/-- Dusart's lower comparison function
`x / log x * (1 + 1 / log x)`. -/

def dusartPiLower (x : Real) : Real :=
  x / Real.log x * (1 + 1 / Real.log x)

/-- Dusart's upper comparison function
`x / log x * (1 + 1.2762 / log x)`, with the decimal represented exactly. -/
def dusartPiUpper (x : Real) : Real :=
  x / Real.log x * (1 + (6381 / 5000 : Real) / Real.log x)

theorem log_nat_le_smooth_upper {n a b c : Nat} (hn : 0 < n)
    (hbound : n ≤ 2 ^ a * 3 ^ b * 5 ^ c) :
    Real.log n ≤ (a : Real) * (693148 / 1000000 : Real) +
      (b : Real) * (1098613 / 1000000 : Real) +
      (c : Real) * (1609438 / 1000000 : Real) := by
  have hsmooth := LogTables.log_le_smooth
    (x := (n : Real)) (a := a) (b := b) (c := c)
    (by exact_mod_cast hn)
    (by exact_mod_cast hbound)
  have h2 := mul_le_mul_of_nonneg_left LogTables.log_2_lt.le
    (by positivity : (0 : Real) ≤ a)
  have h3 := mul_le_mul_of_nonneg_left LogTables.log_3_lt.le
    (by positivity : (0 : Real) ≤ b)
  have h5 := mul_le_mul_of_nonneg_left LogTables.log_5_lt.le
    (by positivity : (0 : Real) ≤ c)
  norm_num at h2 h3 h5
  linarith

theorem log_nat_le_smooth_upper_with_seven {n a b c d : Nat} (hn : 0 < n)
    (hbound : n ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    Real.log n ≤ (a : Real) * (693148 / 1000000 : Real) +
      (b : Real) * (1098613 / 1000000 : Real) +
      (c : Real) * (1609438 / 1000000 : Real) +
      (d : Real) * (1946044 / 1000000 : Real) := by
  have hsmooth := LogTables.log_le_smooth_with_seven
    (x := (n : Real)) (a := a) (b := b) (c := c) (d := d)
    (by exact_mod_cast hn)
    (by exact_mod_cast hbound)
  have h2 := mul_le_mul_of_nonneg_left LogTables.log_2_lt.le
    (by positivity : (0 : Real) ≤ a)
  have h3 := mul_le_mul_of_nonneg_left LogTables.log_3_lt.le
    (by positivity : (0 : Real) ≤ b)
  have h5 := mul_le_mul_of_nonneg_left LogTables.log_5_lt.le
    (by positivity : (0 : Real) ≤ c)
  have h7 := mul_le_mul_of_nonneg_left LogTables.log_7_lt.le
    (by positivity : (0 : Real) ≤ d)
  norm_num at h2 h3 h5 h7
  linarith

/-! The upper comparison function is increasing once the logarithm is past
`2`.  This elementary fact lets the small prime-counting range be checked at
integer floors instead of by a separate real interval certificate. -/
theorem dusartPiUpper_monotoneOn :
    MonotoneOn dusartPiUpper (Set.Ici (10 : Real)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (10 : Real))
  · have hlog : ContinuousOn (fun y : Real => Real.log y)
        (Set.Ici (10 : Real)) := by
      exact continuousOn_id.log (by
        intro x hx
        have hx' : (10 : Real) ≤ x := hx
        have hx_pos : (0 : Real) < x := by linarith
        simpa only [id_eq] using hx_pos.ne')
    exact (continuousOn_id.div hlog (by
      intro x hx
      have hx' : (10 : Real) ≤ x := hx
      exact (Real.log_pos (by linarith)).ne')).mul
      (continuousOn_const.add (continuousOn_const.div hlog (by
        intro x hx
        have hx' : (10 : Real) ≤ x := hx
        exact (Real.log_pos (by linarith)).ne')))
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici (10 : Real))) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : (10 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        simpa only [id_eq] using (show x ≠ 0 by linarith))
    exact (differentiableOn_id.div hlog (by
      intro x hx
      exact (Real.log_pos (by
        have hx' : (10 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        linarith)).ne')).mul
      ((differentiableOn_const (1 : Real)).add
        ((differentiableOn_const (6381 / 5000 : Real)).div hlog (by
          intro x hx
          exact (Real.log_pos (by
            have hx' : (10 : Real) < x := by
              simpa only [interior_Ici, Set.mem_Ioi] using hx
            linarith)).ne')))
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
    have hderiv := ((hasDerivAt_id x).div
      (Real.hasDerivAt_log x_ne) hlog_pos.ne').mul
      ((hasDerivAt_const x (1 : Real)).add
        ((hasDerivAt_const x (6381 / 5000 : Real)).div
          (Real.hasDerivAt_log x_ne) hlog_pos.ne'))
    simp only [id_eq] at hderiv
    change 0 ≤ deriv (id / Real.log *
      ((fun _ : Real => 1) + (fun _ : Real => 6381 / 5000) / Real.log)) x
    rw [hderiv.deriv]
    simp only [Pi.add_apply, Pi.div_apply, id_eq]
    field_simp [x_ne, hlog_pos.ne']
    have hfirst : 0 < Real.log x * (Real.log x - 1) := by
      exact mul_pos hlog_pos (by linarith [hlog_gt_two])
    have hsecond : 0 < (6381 / 5000 : Real) * (Real.log x - 2) := by
      exact mul_pos (by norm_num) (by linarith [hlog_gt_two])
    nlinarith

theorem dusartPiLower_monotoneOn :
    MonotoneOn dusartPiLower (Set.Ici (599 : Real)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (599 : Real))
  · have hlog : ContinuousOn (fun y : Real => Real.log y)
        (Set.Ici (599 : Real)) := by
      exact continuousOn_id.log (by
        intro x hx
        have hx' : (599 : Real) ≤ x := hx
        have hx_pos : (0 : Real) < x := by linarith
        simpa only [id_eq] using hx_pos.ne')
    exact (continuousOn_id.div hlog (by
      intro x hx
      have hx' : (599 : Real) ≤ x := hx
      exact (Real.log_pos (by linarith)).ne')).mul
      (continuousOn_const.add (continuousOn_const.div hlog (by
        intro x hx
        have hx' : (599 : Real) ≤ x := hx
        exact (Real.log_pos (by linarith)).ne')))
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici (599 : Real))) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : (599 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        simpa only [id_eq] using (show x ≠ 0 by linarith))
    exact (differentiableOn_id.div hlog (by
      intro x hx
      exact (Real.log_pos (by
        have hx' : (599 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        linarith)).ne')).mul
      ((differentiableOn_const (1 : Real)).add
        ((differentiableOn_const (1 : Real)).div hlog (by
          intro x hx
          exact (Real.log_pos (by
            have hx' : (599 : Real) < x := by
              simpa only [interior_Ici, Set.mem_Ioi] using hx
            linarith)).ne')))
  · intro x hx
    simp only [interior_Ici, Set.mem_Ioi] at hx
    have x_ne : x ≠ 0 := by linarith
    have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog_gt_two : (2 : Real) < Real.log x := by
      have hlog599 : (2 : Real) < Real.log (599 : Real) := by
        apply (Real.lt_log_iff_exp_lt (by norm_num)).2
        have hexp : Real.exp 2 < (9 : Real) := by
          rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
          have hone : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
          nlinarith [mul_self_lt_mul_self (Real.exp_pos 1).le hone]
        exact hexp.trans (by norm_num)
      exact hlog599.trans_le (Real.log_le_log (by norm_num) (le_of_lt hx))
    have hderiv := ((hasDerivAt_id x).div
      (Real.hasDerivAt_log x_ne) hlog_pos.ne').mul
      ((hasDerivAt_const x (1 : Real)).add
        ((hasDerivAt_const x (1 : Real)).div
          (Real.hasDerivAt_log x_ne) hlog_pos.ne'))
    simp only [id_eq] at hderiv
    change 0 ≤ deriv (id / Real.log *
      ((fun _ : Real => 1) + (fun _ : Real => 1) / Real.log)) x
    rw [hderiv.deriv]
    simp only [Pi.add_apply, Pi.div_apply, id_eq]
    field_simp [x_ne, hlog_pos.ne']
    nlinarith [sq_pos_of_pos hlog_pos, hlog_gt_two]

/-! For the remaining bounded range, monotonicity reduces a real-variable
upper estimate to integer-floor checks, with only the tiny interval `[2,10)`
left as a direct elementary obligation. -/
theorem real_primeCounting_upper_of_integer_certificate
    (small : ∀ x : Real, 2 ≤ x → x < 10 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x)
    (certificate : ∀ n : Nat, 10 ≤ n → n < 599 →
      (Nat.primeCounting n : Real) ≤ dusartPiUpper n) :
    ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x := by
  intro x hx2 hx599
  by_cases hsmall : x < 10
  · exact small x hx2 hsmall
  · let n : Nat := ⌊x⌋₊
    have hx0 : 0 ≤ x := by linarith
    have hn10 : 10 ≤ n := by
      exact Nat.le_floor (le_of_not_gt hsmall)
    have hnn : n < 599 := (Nat.floor_lt hx0).2 hx599
    have hcert := certificate n hn10 hnn
    have hnle : (n : Real) ≤ x := by
      exact Nat.floor_le hx0
    have hmono : dusartPiUpper (n : Real) ≤ dusartPiUpper x :=
      dusartPiUpper_monotoneOn (show (10 : Real) ≤ n by exact_mod_cast hn10)
        (show (10 : Real) ≤ x from le_of_not_gt hsmall)
        hnle
    simpa [n] using hcert.trans hmono

/-! The only real-variable prime-counting range below `10` is elementary.
The proof uses exact `π 9 = 4` and certified decimal logarithm bounds; no
analytic prime-counting estimate is hidden here. -/
theorem dusartPrimeCounting_upper_below_ten :
    ∀ x : Real, 2 ≤ x → x < 10 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x := by
  intro x hx2 hx10
  have hx0 : 0 ≤ x := by linarith
  have hfloor : ⌊x⌋₊ < 10 := (Nat.floor_lt hx0).2 hx10
  have hcount : (Nat.primeCounting ⌊x⌋₊ : Real) ≤ 4 := by
    have hmono := Nat.monotone_primeCounting (show ⌊x⌋₊ ≤ 9 by omega)
    have hpi9 : Nat.primeCounting 9 = 4 := by decide
    exact_mod_cast (show Nat.primeCounting ⌊x⌋₊ ≤ 4 by simpa [hpi9] using hmono)
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have interval_lower : ∀ (a b L : Real),
      0 < a → a ≤ x → x ≤ b → 0 < L → Real.log x ≤ L →
      4 ≤ a / L + (6381 / 5000 : Real) * a / L ^ 2 →
      4 ≤ dusartPiUpper x := by
    intro a b L ha hax hxb hL hlogL hnumeric
    have hfirst : a / L ≤ x / Real.log x := by
      apply (div_le_div_iff₀ hL hlog_pos).2
      calc
        a * Real.log x ≤ a * L := mul_le_mul_of_nonneg_left hlogL ha.le
        _ ≤ x * L := mul_le_mul_of_nonneg_right hax hL.le
    have hlogsq : (Real.log x) ^ 2 ≤ L ^ 2 := by
      nlinarith [sq_nonneg (L - Real.log x), hlogL]
    have hsecond : (6381 / 5000 : Real) * a / L ^ 2 ≤
        (6381 / 5000 : Real) * x / (Real.log x) ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hL) (sq_pos_of_pos hlog_pos)).2
      have hcross : a * (Real.log x) ^ 2 ≤ x * L ^ 2 := by
        calc
          a * (Real.log x) ^ 2 ≤ a * L ^ 2 :=
            mul_le_mul_of_nonneg_left hlogsq ha.le
          _ ≤ x * L ^ 2 :=
            mul_le_mul_of_nonneg_right hax (sq_nonneg L)
      convert (mul_le_mul_of_nonneg_left hcross
        (by norm_num : (0 : Real) ≤ 6381 / 5000)) using 1 <;> ring
    calc
      4 ≤ a / L + (6381 / 5000 : Real) * a / L ^ 2 := hnumeric
      _ ≤ x / Real.log x + (6381 / 5000 : Real) * x /
          (Real.log x) ^ 2 := add_le_add hfirst hsecond
      _ = dusartPiUpper x := by
        dsimp [dusartPiUpper]
        ring
  have hupper : 4 ≤ dusartPiUpper x := by
    by_cases h25 : x < (5 / 2 : Real)
    · refine interval_lower 2 (5 / 2) (916292 / 1000000)
        (by norm_num) (by linarith) (by linarith) (by norm_num) ?_ ?_
      have hlogle : Real.log x ≤ (916292 / 1000000 : Real) := by
        calc
          Real.log x ≤ Real.log (5 / 2) :=
            Real.log_le_log (by linarith [hx2]) (by linarith)
          _ = Real.log 5 - Real.log 2 := by
            rw [Real.log_div (by norm_num) (by norm_num)]
          _ ≤ 916292 / 1000000 := by
            nlinarith [LogTables.log_5_lt, LogTables.log_2_gt]
      · exact hlogle
      · norm_num
    · by_cases h3 : x < 3
      · apply interval_lower (5 / 2) 3 (1098613 / 1000000)
          (by norm_num) (by linarith) (by linarith) (by norm_num)
        · have hlogx3 : Real.log x ≤ Real.log 3 :=
            Real.log_le_log (by linarith) (by linarith)
          have hrat : (1.098613 : Real) ≤ 1098613 / 1000000 := by norm_num
          exact (hlogx3.trans_lt (LogTables.log_3_lt.trans_le hrat)).le
        · norm_num
      · by_cases h4 : x < 4
        · apply interval_lower 3 4 (1386296 / 1000000)
            (by norm_num) (by linarith) (by linarith) (by norm_num)
          · calc
              Real.log x ≤ Real.log 4 := Real.log_le_log (by linarith) (by linarith)
              _ = 2 * Real.log 2 := by
                rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
                norm_num
              _ ≤ 1386296 / 1000000 := by
                nlinarith [LogTables.log_2_lt]
          · norm_num
        · by_cases h5 : x < 5
          · apply interval_lower 4 5 (1609438 / 1000000)
              (by norm_num) (by linarith) (by linarith) (by norm_num)
            · have hlogx5 : Real.log x ≤ Real.log 5 :=
                Real.log_le_log (by linarith) (by linarith)
              have hrat : (1.609438 : Real) ≤ 1609438 / 1000000 := by norm_num
              exact (hlogx5.trans_lt (LogTables.log_5_lt.trans_le hrat)).le
            · norm_num
          · by_cases h6 : x < 6
            · apply interval_lower 5 6 (1791761 / 1000000)
                (by norm_num) (by linarith) (by linarith) (by norm_num)
              · calc
                  Real.log x ≤ Real.log 6 := Real.log_le_log (by linarith) (by linarith)
                  _ = Real.log 2 + Real.log 3 := by
                    rw [show (6 : Real) = 2 * 3 by norm_num,
                      Real.log_mul (by norm_num) (by norm_num)]
                  _ ≤ 1791761 / 1000000 := by
                    nlinarith [LogTables.log_2_lt, LogTables.log_3_lt]
              · norm_num
            · by_cases h7 : x < 7
              · apply interval_lower 6 7 (1946044 / 1000000)
                  (by norm_num) (by linarith) (by linarith) (by norm_num)
                · have hlogx7 : Real.log x ≤ Real.log 7 :=
                    Real.log_le_log (by linarith) (by linarith)
                  have hrat : (1.946044 : Real) ≤ 1946044 / 1000000 := by norm_num
                  exact (hlogx7.trans_lt (LogTables.log_7_lt.trans_le hrat)).le
                · norm_num
              · by_cases h8 : x < 8
                · apply interval_lower 7 8 (2079444 / 1000000)
                    (by norm_num) (by linarith) (by linarith) (by norm_num)
                  · calc
                      Real.log x ≤ Real.log 8 := Real.log_le_log (by linarith) (by linarith)
                      _ = 3 * Real.log 2 := by
                        rw [show (8 : Real) = 2 ^ 3 by norm_num, Real.log_pow]
                        norm_num
                      _ ≤ 2079444 / 1000000 := by
                        nlinarith [LogTables.log_2_lt]
                  · norm_num
                · by_cases h9 : x < 9
                  · apply interval_lower 8 9 (2197226 / 1000000)
                      (by norm_num) (by linarith) (by linarith) (by norm_num)
                    · calc
                        Real.log x ≤ Real.log 9 := Real.log_le_log (by linarith) (by linarith)
                        _ = 2 * Real.log 3 := by
                          rw [show (9 : Real) = 3 ^ 2 by norm_num, Real.log_pow]
                          norm_num
                        _ ≤ 2197226 / 1000000 := by
                          nlinarith [LogTables.log_3_lt]
                    · norm_num
                  · apply interval_lower 9 10 (2302586 / 1000000)
                      (by norm_num) (by linarith) (by linarith) (by norm_num)
                    · calc
                        Real.log x ≤ Real.log 10 := Real.log_le_log (by linarith) (by linarith)
                        _ = Real.log 2 + Real.log 5 := by
                          rw [show (10 : Real) = 2 * 5 by norm_num,
                            Real.log_mul (by norm_num) (by norm_num)]
                        _ ≤ 2302586 / 1000000 := by
                          nlinarith [LogTables.log_2_lt, LogTables.log_5_lt]
                    · norm_num
  exact hcount.trans hupper

/-! A single list can carry the remaining integer checks.  Each row contains
only a rational-style logarithm envelope and the resulting arithmetic bound;
the adapter below turns the list into the function required by the public
provider. -/
structure DusartPrimeCountingUpperIntegerRow where
  n : Nat
  logUpper : Real
  n_large : 10 ≤ n
  logUpper_pos : 0 < logUpper
  log_bound : Real.log n ≤ logUpper
  numerical : (Nat.primeCounting n : Real) ≤
    (n : Real) / logUpper + (6381 / 5000 : Real) * n / logUpper ^ 2

def DusartPrimeCountingUpperIntegerRowsCover
    (rows : List DusartPrimeCountingUpperIntegerRow) : Prop :=
  ∀ n : Nat, 10 ≤ n → n < 599 →
    ∃ row ∈ rows, row.n = n

theorem dusartPrimeCounting_upper_of_integer_rows
    {rows : List DusartPrimeCountingUpperIntegerRow}
    (cover : DusartPrimeCountingUpperIntegerRowsCover rows) :
    ∀ n : Nat, 10 ≤ n → n < 599 →
      (Nat.primeCounting n : Real) ≤ dusartPiUpper n := by
  intro n hn10 hn599
  obtain ⟨row, hrow, rfl⟩ := cover n hn10 hn599
  have hnpos : (0 : Real) < row.n := by
    exact_mod_cast (show 0 < row.n by omega)
  have hlogpos : 0 < Real.log row.n :=
    Real.log_pos (by exact_mod_cast (show 1 < row.n by omega))
  have hfirst : (row.n : Real) / row.logUpper ≤
      (row.n : Real) / Real.log row.n := by
    apply (div_le_div_iff₀ row.logUpper_pos hlogpos).2
    exact mul_le_mul_of_nonneg_left row.log_bound hnpos.le
  have hlogsq : (Real.log row.n) ^ 2 ≤ row.logUpper ^ 2 := by
    nlinarith [sq_nonneg (row.logUpper - Real.log row.n), row.log_bound]
  have hsecond : (6381 / 5000 : Real) * (row.n : Real) /
      row.logUpper ^ 2 ≤ (6381 / 5000 : Real) * (row.n : Real) /
        (Real.log row.n) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos row.logUpper_pos)
      (sq_pos_of_pos hlogpos)).2
    have hcross : (row.n : Real) * (Real.log row.n) ^ 2 ≤
        (row.n : Real) * row.logUpper ^ 2 :=
      mul_le_mul_of_nonneg_left hlogsq hnpos.le
    convert (mul_le_mul_of_nonneg_left hcross
      (by norm_num : (0 : Real) ≤ 6381 / 5000)) using 1 <;> ring
  have hbound := add_le_add hfirst hsecond
  calc
    (Nat.primeCounting row.n : Real) ≤
        (row.n : Real) / row.logUpper +
          (6381 / 5000 : Real) * row.n / row.logUpper ^ 2 := row.numerical
    _ ≤ (row.n : Real) / Real.log row.n +
        (6381 / 5000 : Real) * row.n / (Real.log row.n) ^ 2 := hbound
    _ = dusartPiUpper row.n := by
      dsimp [dusartPiUpper]
      ring

theorem real_primeCounting_upper_of_integer_rows
    {rows : List DusartPrimeCountingUpperIntegerRow}
    (cover : DusartPrimeCountingUpperIntegerRowsCover rows) :
    ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x :=
  real_primeCounting_upper_of_integer_certificate
    dusartPrimeCounting_upper_below_ten
    (dusartPrimeCounting_upper_of_integer_rows cover)

/-! An interval row records one endpoint count bound and propagates it across
the whole integer interval by monotonicity.  This is the compact form used by
the finite certificate layer; its coverage list need not contain one row for
every integer in `[10, 599)`. -/
set_option autoImplicit true in
structure DusartPrimeCountingUpperIntegerIntervalRow where
  left : Nat
  right : Nat
  left_large : 10 ≤ left
  left_le_right : left ≤ right
  logUpper : Real
  logUpper_pos : 0 < logUpper
  log_bound : Real.log left ≤ logUpper
  numerical : (Nat.primeCounting right : Real) ≤
    (left : Real) / logUpper + (6381 / 5000 : Real) * left / logUpper ^ 2

def dusartPrimeCountingUpperIntegerIntervalRow_of_smooth
    {left right a b c : Nat} (hleft : 10 ≤ left)
    (hle : left ≤ right) (hUpos :
      0 < (a : Real) * (693148 / 1000000 : Real) +
        (b : Real) * (1098613 / 1000000 : Real) +
        (c : Real) * (1609438 / 1000000 : Real))
    (hsmooth : left ≤ 2 ^ a * 3 ^ b * 5 ^ c)
    (hnumerical : (Nat.primeCounting right : Real) ≤
      (left : Real) /
          ((a : Real) * (693148 / 1000000 : Real) +
            (b : Real) * (1098613 / 1000000 : Real) +
            (c : Real) * (1609438 / 1000000 : Real)) +
        (6381 / 5000 : Real) * left /
          ((a : Real) * (693148 / 1000000 : Real) +
            (b : Real) * (1098613 / 1000000 : Real) +
            (c : Real) * (1609438 / 1000000 : Real)) ^ 2) :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  let U : Real :=
    (a : Real) * (693148 / 1000000 : Real) +
      (b : Real) * (1098613 / 1000000 : Real) +
      (c : Real) * (1609438 / 1000000 : Real)
  refine {
    left := left
    right := right
    left_large := hleft
    left_le_right := hle
    logUpper := U
    logUpper_pos := ?_
    log_bound := ?_
    numerical := ?_ }
  · exact hUpos
  · dsimp [U]
    exact log_nat_le_smooth_upper (by omega) hsmooth
  · simpa [U] using hnumerical

def dusartPrimeCountingUpperIntegerIntervalRow_of_smooth_with_seven
    {left right a b c d : Nat} (hleft : 10 ≤ left)
    (hle : left ≤ right) (hUpos :
      0 < (a : Real) * (693148 / 1000000 : Real) +
        (b : Real) * (1098613 / 1000000 : Real) +
        (c : Real) * (1609438 / 1000000 : Real) +
        (d : Real) * (1946044 / 1000000 : Real))
    (hsmooth : left ≤ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d)
    (hnumerical : (Nat.primeCounting right : Real) ≤
      (left : Real) /
          ((a : Real) * (693148 / 1000000 : Real) +
            (b : Real) * (1098613 / 1000000 : Real) +
            (c : Real) * (1609438 / 1000000 : Real) +
            (d : Real) * (1946044 / 1000000 : Real)) +
        (6381 / 5000 : Real) * left /
          ((a : Real) * (693148 / 1000000 : Real) +
            (b : Real) * (1098613 / 1000000 : Real) +
            (c : Real) * (1609438 / 1000000 : Real) +
            (d : Real) * (1946044 / 1000000 : Real)) ^ 2) :
    DusartPrimeCountingUpperIntegerIntervalRow := by
  let U : Real :=
    (a : Real) * (693148 / 1000000 : Real) +
      (b : Real) * (1098613 / 1000000 : Real) +
      (c : Real) * (1609438 / 1000000 : Real) +
      (d : Real) * (1946044 / 1000000 : Real)
  refine {
    left := left
    right := right
    left_large := hleft
    left_le_right := hle
    logUpper := U
    logUpper_pos := ?_
    log_bound := ?_
    numerical := ?_ }
  · exact hUpos
  · dsimp [U]
    exact log_nat_le_smooth_upper_with_seven (by omega) hsmooth
  · simpa [U] using hnumerical

def DusartPrimeCountingUpperIntegerIntervalRowsCover
    (rows : List DusartPrimeCountingUpperIntegerIntervalRow) : Prop :=
  ∀ n : Nat, 10 ≤ n → n < 599 →
    ∃ row ∈ rows, row.left ≤ n ∧ n ≤ row.right

theorem dusartPrimeCounting_upper_of_integer_interval_rows
    {rows : List DusartPrimeCountingUpperIntegerIntervalRow}
    (cover : DusartPrimeCountingUpperIntegerIntervalRowsCover rows) :
    ∀ n : Nat, 10 ≤ n → n < 599 →
      (Nat.primeCounting n : Real) ≤ dusartPiUpper n := by
  intro n hn10 hn599
  obtain ⟨row, hrow, hleft, hright⟩ := cover n hn10 hn599
  have hpi : (Nat.primeCounting n : Real) ≤
      (Nat.primeCounting row.right : Real) := by
    exact_mod_cast Nat.monotone_primeCounting hright
  have hleft_pos : (0 : Real) < row.left := by
    have hleft10 := row.left_large
    exact_mod_cast (show (0 : Nat) < row.left by omega)
  have hlog_pos : 0 < Real.log row.left :=
    Real.log_pos (by
      have hleft10 := row.left_large
      exact_mod_cast (show (1 : Nat) < row.left by omega))
  have hfirst : (row.left : Real) / row.logUpper ≤
      (row.left : Real) / Real.log row.left := by
    apply (div_le_div_iff₀ row.logUpper_pos hlog_pos).2
    exact mul_le_mul_of_nonneg_left row.log_bound hleft_pos.le
  have hlogsq : (Real.log row.left) ^ 2 ≤ row.logUpper ^ 2 := by
    nlinarith [sq_nonneg (row.logUpper - Real.log row.left), row.log_bound]
  have hsecond : (6381 / 5000 : Real) * (row.left : Real) /
      row.logUpper ^ 2 ≤ (6381 / 5000 : Real) * (row.left : Real) /
        (Real.log row.left) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos row.logUpper_pos)
      (sq_pos_of_pos hlog_pos)).2
    have hcross : (row.left : Real) * (Real.log row.left) ^ 2 ≤
        (row.left : Real) * row.logUpper ^ 2 :=
      mul_le_mul_of_nonneg_left hlogsq hleft_pos.le
    convert mul_le_mul_of_nonneg_left hcross
      (by norm_num : (0 : Real) ≤ 6381 / 5000) using 1 <;> ring
  have hbound : (Nat.primeCounting row.right : Real) ≤
      dusartPiUpper row.left := by
    calc
      (Nat.primeCounting row.right : Real) ≤
          (row.left : Real) / row.logUpper +
            (6381 / 5000 : Real) * row.left / row.logUpper ^ 2 :=
        row.numerical
      _ ≤ (row.left : Real) / Real.log row.left +
          (6381 / 5000 : Real) * row.left /
            (Real.log row.left) ^ 2 := add_le_add hfirst hsecond
      _ = dusartPiUpper row.left := by
        dsimp [dusartPiUpper]
        ring
  have hupper : dusartPiUpper row.left ≤ dusartPiUpper n :=
    dusartPiUpper_monotoneOn
      (show (row.left : Real) ∈ Set.Ici 10 by
        change (10 : Real) ≤ row.left
        exact_mod_cast row.left_large)
      (show (n : Real) ∈ Set.Ici 10 by
        change (10 : Real) ≤ n
        exact_mod_cast hn10)
      (show (row.left : Real) ≤ n by exact_mod_cast hleft)
  exact hpi.trans (hbound.trans hupper)

theorem real_primeCounting_upper_of_integer_interval_rows
    {rows : List DusartPrimeCountingUpperIntegerIntervalRow}
    (cover : DusartPrimeCountingUpperIntegerIntervalRowsCover rows) :
    ∀ x : Real, 2 ≤ x → x < 599 →
      (Nat.primeCounting ⌊x⌋₊ : Real) ≤ dusartPiUpper x :=
  real_primeCounting_upper_of_integer_certificate
    dusartPrimeCounting_upper_below_ten
    (dusartPrimeCounting_upper_of_integer_interval_rows cover)

/-! The exact Abel-summation identity underlying the prime-counting
asymptotic.  Keeping the identity in this namespace makes the later
remainder estimates explicit instead of treating `π` as an opaque provider. -/
theorem primeCounting_from_theta_integral {x : Real} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : Real) =
      Chebyshev.theta x / Real.log x +
        ∫ t in (2 : Real)..x,
          Chebyshev.theta t / (t * (Real.log t) ^ 2) := by
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx

/-! A first explicit integration-by-parts identity.  This is the analytic
piece needed to turn the exact Abel identity above into a finite asymptotic
expansion; it is proved here rather than imported from an estimate library. -/
theorem integral_inv_log_sq_eq
    {x : Real} (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / Real.log t ^ 2 =
      x / Real.log x ^ 2 - 2 / Real.log 2 ^ 2 +
        2 * ∫ t in Set.Icc 2 x, 1 / Real.log t ^ 3 := by
  suffices h_ibp : ∀ a b : Real, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (Real.log t) ^ 2) =
        (b / (Real.log b) ^ 2) - (a / (Real.log a) ^ 2) +
          2 * ∫ t in a..b, (1 / (Real.log t) ^ 3) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (Real.log t) ^ 2) t =
        1 / (Real.log t) ^ 2 - 2 * (1 / (Real.log t) ^ 3) := by
    intro t ht
    norm_num [Real.differentiableAt_log,
      ne_of_gt (show 0 < Real.log t from Real.log_pos <| by linarith [ht.1]),
      ne_of_gt (show 0 < t from by linarith [ht.1])]
    ring_nf
    grind
  have h_ftc : ∫ t in a..b, deriv (fun t ↦ t / (Real.log t) ^ 2) t =
      (b / (Real.log b) ^ 2) - (a / (Real.log a) ^ 2) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun y hy ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (Real.differentiableAt_log
          (by cases Set.mem_uIcc.mp hy <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| Real.log_pos <|
          by cases Set.mem_uIcc.mp hy <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := Real.continuousOn_log.mono fun y (hy : y ∈ Set.Icc a b) ↦
        ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ n : Nat, ∀ y ∈ Set.Icc a b,
          Real.log y ^ n ≠ 0 :=
        fun n y hy ↦ pow_ne_zero n <| ne_of_gt <| Real.log_pos <|
          by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div
          (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub]
  · norm_num
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt
      fun y hy ↦ ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (Real.continuousAt_log
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
        (ne_of_gt (pow_pos (Real.log_pos
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))
  · exact ContinuousOn.intervalIntegrable
      (continuousOn_const.mul <| continuousOn_of_forall_continuousAt
        fun y hy ↦ ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (Real.continuousAt_log
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
          (ne_of_gt (pow_pos (Real.log_pos
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))

theorem integral_inv_log_cubed_eq
    {x : Real} (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / Real.log t ^ 3 =
      x / Real.log x ^ 3 - 2 / Real.log 2 ^ 3 +
        3 * ∫ t in Set.Icc 2 x, 1 / Real.log t ^ 4 := by
  suffices h_ibp : ∀ a b : Real, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (Real.log t) ^ 3) =
        (b / (Real.log b) ^ 3) - (a / (Real.log a) ^ 3) +
          3 * ∫ t in a..b, (1 / (Real.log t) ^ 4) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (Real.log t) ^ 3) t =
        1 / (Real.log t) ^ 3 - 3 * (1 / (Real.log t) ^ 4) := by
    intro t ht
    norm_num [Real.differentiableAt_log,
      ne_of_gt (show 0 < Real.log t from Real.log_pos <| by linarith [ht.1]),
      ne_of_gt (show 0 < t from by linarith [ht.1])]
    ring_nf
    grind
  have h_ftc : ∫ t in a..b, deriv (fun t ↦ t / (Real.log t) ^ 3) t =
      (b / (Real.log b) ^ 3) - (a / (Real.log a) ^ 3) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun y hy ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (Real.differentiableAt_log
          (by cases Set.mem_uIcc.mp hy <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| Real.log_pos <|
          by cases Set.mem_uIcc.mp hy <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := Real.continuousOn_log.mono fun y (hy : y ∈ Set.Icc a b) ↦
        ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ n : Nat, ∀ y ∈ Set.Icc a b,
          Real.log y ^ n ≠ 0 :=
        fun n y hy ↦ pow_ne_zero n <| ne_of_gt <| Real.log_pos <|
          by linarith [hy.1]
      exact ContinuousOn.congr (ContinuousOn.sub
        (continuousOn_const.div (hlog_cont.pow _) (hpow_ne _))
        (continuousOn_const.mul <| continuousOn_const.div
          (hlog_cont.pow _) (hpow_ne _))) h_deriv
  rw [← h_ftc, intervalIntegral.integral_congr fun t ht =>
    h_deriv t <| by simpa [hab] using ht]
  rw [intervalIntegral.integral_sub]
  · norm_num
  · exact ContinuousOn.intervalIntegrable (continuousOn_of_forall_continuousAt
      fun y hy ↦ ContinuousAt.div continuousAt_const
        (ContinuousAt.pow (Real.continuousAt_log
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
        (ne_of_gt (pow_pos (Real.log_pos
          (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))
  · exact ContinuousOn.intervalIntegrable
      (continuousOn_const.mul <| continuousOn_of_forall_continuousAt
        fun y hy ↦ ContinuousAt.div continuousAt_const
          (ContinuousAt.pow (Real.continuousAt_log
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)
          (ne_of_gt (pow_pos (Real.log_pos
            (by linarith [Set.mem_Icc.mp (by simpa [hab] using hy)])) _)))

theorem deriv_log_power_kernel
    {n : Nat} {t : Real} (ht : 1 < t) :
    deriv (fun y : Real => y / (Real.log y) ^ (n + 1)) t =
      1 / (Real.log t) ^ (n + 1) -
        (n + 1 : Real) * (1 / (Real.log t) ^ (n + 2)) := by
  have htpos : 0 < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hlogne : Real.log t ≠ 0 := ne_of_gt hlogpos
  have hderiv := (hasDerivAt_id t).div
    ((Real.hasDerivAt_log (ne_of_gt htpos)).pow (n + 1))
    (pow_ne_zero _ hlogne)
  convert hderiv.deriv using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply]
    rw [show n + 1 - 1 = n by omega]
    field_simp [hlogne]
    rw [pow_succ]
    ring_nf
    norm_num [Nat.cast_add, Nat.cast_one]
    ring

end

end PrimeFactorUnimodality
