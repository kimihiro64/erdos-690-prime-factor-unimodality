import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Core
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.EndpointBounds
import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Mathlib.NumberTheory.Pocklington
import PrimeFactorUnimodality.Mathlib.NumberTheory.PocklingtonRows

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prime-row prefix -/

namespace PrimeFactorUnimodality

noncomputable section
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

def dusartPrimeRow_of_explicit
    {p q : Nat} {L : Real}
    (hq : q.Prime)
    (hpq : p < q)
    (hleft_large : 3275 ≤ p)
    (hlog : Real.log p ≤ L)
    (hL : 0 < L)
    (hproduct : (q - p : Real) * (2 * L ^ 2) ≤ p) :
    DusartPrimeRow := by
  have hp_pos : (0 : Real) < p := by
    exact_mod_cast (show 0 < p by omega)
  have hlog_pos : 0 < Real.log p :=
    Real.log_pos (by norm_num at hleft_large ⊢; linarith)
  have hlog_sq : 2 * (Real.log p) ^ 2 ≤ 2 * L ^ 2 := by
    nlinarith [sq_nonneg (Real.log p), sq_nonneg L]
  have hdenL : 0 < 2 * L ^ 2 := by positivity
  have hdenLog : 0 < 2 * (Real.log p) ^ 2 := by positivity
  have hgapL : (q - p : Real) ≤ p / (2 * L ^ 2) := by
    apply (le_div_iff₀ hdenL).2
    exact hproduct
  have hgap : (q - p : Real) ≤ p / (2 * (Real.log p) ^ 2) :=
    hgapL.trans (div_le_div_of_nonneg_left hp_pos.le hdenLog hlog_sq)
  refine {
    left := p
    right := q - 1
    prime := q
    left_large := hleft_large
    right_lt_prime := by omega
    prime_prime := hq
    prime_upper := ?_ }
  have hqreal : (q : Real) - p ≤
      p / (2 * (Real.log p) ^ 2) := by
    exact hgap
  dsimp [dusartUpper]
  calc
    (q : Real) = p + ((q : Real) - p) := by ring
    _ ≤ p + p / (2 * (Real.log p) ^ 2) := by linarith
    _ = p * (1 + (1 / 2 : Real) / (Real.log p) ^ 2) := by ring

def dusartPrimeRow_of_explicit_3802
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((33 : Real) / 4) ^ 2) ≤ p)
    (hleft_large : 3275 ≤ p)
    (hleft_3802 : p ≤ 3802) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq hleft_large
    (log_le_33_over_4_of_3275_le hleft_large hleft_3802)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_4670
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((169 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 3803 ≤ p)
    (hleft_4670 : p ≤ 4670) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_169_over_20_of_3803_le hleft_large hleft_4670)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_4914
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((17 : Real) / 2) ^ 2) ≤ p)
    (hleft_large : 4673 ≤ p)
    (hleft_4914 : p ≤ 4914) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_17_over_2_of_4673_le hleft_large hleft_4914)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_5166
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((171 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 4919 ≤ p)
    (hleft_5166 : p ≤ 5166) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_171_over_20_of_4919_le hleft_large hleft_5166)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_5431
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((43 : Real) / 5) ^ 2) ≤ p)
    (hleft_large : 5167 ≤ p)
    (hleft_5431 : p ≤ 5431) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_43_over_5_of_5167_le hleft_large hleft_5431)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_5710
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((173 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 5437 ≤ p)
    (hleft_5710 : p ≤ 5710) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_173_over_20_of_5437_le hleft_large hleft_5710)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_6002
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((87 : Real) / 10) ^ 2) ≤ p)
    (hleft_large : 5711 ≤ p)
    (hleft_6002 : p ≤ 6002) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_87_over_10_of_5711_le hleft_large hleft_6002)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_6310
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((35 : Real) / 4) ^ 2) ≤ p)
    (hleft_large : 6007 ≤ p)
    (hleft_6310 : p ≤ 6310) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_35_over_4_of_6007_le hleft_large hleft_6310)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_6634
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((44 : Real) / 5) ^ 2) ≤ p)
    (hleft_large : 6311 ≤ p)
    (hleft_6634 : p ≤ 6634) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_44_over_5_of_6311_le hleft_large hleft_6634)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_6974
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((177 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 6637 ≤ p)
    (hleft_6974 : p ≤ 6974) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_177_over_20_of_6637_le hleft_large hleft_6974)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_7331
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((89 : Real) / 10) ^ 2) ≤ p)
    (hleft_large : 6977 ≤ p)
    (hleft_7331 : p ≤ 7331) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_89_over_10_of_6977_le hleft_large hleft_7331)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_7707
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((179 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 7333 ≤ p)
    (hleft_7707 : p ≤ 7707) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_179_over_20_of_7333_le hleft_large hleft_7707)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_8103
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * (9 : Real) ^ 2) ≤ p)
    (hleft_large : 7717 ≤ p)
    (hleft_8103 : p ≤ 8103) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_9_of_7717_le hleft_large hleft_8103)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_8518
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((181 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 8111 ≤ p)
    (hleft_8518 : p ≤ 8518) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_181_over_20_of_8111_le hleft_large hleft_8518)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_8955
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((91 : Real) / 10) ^ 2) ≤ p)
    (hleft_large : 8521 ≤ p)
    (hleft_8955 : p ≤ 8955) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_91_over_10_of_8521_le hleft_large hleft_8955)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_9414
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((183 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 8963 ≤ p)
    (hleft_9414 : p ≤ 9414) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_183_over_20_of_8963_le hleft_large hleft_9414)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_9897
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((46 : Real) / 5) ^ 2) ≤ p)
    (hleft_large : 9419 ≤ p)
    (hleft_9897 : p ≤ 9897) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_46_over_5_of_9419_le hleft_large hleft_9897)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_10404
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((37 : Real) / 4) ^ 2) ≤ p)
    (hleft_large : 9901 ≤ p)
    (hleft_10404 : p ≤ 10404) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_37_over_4_of_9901_le hleft_large hleft_10404)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_10938
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((93 : Real) / 10) ^ 2) ≤ p)
    (hleft_large : 10427 ≤ p)
    (hleft_10938 : p ≤ 10938) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_93_over_10_of_10427_le hleft_large hleft_10938)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_11498
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((187 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 10939 ≤ p)
    (hleft_11498 : p ≤ 11498) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_187_over_20_of_10939_le hleft_large hleft_11498)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_12088
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((47 : Real) / 5) ^ 2) ≤ p)
    (hleft_large : 11503 ≤ p)
    (hleft_12088 : p ≤ 12088) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_47_over_5_of_11503_le hleft_large hleft_12088)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_12708
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((189 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 12097 ≤ p)
    (hleft_12708 : p ≤ 12708) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_189_over_20_of_12097_le hleft_large hleft_12708)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_13359
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((19 : Real) / 2) ^ 2) ≤ p)
    (hleft_large : 12713 ≤ p)
    (hleft_13359 : p ≤ 13359) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_19_over_2_of_12713_le hleft_large hleft_13359)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_14044
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((191 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 13367 ≤ p)
    (hleft_14044 : p ≤ 14044) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_191_over_20_of_13367_le hleft_large hleft_14044)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_14764
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((48 : Real) / 5) ^ 2) ≤ p)
    (hleft_large : 14051 ≤ p)
    (hleft_14764 : p ≤ 14764) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_48_over_5_of_14051_le hleft_large hleft_14764)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_15521
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((193 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 14767 ≤ p)
    (hleft_15521 : p ≤ 15521) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_193_over_20_of_14767_le hleft_large hleft_15521)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_16317
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((97 : Real) / 10) ^ 2) ≤ p)
    (hleft_large : 15527 ≤ p)
    (hleft_16317 : p ≤ 16317) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_97_over_10_of_15527_le hleft_large hleft_16317)
    (by norm_num) hproduct

def dusartPrimeRow_of_explicit_23155
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((201 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 22027 ≤ p)
    (hleft_23155 : p ≤ 23155) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_201_over_20_of_22027_le hleft_large hleft_23155)
    (by norm_num) hproduct


def dusartPrimeRow_of_explicit_22026
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((10 : Real) / 1) ^ 2) ≤ p)
    (hleft_large : 20959 ≤ p)
    (hleft_22026 : p ≤ 22026) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_10_over_1_of_20959_le hleft_large hleft_22026)
    (by norm_num) hproduct


def dusartPrimeRow_of_explicit_20952
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((199 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 19937 ≤ p)
    (hleft_20952 : p ≤ 20952) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_199_over_20_of_19937_le hleft_large hleft_20952)
    (by norm_num) hproduct


def dusartPrimeRow_of_explicit_19930
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((99 : Real) / 10) ^ 2) ≤ p)
    (hleft_large : 18959 ≤ p)
    (hleft_19930 : p ≤ 19930) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_99_over_10_of_18959_le hleft_large hleft_19930)
    (by norm_num) hproduct


def dusartPrimeRow_of_explicit_18958
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((197 : Real) / 20) ^ 2) ≤ p)
    (hleft_large : 18041 ≤ p)
    (hleft_18958 : p ≤ 18958) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_197_over_20_of_18041_le hleft_large hleft_18958)
    (by norm_num) hproduct


def dusartPrimeRow_of_explicit_18033
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((49 : Real) / 5) ^ 2) ≤ p)
    (hleft_large : 17159 ≤ p)
    (hleft_18033 : p ≤ 18033) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_49_over_5_of_17159_le hleft_large hleft_18033)
    (by norm_num) hproduct


def dusartPrimeRow_of_explicit_17154
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((39 : Real) / 4) ^ 2) ≤ p)
    (hleft_large : 16319 ≤ p)
    (hleft_17154 : p ≤ 17154) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq (by omega)
    (log_le_39_over_4_of_16319_le hleft_large hleft_17154)
    (by norm_num) hproduct


def dusartPrimeRow_of_explicit_89693
    {p q : Nat}
    (hq : q.Prime)
    (hpq : p < q)
    (hproduct : (q - p : Real) *
        (2 * ((1141 : Real) / 100) ^ 2) ≤ p)
    (hleft_large : 3275 ≤ p)
    (hleft_89693 : p ≤ 89693) :
    DusartPrimeRow :=
  dusartPrimeRow_of_explicit hq hpq hleft_large
    (log_le_1141_over_100_of_3275_le hleft_large hleft_89693)
    (by norm_num) hproduct

inductive DusartPrimeRowsChain : Nat → Nat → List DusartPrimeRow → Prop
  | empty {a b : Nat} (h : b < a) :
      DusartPrimeRowsChain a b []
  | cons {a b : Nat} (row : DusartPrimeRow)
      (hleft : row.left ≤ a)
      (hordered : row.left ≤ row.right)
      {tail : List DusartPrimeRow}
      (htail : DusartPrimeRowsChain (row.right + 1) b tail) :
      DusartPrimeRowsChain a b (row :: tail)

theorem dusartPrimeRowsCover_of_chain
    {a b : Nat} {rows : List DusartPrimeRow}
    (chain : DusartPrimeRowsChain a b rows) :
    ∀ x : Real, (a : Real) ≤ x → x < (b : Real) + 1 →
      ∃ row ∈ rows, (row.left : Real) ≤ x ∧ x < (row.right : Real) + 1 := by
  induction chain with
  | @empty a b h =>
      intro x hleft hright
      exfalso
      have hab : (b : Real) + 1 ≤ a := by
        exact_mod_cast Nat.succ_le_of_lt h
      linarith
  | @cons a b row hleft hordered tail htail ih =>
      intro x hxa hxb
      by_cases hrow : x < (row.right : Real) + 1
      · refine ⟨row, by simp, ?_, hrow⟩
        have hleft_real : (row.left : Real) ≤ a := by
          exact_mod_cast hleft
        exact hleft_real.trans hxa
      · have hnext : ((row.right + 1 : Nat) : Real) ≤ x := by
          have : (row.right : Real) + 1 ≤ x := le_of_not_gt hrow
          norm_num at this ⊢
          exact this
        obtain ⟨next, hmem, hnext_left, hnext_right⟩ :=
          ih x hnext hxb
        exact ⟨next, by simp [hmem], hnext_left, hnext_right⟩

theorem dusartPrimeRowsChain_raise_start
    {a a' b : Nat} {rows : List DusartPrimeRow}
    (haa' : a ≤ a')
    (chain : DusartPrimeRowsChain a b rows) :
    DusartPrimeRowsChain a' b rows := by
  induction chain with
  | empty h =>
      exact DusartPrimeRowsChain.empty (by omega)
  | @cons a b row hleft hordered tail htail ih =>
      exact DusartPrimeRowsChain.cons row (by omega) hordered htail

theorem dusartPrimeRowsChain_append
    {a m b : Nat} {left right : List DusartPrimeRow}
    (hleft : DusartPrimeRowsChain a m left)
    (hright : DusartPrimeRowsChain (m + 1) b right) :
    DusartPrimeRowsChain a b (left ++ right) := by
  induction hleft with
  | empty h =>
      simpa using dusartPrimeRowsChain_raise_start (by omega) hright
  | @cons a m row hrow hordered tail htail ih =>
      simpa using DusartPrimeRowsChain.cons row hrow hordered
        (ih hright)


@[simp] theorem dusartPrimeRow_of_explicit_left
    {p q : Nat} {L : Real} (hq : q.Prime) (hpq : p < q)
    (hleft_large : 3275 ≤ p) (hlog : Real.log p ≤ L)
    (hL : 0 < L) (hproduct : (q - p : Real) * (2 * L ^ 2) ≤ p) :
    (dusartPrimeRow_of_explicit hq hpq hleft_large hlog hL hproduct).left = p := by
  rfl

@[simp] theorem dusartPrimeRow_of_explicit_right
    {p q : Nat} {L : Real} (hq : q.Prime) (hpq : p < q)
    (hleft_large : 3275 ≤ p) (hlog : Real.log p ≤ L)
    (hL : 0 < L) (hproduct : (q - p : Real) * (2 * L ^ 2) ≤ p) :
    (dusartPrimeRow_of_explicit hq hpq hleft_large hlog hL hproduct).right = q - 1 := by
  rfl

/-! Reusable assembler for generated row parts. -/
def DusartPrimeRowsChainData (a b : Nat) : List DusartPrimeRow → Prop
  | [] => b < a
  | row :: tail =>
      row.left ≤ a ∧ row.left ≤ row.right ∧
        DusartPrimeRowsChainData (row.right + 1) b tail

theorem dusartPrimeRowsChain_of_data
    {a b : Nat} {rows : List DusartPrimeRow}
    (h : DusartPrimeRowsChainData a b rows) :
    DusartPrimeRowsChain a b rows := by
  induction rows generalizing a b with
  | nil => exact DusartPrimeRowsChain.empty h
  | cons row tail ih =>
      exact DusartPrimeRowsChain.cons row h.1 h.2.1 (ih h.2.2)
