import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.Core

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Endpoint logarithm bounds for finite prime intervals -/

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
    have hfactor : 0 ≤ (Real.log x) ^ 2 * (Real.log x - 3) :=
      mul_nonneg log_sq_pos.le (by linarith)
    nlinarith [hfactor]

theorem logCubedWidth_monotoneOn :
    MonotoneOn logCubedWidth (Set.Ici (3275 : Real)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici (3275 : Real))
  · have hlog : ContinuousOn (fun y : Real => Real.log y)
        (Set.Ici (3275 : Real)) := by
      exact continuousOn_id.log (by
        intro x hx
        have hx_pos : (0 : Real) < x := by
          norm_num at hx ⊢
          linarith
        simpa only [id_eq] using hx_pos.ne')
    exact continuousOn_id.div (hlog.pow 3) (by
      intro x hx
      exact pow_ne_zero 3
        (Real.log_pos (by norm_num at hx ⊢; linarith)).ne')
  · have hlog : DifferentiableOn ℝ (fun y : Real => Real.log y)
        (interior (Set.Ici (3275 : Real))) := by
      exact differentiableOn_id.log (by
        intro x hx
        have hx' : (3275 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        simpa only [id_eq] using (show x ≠ 0 by linarith))
    exact differentiableOn_id.div (hlog.pow 3) (by
      intro x hx
      exact pow_ne_zero 3
        (Real.log_pos (by norm_num at hx ⊢; linarith)).ne')
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
      have hx' : (3 : Real) ^ 3 < x := by
        have h3275 : (3275 : Real) < x := by
          simpa only [interior_Ici, Set.mem_Ioi] using hx
        norm_num at ⊢
        linarith
      exact exp_three.trans hx'
    have log_cube_pos : 0 < (Real.log x) ^ 3 := by positivity
    have hden_ne : (Real.log x) ^ 3 ≠ 0 := ne_of_gt log_cube_pos
    have hlog := Real.hasDerivAt_log x_ne
    have hderiv := (hasDerivAt_id x).div (hlog.pow 3) hden_ne
    simp only [id_eq] at hderiv
    change 0 ≤ deriv (id / Real.log ^ 3) x
    rw [hderiv.deriv]
    field_simp [x_ne, log_pos.ne']
    have log_sq_pos : 0 < (Real.log x) ^ 2 := by positivity
    have hfactor : 0 ≤ (Real.log x) ^ 2 * (Real.log x - 3) :=
      mul_nonneg log_sq_pos.le (by linarith)
    simp only [Pi.pow_apply] at *
    norm_num at *
    nlinarith [hfactor]

theorem logCubedWidth_lower_of_endpoint
    {g x : Nat}
    (hendpoint : (g : Real) ≤ logCubedWidth 89693)
    (hx : (89693 : Real) ≤ x) :
    (g : Real) ≤ logCubedWidth x := by
  exact hendpoint.trans
    (logCubedWidth_monotoneOn (a := (89693 : Real)) (b := (x : Real))
      (by norm_num) (Set.mem_Ici.mpr (by linarith [hx])) hx)

theorem logCubedWidth_lower_of_log_upper
    {a g : Nat} {L : Real}
    (ha : (89693 : Real) ≤ a)
    (hL : 0 ≤ L)
    (hlog : Real.log a ≤ L)
    (hproduct : (g : Real) * L ^ 3 ≤ a) :
    (g : Real) ≤ logCubedWidth a := by
  have ha_pos : 0 < (a : Real) := by linarith
  have hlog_pos : 0 < Real.log a := by
    exact Real.log_pos (by linarith)
  have hlog_nonneg : 0 ≤ Real.log a := hlog_pos.le
  have hpow : (Real.log a) ^ 3 ≤ L ^ 3 :=
    pow_le_pow_left₀ hlog_nonneg hlog 3
  have hmul : (g : Real) * (Real.log a) ^ 3 ≤
      (g : Real) * L ^ 3 :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hbound : (g : Real) * (Real.log a) ^ 3 ≤ a :=
    hmul.trans hproduct
  exact (le_div_iff₀ (pow_pos hlog_pos 3)).2 (by
    simpa [logCubedWidth] using hbound)

/-! A small certified exponential lower bound used for the finite endpoint
checks below.  It reduces each check to the library's decimal lower bound for
`exp 1` and the elementary inequality `1 + r ≤ exp r`. -/
lemma exp_lower_nat_add (n : Nat) {r : Real} (hr : 0 ≤ r) :
    ((27182818283 : Real) / 10000000000) ^ n *
        (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120 +
          r ^ 6 / 720 + r ^ 7 / 5040 + r ^ 8 / 40320 + r ^ 9 / 362880) ≤
      Real.exp (n + r) := by
  have hbase : (27182818283 : Real) / 10000000000 ≤ Real.exp 1 := by
    exact (by norm_num :
      (27182818283 : Real) / 10000000000 ≤ 2.7182818283).trans
      Real.exp_one_gt_d9.le
  have hpow : ((27182818283 : Real) / 10000000000) ^ n ≤
      (Real.exp 1) ^ n := by
    exact pow_le_pow_left₀ (by positivity) hbase n
  have hsum : 1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120 +
      r ^ 6 / 720 + r ^ 7 / 5040 + r ^ 8 / 40320 + r ^ 9 / 362880 ≤
      Real.exp r := by
    have h := Real.sum_le_exp_of_nonneg hr 10
    norm_num [Finset.sum_range_succ, pow_succ] at h ⊢
    linarith [h]
  calc
    ((27182818283 : Real) / 10000000000) ^ n *
        (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120 +
          r ^ 6 / 720 + r ^ 7 / 5040 + r ^ 8 / 40320 + r ^ 9 / 362880) ≤
        (Real.exp 1) ^ n * (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 +
          r ^ 5 / 120 + r ^ 6 / 720 + r ^ 7 / 5040 + r ^ 8 / 40320 +
          r ^ 9 / 362880) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ (Real.exp 1) ^ n * Real.exp r :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = Real.exp (n + r) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem log_89693_le_1141_over_100 :
    Real.log (89693 : Real) ≤ (1141 : Real) / 100 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 11 (r := (41 : Real) / 100) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem logCubedWidth_89693_ge_60 :
    (60 : Real) ≤ logCubedWidth 89693 := by
  apply logCubedWidth_lower_of_log_upper (a := 89693) (g := 60)
    (by norm_num) (by norm_num) log_89693_le_1141_over_100
  norm_num

theorem log_100000_le_116_over_10 :
    Real.log (100000 : Real) ≤ (116 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 11 (r := (6 : Real) / 10) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_1141_over_100_of_3275_le
    {a : Nat} (ha : 3275 ≤ a) (ha89693 : a ≤ 89693) :
    Real.log a ≤ (1141 : Real) / 100 := by
  have hmono : Real.log (a : Real) ≤ Real.log (89693 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha89693
  exact hmono.trans log_89693_le_1141_over_100

theorem log_3802_le_33_over_4 :
    Real.log (3802 : Real) ≤ (33 : Real) / 4 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (1 : Real) / 4) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_33_over_4_of_3275_le
    {a : Nat} (ha : 3275 ≤ a) (ha3802 : a ≤ 3802) :
    Real.log a ≤ (33 : Real) / 4 := by
  have hmono : Real.log (a : Real) ≤ Real.log (3802 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha3802
  exact hmono.trans log_3802_le_33_over_4

theorem log_4670_le_169_over_20 :
    Real.log (4670 : Real) ≤ (169 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (9 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_169_over_20_of_3803_le
    {a : Nat} (ha : 3803 ≤ a) (ha4670 : a ≤ 4670) :
    Real.log a ≤ (169 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (4670 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha4670
  exact hmono.trans log_4670_le_169_over_20

theorem log_4914_le_17_over_2 :
    Real.log (4914 : Real) ≤ (17 : Real) / 2 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (1 : Real) / 2) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_17_over_2_of_4673_le
    {a : Nat} (ha : 4673 ≤ a) (ha4914 : a ≤ 4914) :
    Real.log a ≤ (17 : Real) / 2 := by
  have hmono : Real.log (a : Real) ≤ Real.log (4914 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha4914
  exact hmono.trans log_4914_le_17_over_2

theorem log_5166_le_171_over_20 :
    Real.log (5166 : Real) ≤ (171 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (11 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_171_over_20_of_4919_le
    {a : Nat} (ha : 4919 ≤ a) (ha5166 : a ≤ 5166) :
    Real.log a ≤ (171 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (5166 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha5166
  exact hmono.trans log_5166_le_171_over_20

theorem log_5431_le_43_over_5 :
    Real.log (5431 : Real) ≤ (43 : Real) / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (3 : Real) / 5) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_43_over_5_of_5167_le
    {a : Nat} (ha : 5167 ≤ a) (ha5431 : a ≤ 5431) :
    Real.log a ≤ (43 : Real) / 5 := by
  have hmono : Real.log (a : Real) ≤ Real.log (5431 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha5431
  exact hmono.trans log_5431_le_43_over_5

theorem log_5710_le_173_over_20 :
    Real.log (5710 : Real) ≤ (173 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (13 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_173_over_20_of_5437_le
    {a : Nat} (ha : 5437 ≤ a) (ha5710 : a ≤ 5710) :
    Real.log a ≤ (173 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (5710 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha5710
  exact hmono.trans log_5710_le_173_over_20

theorem log_6002_le_87_over_10 :
    Real.log (6002 : Real) ≤ (87 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (7 : Real) / 10) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_87_over_10_of_5711_le
    {a : Nat} (ha : 5711 ≤ a) (ha6002 : a ≤ 6002) :
    Real.log a ≤ (87 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (6002 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha6002
  exact hmono.trans log_6002_le_87_over_10

theorem log_6310_le_35_over_4 :
    Real.log (6310 : Real) ≤ (35 : Real) / 4 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (3 : Real) / 4) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_35_over_4_of_6007_le
    {a : Nat} (ha : 6007 ≤ a) (ha6310 : a ≤ 6310) :
    Real.log a ≤ (35 : Real) / 4 := by
  have hmono : Real.log (a : Real) ≤ Real.log (6310 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha6310
  exact hmono.trans log_6310_le_35_over_4

theorem log_6634_le_44_over_5 :
    Real.log (6634 : Real) ≤ (44 : Real) / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (4 : Real) / 5) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_44_over_5_of_6311_le
    {a : Nat} (ha : 6311 ≤ a) (ha6634 : a ≤ 6634) :
    Real.log a ≤ (44 : Real) / 5 := by
  have hmono : Real.log (a : Real) ≤ Real.log (6634 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha6634
  exact hmono.trans log_6634_le_44_over_5

theorem log_6974_le_177_over_20 :
    Real.log (6974 : Real) ≤ (177 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (17 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_177_over_20_of_6637_le
    {a : Nat} (ha : 6637 ≤ a) (ha6974 : a ≤ 6974) :
    Real.log a ≤ (177 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (6974 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha6974
  exact hmono.trans log_6974_le_177_over_20

theorem log_7331_le_89_over_10 :
    Real.log (7331 : Real) ≤ (89 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (9 : Real) / 10) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_89_over_10_of_6977_le
    {a : Nat} (ha : 6977 ≤ a) (ha7331 : a ≤ 7331) :
    Real.log a ≤ (89 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (7331 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha7331
  exact hmono.trans log_7331_le_89_over_10

theorem log_7707_le_179_over_20 :
    Real.log (7707 : Real) ≤ (179 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 8 (r := (19 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_179_over_20_of_7333_le
    {a : Nat} (ha : 7333 ≤ a) (ha7707 : a ≤ 7707) :
    Real.log a ≤ (179 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (7707 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha7707
  exact hmono.trans log_7707_le_179_over_20

theorem log_8103_le_9 :
    Real.log (8103 : Real) ≤ (9 : Real) := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := 0) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_9_of_7717_le
    {a : Nat} (ha : 7717 ≤ a) (ha8103 : a ≤ 8103) :
    Real.log a ≤ (9 : Real) := by
  have hmono : Real.log (a : Real) ≤ Real.log (8103 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha8103
  exact hmono.trans log_8103_le_9

theorem log_8518_le_181_over_20 :
    Real.log (8518 : Real) ≤ (181 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (1 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_181_over_20_of_8111_le
    {a : Nat} (ha : 8111 ≤ a) (ha8518 : a ≤ 8518) :
    Real.log a ≤ (181 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (8518 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha8518
  exact hmono.trans log_8518_le_181_over_20

theorem log_8955_le_91_over_10 :
    Real.log (8955 : Real) ≤ (91 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (1 : Real) / 10) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_91_over_10_of_8521_le
    {a : Nat} (ha : 8521 ≤ a) (ha8955 : a ≤ 8955) :
    Real.log a ≤ (91 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (8955 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha8955
  exact hmono.trans log_8955_le_91_over_10

theorem log_9414_le_183_over_20 :
    Real.log (9414 : Real) ≤ (183 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (3 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_183_over_20_of_8963_le
    {a : Nat} (ha : 8963 ≤ a) (ha9414 : a ≤ 9414) :
    Real.log a ≤ (183 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (9414 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha9414
  exact hmono.trans log_9414_le_183_over_20

theorem log_9897_le_46_over_5 :
    Real.log (9897 : Real) ≤ (46 : Real) / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (1 : Real) / 5) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_46_over_5_of_9419_le
    {a : Nat} (ha : 9419 ≤ a) (ha9897 : a ≤ 9897) :
    Real.log a ≤ (46 : Real) / 5 := by
  have hmono : Real.log (a : Real) ≤ Real.log (9897 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha9897
  exact hmono.trans log_9897_le_46_over_5

theorem log_10404_le_37_over_4 :
    Real.log (10404 : Real) ≤ (37 : Real) / 4 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (1 : Real) / 4) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_37_over_4_of_9901_le
    {a : Nat} (ha : 9901 ≤ a) (ha10404 : a ≤ 10404) :
    Real.log a ≤ (37 : Real) / 4 := by
  have hmono : Real.log (a : Real) ≤ Real.log (10404 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha10404
  exact hmono.trans log_10404_le_37_over_4

theorem log_10938_le_93_over_10 :
    Real.log (10938 : Real) ≤ (93 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (3 : Real) / 10) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_93_over_10_of_10427_le
    {a : Nat} (ha : 10427 ≤ a) (ha10938 : a ≤ 10938) :
    Real.log a ≤ (93 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (10938 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha10938
  exact hmono.trans log_10938_le_93_over_10

theorem log_11498_le_187_over_20 :
    Real.log (11498 : Real) ≤ (187 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (7 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_187_over_20_of_10939_le
    {a : Nat} (ha : 10939 ≤ a) (ha11498 : a ≤ 11498) :
    Real.log a ≤ (187 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (11498 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha11498
  exact hmono.trans log_11498_le_187_over_20

theorem log_12088_le_47_over_5 :
    Real.log (12088 : Real) ≤ (47 : Real) / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (2 : Real) / 5) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_47_over_5_of_11503_le
    {a : Nat} (ha : 11503 ≤ a) (ha12088 : a ≤ 12088) :
    Real.log a ≤ (47 : Real) / 5 := by
  have hmono : Real.log (a : Real) ≤ Real.log (12088 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha12088
  exact hmono.trans log_12088_le_47_over_5

theorem log_12708_le_189_over_20 :
    Real.log (12708 : Real) ≤ (189 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (9 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_189_over_20_of_12097_le
    {a : Nat} (ha : 12097 ≤ a) (ha12708 : a ≤ 12708) :
    Real.log a ≤ (189 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (12708 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha12708
  exact hmono.trans log_12708_le_189_over_20

theorem log_13359_le_19_over_2 :
    Real.log (13359 : Real) ≤ (19 : Real) / 2 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (1 : Real) / 2) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_19_over_2_of_12713_le
    {a : Nat} (ha : 12713 ≤ a) (ha13359 : a ≤ 13359) :
    Real.log a ≤ (19 : Real) / 2 := by
  have hmono : Real.log (a : Real) ≤ Real.log (13359 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha13359
  exact hmono.trans log_13359_le_19_over_2

theorem log_14044_le_191_over_20 :
    Real.log (14044 : Real) ≤ (191 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (11 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_191_over_20_of_13367_le
    {a : Nat} (ha : 13367 ≤ a) (ha14044 : a ≤ 14044) :
    Real.log a ≤ (191 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (14044 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha14044
  exact hmono.trans log_14044_le_191_over_20

theorem log_14764_le_48_over_5 :
    Real.log (14764 : Real) ≤ (48 : Real) / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (3 : Real) / 5) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_48_over_5_of_14051_le
    {a : Nat} (ha : 14051 ≤ a) (ha14764 : a ≤ 14764) :
    Real.log a ≤ (48 : Real) / 5 := by
  have hmono : Real.log (a : Real) ≤ Real.log (14764 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha14764
  exact hmono.trans log_14764_le_48_over_5

theorem log_15521_le_193_over_20 :
    Real.log (15521 : Real) ≤ (193 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (13 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_193_over_20_of_14767_le
    {a : Nat} (ha : 14767 ≤ a) (ha15521 : a ≤ 15521) :
    Real.log a ≤ (193 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (15521 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha15521
  exact hmono.trans log_15521_le_193_over_20

theorem log_16317_le_97_over_10 :
    Real.log (16317 : Real) ≤ (97 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (7 : Real) / 10) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_97_over_10_of_15527_le
    {a : Nat} (ha : 15527 ≤ a) (ha16317 : a ≤ 16317) :
    Real.log a ≤ (97 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (16317 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha16317
  exact hmono.trans log_16317_le_97_over_10

theorem log_23155_le_201_over_20 :
    Real.log (23155 : Real) ≤ (201 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 10 (r := (1 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_201_over_20_of_22027_le
    {a : Nat} (ha : 22027 ≤ a) (ha23155 : a ≤ 23155) :
    Real.log a ≤ (201 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (23155 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha23155
  exact hmono.trans log_23155_le_201_over_20


theorem log_22026_le_10_over_1 :
    Real.log (22026 : Real) ≤ (10 : Real) / 1 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 10 (r := 0) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_10_over_1_of_20959_le
    {a : Nat} (ha : 20959 ≤ a) (ha22026 : a ≤ 22026) :
    Real.log a ≤ (10 : Real) / 1 := by
  have hmono : Real.log (a : Real) ≤ Real.log (22026 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha22026
  exact hmono.trans log_22026_le_10_over_1


theorem log_20952_le_199_over_20 :
    Real.log (20952 : Real) ≤ (199 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (19 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_199_over_20_of_19937_le
    {a : Nat} (ha : 19937 ≤ a) (ha20952 : a ≤ 20952) :
    Real.log a ≤ (199 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (20952 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha20952
  exact hmono.trans log_20952_le_199_over_20


theorem log_19930_le_99_over_10 :
    Real.log (19930 : Real) ≤ (99 : Real) / 10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (9 : Real) / 10) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_99_over_10_of_18959_le
    {a : Nat} (ha : 18959 ≤ a) (ha19930 : a ≤ 19930) :
    Real.log a ≤ (99 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (19930 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha19930
  exact hmono.trans log_19930_le_99_over_10


theorem log_18958_le_197_over_20 :
    Real.log (18958 : Real) ≤ (197 : Real) / 20 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (17 : Real) / 20) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_197_over_20_of_18041_le
    {a : Nat} (ha : 18041 ≤ a) (ha18958 : a ≤ 18958) :
    Real.log a ≤ (197 : Real) / 20 := by
  have hmono : Real.log (a : Real) ≤ Real.log (18958 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha18958
  exact hmono.trans log_18958_le_197_over_20


theorem log_18033_le_49_over_5 :
    Real.log (18033 : Real) ≤ (49 : Real) / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (8 : Real) / 10) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_49_over_5_of_17159_le
    {a : Nat} (ha : 17159 ≤ a) (ha18033 : a ≤ 18033) :
    Real.log a ≤ (49 : Real) / 5 := by
  have hmono : Real.log (a : Real) ≤ Real.log (18033 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha18033
  exact hmono.trans log_18033_le_49_over_5


theorem log_17154_le_39_over_4 :
    Real.log (17154 : Real) ≤ (39 : Real) / 4 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have h := exp_lower_nat_add 9 (r := (3 : Real) / 4) (by norm_num)
  norm_num at h ⊢
  linarith [h]

theorem log_le_39_over_4_of_16319_le
    {a : Nat} (ha : 16319 ≤ a) (ha17154 : a ≤ 17154) :
    Real.log a ≤ (39 : Real) / 4 := by
  have hmono : Real.log (a : Real) ≤ Real.log (17154 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha17154
  exact hmono.trans log_17154_le_39_over_4


theorem log_le_116_over_10_of_89693_le
    {a : Nat} (ha : (89693 : Nat) ≤ a) (ha100000 : a ≤ 100000) :
    Real.log a ≤ (116 : Real) / 10 := by
  have hmono : Real.log (a : Real) ≤ Real.log (100000 : Real) := by
    have ha_pos : (0 : Real) < a := by
      exact_mod_cast (show 0 < a by omega)
    apply Real.log_le_log
    · exact ha_pos
    · exact_mod_cast ha100000
  exact hmono.trans log_100000_le_116_over_10


end

end PrimeFactorUnimodality

