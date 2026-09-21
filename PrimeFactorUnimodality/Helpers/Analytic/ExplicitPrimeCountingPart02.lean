import PrimeFactorUnimodality.Helpers.Analytic.ExplicitPrimeCountingPart01


set_option autoImplicit false

/-! # Interfaces for explicit prime-counting estimates -/

namespace PrimeFactorUnimodality

noncomputable section

/-- Dusart's lower comparison function
`x / log x * (1 + 1 / log x)`. -/

theorem integral_inv_log_pow_succ_eq
    {n : Nat} {x : Real} (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / Real.log t ^ (n + 1) =
      x / Real.log x ^ (n + 1) - 2 / Real.log 2 ^ (n + 1) +
        (n + 1 : Real) *
          ∫ t in Set.Icc 2 x, 1 / Real.log t ^ (n + 2) := by
  suffices h_ibp : ∀ a b : Real, 2 ≤ a → a ≤ b →
      ∫ t in a..b, (1 / (Real.log t) ^ (n + 1)) =
        (b / (Real.log b) ^ (n + 1)) -
          (a / (Real.log a) ^ (n + 1)) +
          (n + 1 : Real) *
            ∫ t in a..b, (1 / (Real.log t) ^ (n + 2)) by
    simpa only [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx] using h_ibp 2 x (by norm_num) hx
  intro a b ha hab
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (Real.log t) ^ (n + 1)) t =
        1 / (Real.log t) ^ (n + 1) -
          (n + 1 : Real) * (1 / (Real.log t) ^ (n + 2)) := by
    intro t ht
    exact deriv_log_power_kernel (n := n) (by linarith [ht.1])
  have h_ftc : ∫ t in a..b,
      deriv (fun t ↦ t / (Real.log t) ^ (n + 1)) t =
      (b / (Real.log b) ^ (n + 1)) -
        (a / (Real.log a) ^ (n + 1)) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun y hy ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (Real.differentiableAt_log
          (by cases Set.mem_uIcc.mp hy <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| Real.log_pos <|
          by cases Set.mem_uIcc.mp hy <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := Real.continuousOn_log.mono
        fun y (hy : y ∈ Set.Icc a b) ↦ ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ m : Nat, ∀ y ∈ Set.Icc a b,
          Real.log y ^ m ≠ 0 :=
        fun m y hy ↦ pow_ne_zero m <| ne_of_gt <| Real.log_pos <|
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

theorem integral_inv_log_pow_succ_eq_interval
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / Real.log t ^ (n + 1) =
      b / Real.log b ^ (n + 1) - a / Real.log a ^ (n + 1) +
        (n + 1 : Real) *
          ∫ t in a..b, 1 / Real.log t ^ (n + 2) := by
  have h_deriv : ∀ t ∈ Set.Icc a b,
      deriv (fun t ↦ t / (Real.log t) ^ (n + 1)) t =
        1 / (Real.log t) ^ (n + 1) -
          (n + 1 : Real) * (1 / (Real.log t) ^ (n + 2)) := by
    intro t ht
    exact deriv_log_power_kernel (n := n) (by linarith [ht.1])
  have h_ftc : ∫ t in a..b,
      deriv (fun t ↦ t / (Real.log t) ^ (n + 1)) t =
      (b / (Real.log b) ^ (n + 1)) -
        (a / (Real.log a) ^ (n + 1)) := by
    rw [intervalIntegral.integral_deriv_eq_sub']
    · rfl
    · exact fun y hy ↦ DifferentiableAt.div differentiableAt_id
        (DifferentiableAt.pow (Real.differentiableAt_log
          (by cases Set.mem_uIcc.mp hy <;> linarith)) _)
        (pow_ne_zero _ <| ne_of_gt <| Real.log_pos <|
          by cases Set.mem_uIcc.mp hy <;> linarith)
    · rw [Set.uIcc_of_le hab]
      have hlog_cont := Real.continuousOn_log.mono
        fun y (hy : y ∈ Set.Icc a b) ↦ ne_of_gt <| by linarith [hy.1]
      have hpow_ne : ∀ m : Nat, ∀ y ∈ Set.Icc a b,
          Real.log y ^ m ≠ 0 :=
        fun m y hy ↦ pow_ne_zero m <| ne_of_gt <| Real.log_pos <|
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

theorem strictMonoOn_id_div_log_pow
    {n : Nat} {a : Real} (ha : 1 < a)
    (hcoef : (n + 1 : Real) < Real.log a) :
    StrictMonoOn (fun t : Real => t / Real.log t ^ (n + 1)) (Set.Ici a) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici a)
  · apply ContinuousOn.div continuousOn_id
    · exact (Real.continuousOn_log.mono (fun y hy =>
        have hy' : a ≤ y := hy
        ne_of_gt (by linarith [ha, hy']))).pow _
    · intro y hy
      have hy' : a ≤ y := hy
      exact pow_ne_zero _
        (ne_of_gt (Real.log_pos (lt_of_lt_of_le ha hy')))
  · intro t ht
    have hta : a < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have hlog : 0 < Real.log t := Real.log_pos (lt_trans ha hta)
    have hlog_gt : (n + 1 : Real) < Real.log t :=
      lt_of_lt_of_le hcoef (Real.log_le_log (by linarith) hta.le)
    rw [deriv_log_power_kernel (n := n) (by linarith)]
    have hnum : 0 < Real.log t - (n + 1 : Real) := by linarith
    field_simp [ne_of_gt hlog]
    have hp : 0 < Real.log t ^ n * Real.log t :=
      mul_pos (pow_pos hlog n) hlog
    simpa [pow_succ] using (mul_lt_mul_of_pos_left hlog_gt hp)

theorem id_div_log_pow_le_of_le
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a ≤ b)
    (hcoef : (n + 1 : Real) < Real.log a) :
    a / Real.log a ^ (n + 1) ≤ b / Real.log b ^ (n + 1) := by
  rcases hab.eq_or_lt with rfl | hlt
  · rfl
  · exact (strictMonoOn_id_div_log_pow ha hcoef
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hab) hlt).le

theorem inv_log_pow_le_of_le
    {m : Nat} {X x : Real} (hX : 1 < X) (hXx : X ≤ x) :
    1 / Real.log x ^ m ≤ 1 / Real.log X ^ m := by
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlog_le : Real.log X ≤ Real.log x :=
    Real.log_le_log (by linarith) hXx
  have hlogx : 0 < Real.log x := lt_of_lt_of_le hlogX hlog_le
  have hinv : 1 / Real.log x ≤ 1 / Real.log X :=
    one_div_le_one_div_of_le hlogX hlog_le
  have hqx : 0 ≤ 1 / Real.log x := one_div_nonneg.mpr hlogx.le
  have hpow : (1 / Real.log x) ^ m ≤ (1 / Real.log X) ^ m := by
    exact pow_le_pow_left₀ hqx hinv m
  simpa [div_pow] using hpow

theorem id_div_log_pow_add_le
    {m : Nat} {X x : Real} (hX : 1 < X) (hXx : X ≤ x) :
    x / Real.log x ^ (4 + m) ≤
      (x / Real.log x ^ 4) / Real.log X ^ m := by
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hbase : 0 ≤ x / Real.log x ^ 4 :=
    div_nonneg hxpos.le (pow_nonneg hlogx.le _)
  have hpow := inv_log_pow_le_of_le (m := m) hX hXx
  calc
    x / Real.log x ^ (4 + m) =
        (x / Real.log x ^ 4) * (1 / Real.log x ^ m) := by
      field_simp [ne_of_gt hlogx]
      rw [pow_add]
    _ ≤ (x / Real.log x ^ 4) * (1 / Real.log X ^ m) :=
      mul_le_mul_of_nonneg_left hpow hbase
    _ = (x / Real.log x ^ 4) / Real.log X ^ m := by ring

theorem integral_inv_log_pow_succ_le_of_next_bound
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a ≤ b)
    (hnext : (∫ t in a..b, 1 / Real.log t ^ (n + 2)) ≤
      (∫ t in a..b, 1 / Real.log t ^ (n + 1)) / Real.log a)
    (hcoef : (n + 1 : Real) < Real.log a) :
    (∫ t in a..b, 1 / Real.log t ^ (n + 1)) ≤
      (b / Real.log b ^ (n + 1)) /
        (1 - (n + 1 : Real) / Real.log a) := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hden : 0 < 1 - (n + 1 : Real) / Real.log a := by
    rw [sub_pos]
    apply (div_lt_iff₀ hloga).2
    nlinarith [hcoef]
  have hleft : 0 ≤ a / Real.log a ^ (n + 1) := by positivity
  have hidentity := integral_inv_log_pow_succ_eq_interval
    (n := n) ha hab
  have hcoef_nonneg : 0 ≤ (n + 1 : Real) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hnext hcoef_nonneg
  have hineq :
      (∫ t in a..b, 1 / Real.log t ^ (n + 1)) ≤
        b / Real.log b ^ (n + 1) +
          (n + 1 : Real) *
            ((∫ t in a..b, 1 / Real.log t ^ (n + 1)) /
              Real.log a) := by
    calc
      (∫ t in a..b, 1 / Real.log t ^ (n + 1)) =
          b / Real.log b ^ (n + 1) - a / Real.log a ^ (n + 1) +
            (n + 1 : Real) *
              ∫ t in a..b, 1 / Real.log t ^ (n + 2) := hidentity
      _ ≤ b / Real.log b ^ (n + 1) +
            (n + 1 : Real) *
              ∫ t in a..b, 1 / Real.log t ^ (n + 2) := by
        nlinarith
      _ ≤ b / Real.log b ^ (n + 1) +
            (n + 1 : Real) *
              ((∫ t in a..b, 1 / Real.log t ^ (n + 1)) /
                Real.log a) := by
        simpa [add_comm] using add_le_add_left hmul
          (b / Real.log b ^ (n + 1))
  apply (le_div_iff₀ hden).2
  have htarget := hineq
  field_simp [ne_of_gt hloga] at htarget ⊢
  nlinarith

theorem integral_inv_log_pow_next_bound
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / Real.log t ^ (n + 2)) ≤
      (∫ t in a..b, 1 / Real.log t ^ (n + 1)) / Real.log a := by
  have hcont : ∀ m : Nat, ContinuousOn
      (fun t : Real => 1 / Real.log t ^ m) (Set.uIcc a b) := by
    intro m
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun y hy =>
        ne_of_gt (by linarith [hy.1])).pow _
    · intro y hy
      exact pow_ne_zero _ (ne_of_gt (Real.log_pos (by linarith [hy.1])))
  have hfi : IntervalIntegrable
      (fun t : Real => 1 / Real.log t ^ (n + 2))
      MeasureTheory.volume a b := (hcont (n + 2)).intervalIntegrable
  have hgi : IntervalIntegrable
      (fun t : Real => (1 / Real.log a) * (1 / Real.log t ^ (n + 1)))
      MeasureTheory.volume a b :=
    ((continuousOn_const.mul (hcont (n + 1))).intervalIntegrable)
  have hmono : ∀ t ∈ Set.Icc a b,
      1 / Real.log t ^ (n + 2) ≤
        (1 / Real.log a) * (1 / Real.log t ^ (n + 1)) := by
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have hloga : 0 < Real.log a := Real.log_pos ha
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hlog_le : Real.log a ≤ Real.log t :=
      Real.log_le_log (by linarith) ht.1
    have hinv : 1 / Real.log t ≤ 1 / Real.log a :=
      (one_div_le_one_div_of_le hloga hlog_le)
    have hpow : 0 ≤ 1 / Real.log t ^ (n + 1) := by positivity
    calc
      1 / Real.log t ^ (n + 2) =
          (1 / Real.log t ^ (n + 1)) * (1 / Real.log t) := by
            field_simp [ne_of_gt hlogt]
            rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ,
              pow_succ]
      _ ≤ (1 / Real.log t ^ (n + 1)) * (1 / Real.log a) :=
        mul_le_mul_of_nonneg_left hinv hpow
      _ = (1 / Real.log a) * (1 / Real.log t ^ (n + 1)) := by ring
  have hintegral := intervalIntegral.integral_mono_on hab hfi hgi hmono
  simpa [div_eq_mul_inv, mul_comm] using hintegral

theorem integral_inv_log_pow_succ_le
    {n : Nat} {a b : Real} (ha : 1 < a) (hab : a ≤ b)
    (hcoef : (n + 1 : Real) < Real.log a) :
    (∫ t in a..b, 1 / Real.log t ^ (n + 1)) ≤
      (b / Real.log b ^ (n + 1)) /
        (1 - (n + 1 : Real) / Real.log a) :=
  integral_inv_log_pow_succ_le_of_next_bound ha hab
    (integral_inv_log_pow_next_bound ha hab) hcoef

theorem integral_inv_log_pow_succ_le_split_at_million
    {n : Nat} {X : Real} (hX : (1000000 : Real) ≤ X)
    (hcoef : (n + 1 : Real) < Real.log (1000000 : Real)) :
    (∫ t in (2 : Real)..X, 1 / Real.log t ^ (n + 1)) ≤
      (∫ t in (2 : Real)..(1000000 : Real),
        1 / Real.log t ^ (n + 1)) +
      (X / Real.log X ^ (n + 1)) /
        (1 - (n + 1 : Real) / Real.log (1000000 : Real)) := by
  have hcont : ContinuousOn
      (fun t : Real => 1 / Real.log t ^ (n + 1))
      (Set.Icc (2 : Real) X) := by
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (by linarith [ht.1])).pow _
    · intro t ht
      exact pow_ne_zero _
        (ne_of_gt (Real.log_pos (by linarith [ht.1])))
  have hleft : IntervalIntegrable
      (fun t : Real => 1 / Real.log t ^ (n + 1))
      MeasureTheory.volume 2 (1000000 : Real) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (2 : Real) ≤ 1000000)]
    exact hcont.mono (Set.Icc_subset_Icc le_rfl hX)
  have hright : IntervalIntegrable
      (fun t : Real => 1 / Real.log t ^ (n + 1))
      MeasureTheory.volume (1000000 : Real) X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hX]
    exact hcont.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have htail := integral_inv_log_pow_succ_le
    (n := n) (a := (1000000 : Real)) (b := X)
    (by norm_num) hX hcoef
  rw [← hsplit]
  exact add_le_add_right htail _

theorem integral_inv_log_pow_succ_low_le_at_million
    (n : Nat) :
    (∫ t in (2 : Real)..(1000000 : Real),
      1 / Real.log t ^ (n + 1)) ≤
      (999998 : Real) / Real.log 2 ^ (n + 1) := by
  have hcont : ContinuousOn
      (fun t : Real => 1 / Real.log t ^ (n + 1))
      (Set.Icc (2 : Real) (1000000 : Real)) := by
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (by linarith [ht.1])).pow _
    · intro t ht
      exact pow_ne_zero _
        (ne_of_gt (Real.log_pos (by linarith [ht.1])))
  have hfi : IntervalIntegrable
      (fun t : Real => 1 / Real.log t ^ (n + 1))
      MeasureTheory.volume 2 (1000000 : Real) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (2 : Real) ≤ 1000000)]
    exact hcont
  have hgi : IntervalIntegrable
      (fun _ : Real => 1 / Real.log 2 ^ (n + 1))
      MeasureTheory.volume 2 (1000000 : Real) :=
    intervalIntegrable_const
  have hpoint : ∀ t ∈ Set.Icc (2 : Real) (1000000 : Real),
      1 / Real.log t ^ (n + 1) ≤ 1 / Real.log 2 ^ (n + 1) := by
    intro t ht
    exact inv_log_pow_le_of_le (m := n + 1) (by norm_num) ht.1
  have hmono := intervalIntegral.integral_mono_on
    (by norm_num : (2 : Real) ≤ 1000000) hfi hgi hpoint
  calc
    (∫ t in (2 : Real)..(1000000 : Real),
        1 / Real.log t ^ (n + 1)) ≤
        ∫ t in (2 : Real)..(1000000 : Real),
          (1 / Real.log 2 ^ (n + 1)) := hmono
    _ = (999998 : Real) / Real.log 2 ^ (n + 1) := by
      rw [intervalIntegral.integral_const]
      norm_num
      ring

theorem integral_inv_log_pow_succ_le_explicit_at_million
    {n : Nat} {X : Real} (hX : (1000000 : Real) ≤ X)
    (hcoef : (n + 1 : Real) < Real.log (1000000 : Real)) :
    (∫ t in (2 : Real)..X, 1 / Real.log t ^ (n + 1)) ≤
      (999998 : Real) / Real.log 2 ^ (n + 1) +
      (X / Real.log X ^ (n + 1)) /
        (1 - (n + 1 : Real) / Real.log (1000000 : Real)) := by
  have hsplit := integral_inv_log_pow_succ_le_split_at_million hX hcoef
  have hlow := integral_inv_log_pow_succ_low_le_at_million n
  calc
    (∫ t in (2 : Real)..X, 1 / Real.log t ^ (n + 1)) ≤
        (∫ t in (2 : Real)..(1000000 : Real),
          1 / Real.log t ^ (n + 1)) +
          (X / Real.log X ^ (n + 1)) /
            (1 - (n + 1 : Real) / Real.log (1000000 : Real)) := hsplit
    _ ≤ (999998 : Real) / Real.log 2 ^ (n + 1) +
          (X / Real.log X ^ (n + 1)) /
            (1 - (n + 1 : Real) / Real.log (1000000 : Real)) := by
      convert add_le_add_left hlow
        ((X / Real.log X ^ (n + 1)) /
          (1 - (n + 1 : Real) / Real.log (1000000 : Real))) using 1 <;> ring

theorem six_lt_log_million :
    (6 : Real) < Real.log (1000000 : Real) := by
  apply (Real.lt_log_iff_exp_lt (by norm_num)).2
  have hexp : Real.exp 6 < (3 : Real) ^ 6 := by
    rw [show (6 : Real) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ Real.exp_one_lt_three
      (Real.exp_pos 1).le (by norm_num)
  exact hexp.trans (by norm_num)

theorem seven_lt_log_million :
    (7 : Real) < Real.log (1000000 : Real) := by
  apply (Real.lt_log_iff_exp_lt (by norm_num)).2
  have hexp : Real.exp 7 < (3 : Real) ^ 7 := by
    rw [show (7 : Real) = (7 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ Real.exp_one_lt_three
      (Real.exp_pos 1).le (by norm_num)
  exact hexp.trans (by norm_num)

theorem integral_inv_log_six_le_explicit {X : Real}
    (hX : (1000000 : Real) ≤ X) :
    (∫ t in (2 : Real)..X, 1 / Real.log t ^ 6) ≤
      (999998 : Real) / Real.log 2 ^ 6 +
      (X / Real.log X ^ 6) /
        (1 - 6 / Real.log (1000000 : Real)) := by
  convert integral_inv_log_pow_succ_le_explicit_at_million
    (n := 5) hX (by norm_num; exact six_lt_log_million) using 1 <;> norm_num

theorem integral_inv_log_seven_le_explicit {X : Real}
    (hX : (1000000 : Real) ≤ X) :
    (∫ t in (2 : Real)..X, 1 / Real.log t ^ 7) ≤
      (999998 : Real) / Real.log 2 ^ 7 +
      (X / Real.log X ^ 7) /
        (1 - 7 / Real.log (1000000 : Real)) := by
  convert integral_inv_log_pow_succ_le_explicit_at_million
    (n := 6) hX (by norm_num; exact seven_lt_log_million) using 1 <;> norm_num

theorem integral_inv_log_pow_succ_le_full_from_two
    {n : Nat} {a b : Real} (ha : (2 : Real) ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / Real.log t ^ (n + 1)) ≤
      ∫ t in (2 : Real)..b, 1 / Real.log t ^ (n + 1) := by
  have hleft : IntervalIntegrable
      (fun t : Real => 1 / Real.log t ^ (n + 1))
      MeasureTheory.volume 2 a := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ha]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (by
          have : (0 : Real) < t := lt_of_lt_of_le (by norm_num) ht.1
          exact this)).pow _
    · intro t ht
      exact pow_ne_zero _ (ne_of_gt (Real.log_pos (by
        have : (1 : Real) < t :=
          lt_of_lt_of_le (by norm_num) ht.1
        exact this)))
  have hright : IntervalIntegrable
      (fun t : Real => 1 / Real.log t ^ (n + 1))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuousOn_log.mono fun t ht =>
        ne_of_gt (by
          have : (0 : Real) < t :=
            lt_of_lt_of_le (by norm_num) (ha.trans ht.1)
          exact this)).pow _
    · intro t ht
      exact pow_ne_zero _ (ne_of_gt (Real.log_pos (by
        have : (1 : Real) < t :=
          lt_of_lt_of_le (by norm_num) (ha.trans ht.1)
        exact this)))
  have hzero : IntervalIntegrable (fun _ : Real => (0 : Real))
      MeasureTheory.volume 2 a := intervalIntegrable_const
  have hnonneg : ∀ t ∈ Set.Icc (2 : Real) a,
      0 ≤ 1 / Real.log t ^ (n + 1) := by
    intro t ht
    have hlog : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact one_div_nonneg.mpr (pow_nonneg hlog.le _)
  have hprefix : 0 ≤ ∫ t in (2 : Real)..a,
      1 / Real.log t ^ (n + 1) := by
    simpa [intervalIntegral.integral_const] using
      intervalIntegral.integral_mono_on ha hzero hleft hnonneg
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [← hadd]
  linarith

theorem integral_inv_log_six_tail_from_599_le_explicit {X : Real}
    (hX : (1000000 : Real) ≤ X) :
    (∫ t in (599 : Real)..X, 1 / Real.log t ^ 6) ≤
      (999998 : Real) / Real.log 2 ^ 6 +
        (X / Real.log X ^ 6) /
          (1 - 6 / Real.log (1000000 : Real)) := by
  exact (integral_inv_log_pow_succ_le_full_from_two
    (n := 5) (a := (599 : Real)) (b := X) (by norm_num)
      (by linarith [hX])).trans
      (integral_inv_log_six_le_explicit hX)

theorem explicit_integral_core_bound_of_log_margins
    {A X : Real} (hX : (4e18 : Real) ≤ X) (hA0 : 0 ≤ A)
    (hA1 : A ≤ 1) (hlog2 : (69 : Real) / 100 ≤ Real.log 2)
    (hlogMillion : (13 : Real) ≤ Real.log (1000000 : Real))
    (hlogCut : (42 : Real) ≤ Real.log (4e18 : Real))
    (hR : (4e18 : Real) / (43 : Real) ^ 4 ≤
      X / Real.log X ^ 4) :
    4000 +
        720 * ((999998 : Real) / Real.log 2 ^ 7 +
          (X / Real.log X ^ 7) /
            (1 - 7 / Real.log (1000000 : Real))) +
        A * ((999998 : Real) / Real.log 2 ^ 6 +
          (X / Real.log X ^ 6) /
            (1 - 6 / Real.log (1000000 : Real))) + 10000 ≤
      (3 / 5 : Real) * X / Real.log X ^ 4 := by
  have hlogX : (0 : Real) < Real.log X := by
    exact Real.log_pos (by linarith [hX])
  have hR0 : 0 ≤ X / Real.log X ^ 4 := by positivity
  have hlogM : 0 < Real.log (1000000 : Real) := by linarith
  have hfrac7 : (7 : Real) / Real.log (1000000 : Real) ≤ 7 / 13 := by
    apply (div_le_iff₀ hlogM).2
    nlinarith
  have hfrac6 : (6 : Real) / Real.log (1000000 : Real) ≤ 6 / 13 := by
    apply (div_le_iff₀ hlogM).2
    nlinarith
  have hden7 : (6 : Real) / 13 ≤
      1 - 7 / Real.log (1000000 : Real) := by linarith
  have hden6 : (7 : Real) / 13 ≤
      1 - 6 / Real.log (1000000 : Real) := by linarith
  have hden7pos : 0 < 1 - 7 / Real.log (1000000 : Real) :=
    lt_of_lt_of_le (by norm_num) hden7
  have hden6pos : 0 < 1 - 6 / Real.log (1000000 : Real) :=
    lt_of_lt_of_le (by norm_num) hden6
  have hinv7 : 1 / (1 - 7 / Real.log (1000000 : Real)) ≤
      (13 : Real) / 6 :=
    (one_div_le_one_div_of_le (by norm_num) hden7).trans_eq (by norm_num)
  have hinv6 : 1 / (1 - 6 / Real.log (1000000 : Real)) ≤
      (13 : Real) / 7 :=
    (one_div_le_one_div_of_le (by norm_num) hden6).trans_eq (by norm_num)
  have hpow6 : ((69 : Real) / 100) ^ 6 ≤ (Real.log 2) ^ 6 :=
    pow_le_pow_left₀ (by norm_num) hlog2 6
  have hpow7 : ((69 : Real) / 100) ^ 7 ≤ (Real.log 2) ^ 7 :=
    pow_le_pow_left₀ (by norm_num) hlog2 7
  have hi6 : 1 / (Real.log 2) ^ 6 ≤
      1 / ((69 : Real) / 100) ^ 6 :=
    one_div_le_one_div_of_le (by positivity) hpow6
  have hi7 : 1 / (Real.log 2) ^ 7 ≤
      1 / ((69 : Real) / 100) ^ 7 :=
    one_div_le_one_div_of_le (by positivity) hpow7
  have hlow6 : (999998 : Real) / Real.log 2 ^ 6 ≤ 10000000 := by
    calc
      (999998 : Real) / Real.log 2 ^ 6 =
          999998 * (1 / Real.log 2 ^ 6) := by ring
      _ ≤ 999998 * (1 / ((69 : Real) / 100) ^ 6) :=
        mul_le_mul_of_nonneg_left hi6 (by norm_num)
      _ ≤ 10000000 := by norm_num
  have hlow7 : (999998 : Real) / Real.log 2 ^ 7 ≤ 14000000 := by
    calc
      (999998 : Real) / Real.log 2 ^ 7 =
          999998 * (1 / Real.log 2 ^ 7) := by ring
      _ ≤ 999998 * (1 / ((69 : Real) / 100) ^ 7) :=
        mul_le_mul_of_nonneg_left hi7 (by norm_num)
      _ ≤ 14000000 := by norm_num
  have hlogCut' : (4 : Real) < Real.log (4e18 : Real) := by
    linarith
  have hpowRel6 : X / Real.log X ^ 6 ≤
      (X / Real.log X ^ 4) / (42 : Real) ^ 2 := by
    calc
      X / Real.log X ^ 6 ≤
          (X / Real.log X ^ 4) /
            Real.log (4e18) ^ 2 :=
        id_div_log_pow_add_le (m := 2) (by norm_num) hX
      _ ≤ (X / Real.log X ^ 4) / (42 : Real) ^ 2 := by
        exact div_le_div_of_nonneg_left hR0 (by positivity)
          (pow_le_pow_left₀ (by norm_num) hlogCut 2)
  have hpowRel7 : X / Real.log X ^ 7 ≤
      (X / Real.log X ^ 4) / (42 : Real) ^ 3 := by
    calc
      X / Real.log X ^ 7 ≤
          (X / Real.log X ^ 4) /
            Real.log (4e18) ^ 3 :=
        id_div_log_pow_add_le (m := 3) (by norm_num) hX
      _ ≤ (X / Real.log X ^ 4) / (42 : Real) ^ 3 := by
        exact div_le_div_of_nonneg_left hR0 (by positivity)
          (pow_le_pow_left₀ (by norm_num) hlogCut 3)
  have htail7 :
      (X / Real.log X ^ 7) /
          (1 - 7 / Real.log (1000000 : Real)) ≤
        ((13 : Real) / 6) *
          ((X / Real.log X ^ 4) / (42 : Real) ^ 3) := by
    calc
      (X / Real.log X ^ 7) /
          (1 - 7 / Real.log (1000000 : Real)) =
          (X / Real.log X ^ 7) *
            (1 / (1 - 7 / Real.log (1000000 : Real))) := by ring
      _ ≤ ((13 : Real) / 6) *
          (X / Real.log X ^ 7) := by
        convert mul_le_mul_of_nonneg_right hinv7
          (by positivity : (0 : Real) ≤ X / Real.log X ^ 7) using 1 <;> ring
      _ ≤ ((13 : Real) / 6) *
          ((X / Real.log X ^ 4) / (42 : Real) ^ 3) := by
        gcongr
  have htail6 :
      (X / Real.log X ^ 6) /
          (1 - 6 / Real.log (1000000 : Real)) ≤
        ((13 : Real) / 7) *
          ((X / Real.log X ^ 4) / (42 : Real) ^ 2) := by
    calc
      (X / Real.log X ^ 6) /
          (1 - 6 / Real.log (1000000 : Real)) =
          (X / Real.log X ^ 6) *
            (1 / (1 - 6 / Real.log (1000000 : Real))) := by ring
      _ ≤ ((13 : Real) / 7) *
          (X / Real.log X ^ 6) := by
        convert mul_le_mul_of_nonneg_right hinv6
          (by positivity : (0 : Real) ≤ X / Real.log X ^ 6) using 1 <;> ring
      _ ≤ ((13 : Real) / 7) *
          ((X / Real.log X ^ 4) / (42 : Real) ^ 2) := by
        gcongr
  have hlow6' : 0 ≤ (999998 : Real) / Real.log 2 ^ 6 := by positivity
  have hlow7' : 0 ≤ (999998 : Real) / Real.log 2 ^ 7 := by positivity
  have htail6' : 0 ≤
      (X / Real.log X ^ 6) /
        (1 - 6 / Real.log (1000000 : Real)) :=
    div_nonneg (by positivity) hden6pos.le
  have htail7' : 0 ≤
      (X / Real.log X ^ 7) /
        (1 - 7 / Real.log (1000000 : Real)) :=
    div_nonneg (by positivity) hden7pos.le
  have hA6 := mul_le_mul_of_nonneg_left htail6 hA0
  have hA7 := mul_le_mul_of_nonneg_left htail7 hA0
  have hA_tail6 : A *
      ((X / Real.log X ^ 6) /
        (1 - 6 / Real.log (1000000 : Real))) ≤
      (13 / 7 : Real) *
        ((X / Real.log X ^ 4) / (42 : Real) ^ 2) := by
    calc
      A * ((X / Real.log X ^ 6) /
          (1 - 6 / Real.log (1000000 : Real))) ≤
          A * ((13 / 7 : Real) *
            ((X / Real.log X ^ 4) / (42 : Real) ^ 2)) := hA6
      _ ≤ (13 / 7 : Real) *
          ((X / Real.log X ^ 4) / (42 : Real) ^ 2) := by
        exact (mul_le_mul_of_nonneg_right hA1 (by positivity)).trans_eq
          (by ring)
  have hA_low6 : A * ((999998 : Real) / Real.log 2 ^ 6) ≤
      (999998 : Real) / Real.log 2 ^ 6 := by
    exact (mul_le_mul_of_nonneg_right hA1 hlow6').trans_eq (by ring)
  have hA_sum6 : A * ((999998 : Real) / Real.log 2 ^ 6 +
        (X / Real.log X ^ 6) /
          (1 - 6 / Real.log (1000000 : Real))) ≤
      (999998 : Real) / Real.log 2 ^ 6 +
        (13 / 7 : Real) *
          ((X / Real.log X ^ 4) / (42 : Real) ^ 2) := by
    calc
      A * ((999998 : Real) / Real.log 2 ^ 6 +
          (X / Real.log X ^ 6) /
            (1 - 6 / Real.log (1000000 : Real))) =
          A * (999998 / Real.log 2 ^ 6) +
            A * ((X / Real.log X ^ 6) /
              (1 - 6 / Real.log (1000000 : Real))) := by ring
      _ ≤ (999998 : Real) / Real.log 2 ^ 6 +
          (13 / 7 : Real) *
            ((X / Real.log X ^ 4) / (42 : Real) ^ 2) :=
        add_le_add hA_low6 hA_tail6
  have hbase7 : (0 : Real) ≤
      (999998 : Real) / Real.log 2 ^ 7 := hlow7'
  have htail7_bound : 0 ≤
      (13 / 6 : Real) *
        ((X / Real.log X ^ 4) / (42 : Real) ^ 3) := by positivity
  calc
    4000 + 720 * (999998 / Real.log 2 ^ 7 +
        (X / Real.log X ^ 7) /
          (1 - 7 / Real.log (1000000 : Real))) +
        A * (999998 / Real.log 2 ^ 6 +
          (X / Real.log X ^ 6) /
            (1 - 6 / Real.log (1000000 : Real))) + 10000
        ≤ 4000 + 720 * (14000000 +
            (13 / 6 : Real) * ((X / Real.log X ^ 4) / 42 ^ 3)) +
          10000000 + (13 / 7 : Real) *
            ((X / Real.log X ^ 4) / 42 ^ 2) := by
          have hlow7s := mul_le_mul_of_nonneg_left hlow7
            (by norm_num : (0 : Real) ≤ 720)
          have htail7s := mul_le_mul_of_nonneg_left htail7
            (by norm_num : (0 : Real) ≤ 720)
          have hsum :
              720 * (999998 / Real.log 2 ^ 7 +
                (X / Real.log X ^ 7) /
                  (1 - 7 / Real.log (1000000 : Real))) +
                A * (999998 / Real.log 2 ^ 6 +
                  (X / Real.log X ^ 6) /
                    (1 - 6 / Real.log (1000000 : Real))) ≤
              720 * (14000000 +
                (13 / 6 : Real) * ((X / Real.log X ^ 4) / 42 ^ 3)) +
                10000000 + (13 / 7 : Real) *
                  ((X / Real.log X ^ 4) / 42 ^ 2) := by
            calc
              _ = 720 * (999998 / Real.log 2 ^ 7) +
                    720 * ((X / Real.log X ^ 7) /
                      (1 - 7 / Real.log (1000000 : Real))) +
                    (A * (999998 / Real.log 2 ^ 6) +
                      A * ((X / Real.log X ^ 6) /
                        (1 - 6 / Real.log (1000000 : Real)))) := by ring
              _ ≤ 720 * 14000000 + 720 *
                    ((13 / 6 : Real) *
                      ((X / Real.log X ^ 4) / 42 ^ 3)) +
                    ((999998 : Real) / Real.log 2 ^ 6 +
                      (13 / 7 : Real) *
                        ((X / Real.log X ^ 4) / 42 ^ 2)) := by
                exact add_le_add (add_le_add hlow7s htail7s)
                  (add_le_add hA_low6 hA_tail6)
              _ ≤ 720 * (14000000 +
                    (13 / 6 : Real) *
                      ((X / Real.log X ^ 4) / 42 ^ 3)) +
                    10000000 + (13 / 7 : Real) *
                      ((X / Real.log X ^ 4) / 42 ^ 2) := by
                nlinarith [hlow6]
          have hlow6tight : (999998 : Real) / Real.log 2 ^ 6 ≤ 9990000 := by
            calc
              (999998 : Real) / Real.log 2 ^ 6 =
                  999998 * (1 / Real.log 2 ^ 6) := by ring
              _ ≤ 999998 * (1 / ((69 : Real) / 100) ^ 6) :=
                mul_le_mul_of_nonneg_left hi6 (by norm_num)
              _ ≤ 9990000 := by norm_num
          linarith [hsum, hlow6tight]
    _ ≤ (3 / 5 : Real) * X / Real.log X ^ 4 := by
          have hnum :
              (4000 : Real) + 720 * (14000000 +
                  (13 / 6 : Real) * (((4e18 : Real) / 43 ^ 4) / 42 ^ 3)) +
                10000000 + (13 / 7 : Real) *
                  (((4e18 : Real) / 43 ^ 4) / 42 ^ 2) ≤
                (3 / 5 : Real) * ((4e18 : Real) / 43 ^ 4) := by
            norm_num
          ring_nf at hR ⊢
          ring_nf at hnum
          linarith [hR, hnum]

theorem lower_bound_div_log_four_of_four_e18_le {X : Real}
    (hX : (4e18 : Real) ≤ X) :
    (4e18 : Real) / (43 : Real) ^ 4 ≤ X / Real.log X ^ 4 := by
  have hlog42 : (42 : Real) < Real.log (4e18 : Real) := by
    apply (Real.lt_log_iff_exp_lt (by norm_num)).2
    have hexp : Real.exp 42 < (2.72 : Real) ^ 42 := by
      rw [show (42 : Real) = (42 : ℕ) * 1 by norm_num,
        Real.exp_nat_mul]
      exact pow_lt_pow_left₀ (by
        linarith [Real.exp_one_lt_d9]) (Real.exp_pos 1).le (by norm_num)
    exact hexp.trans (by norm_num)
  have hlog43 : Real.log (4e18 : Real) < 43 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).2
    have hnum : (4e18 : Real) < (2.718 : Real) ^ (43 : Nat) := by
      norm_num
    have hbase : (2.718 : Real) < Real.exp 1 := by
      exact (by norm_num : (2.718 : Real) < (2.7182818283 : Real)).trans
        Real.exp_one_gt_d9
    calc
      (4e18 : Real) < (2.718 : Real) ^ (43 : Nat) := hnum
      _ < (Real.exp 1) ^ (43 : Nat) := by
        exact pow_lt_pow_left₀ hbase (by norm_num) (by norm_num)
      _ = Real.exp 43 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hmono :
      (4e18 : Real) / Real.log (4e18 : Real) ^ 4 ≤
        X / Real.log X ^ 4 :=
    id_div_log_pow_le_of_le (n := 3) (by norm_num) hX (by linarith)
  have hbase : (4e18 : Real) / (43 : Real) ^ 4 ≤
      (4e18 : Real) / Real.log (4e18 : Real) ^ 4 := by
    apply div_le_div_of_nonneg_left (by norm_num)
      (by positivity : 0 < Real.log (4e18 : Real) ^ 4)
    exact pow_le_pow_left₀ (by positivity) hlog43.le 4
  exact hbase.trans hmono

end

end PrimeFactorUnimodality
