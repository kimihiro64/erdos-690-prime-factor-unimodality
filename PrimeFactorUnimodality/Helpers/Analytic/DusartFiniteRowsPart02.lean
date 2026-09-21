import PrimeFactorUnimodality.Helpers.Analytic.DusartFiniteRowsPart01


set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section


theorem dusartLemma33FiniteRowsCover_five :
    DusartLemma33FiniteRowsCover
      [dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five] 5 := by
  intro x hx hX
  by_cases hsmall : x < 2
  · refine ⟨dusartLemma33FiniteRow_zero_one, by simp, ?_, ?_⟩
    · norm_num [dusartLemma33FiniteRow_zero_one]
      exact hx.le
    · norm_num [dusartLemma33FiniteRow_zero_one]
      linarith
  · by_cases htwo : x < 3
    · refine ⟨dusartLemma33FiniteRow_two, by simp, ?_, ?_⟩
      · norm_num [dusartLemma33FiniteRow_two]
        exact le_of_not_gt hsmall
      · norm_num [dusartLemma33FiniteRow_two]
        linarith
    · by_cases hthree : x < 4
      · refine ⟨dusartLemma33FiniteRow_three, by simp, ?_, ?_⟩
        · norm_num [dusartLemma33FiniteRow_three]
          exact le_of_not_gt htwo
        · norm_num [dusartLemma33FiniteRow_three]
          linarith
      · by_cases hfour : x < 5
        · refine ⟨dusartLemma33FiniteRow_four, by simp, ?_, ?_⟩
          · norm_num [dusartLemma33FiniteRow_four]
            exact le_of_not_gt hthree
          · norm_num [dusartLemma33FiniteRow_four]
            linarith
        · refine ⟨dusartLemma33FiniteRow_five, by simp, ?_, ?_⟩
          · norm_num [dusartLemma33FiniteRow_five]
            exact le_of_not_gt hfour
          · have hright : x < 6 := by linarith
            convert hright using 1 <;>
              norm_num [dusartLemma33FiniteRow_five,
                dusartLemma33FiniteRow_of_zero]

def dusartLemma33FiniteRow_six : DusartLemma33FiniteRow := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 6
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 6
  have htheta_two := Chebyshev.theta_eq_sum_primesLE_log 2
  have hp6 : Nat.primesLE 6 = {2, 3, 5} := by decide
  have hp2 : Nat.primesLE 2 = {2} := by decide
  rw [hp6] at hpsi htheta
  rw [hp2] at htheta_two
  norm_num [Nat.log, Nat.log.go] at hpsi htheta htheta_two
  apply dusartLemma33FiniteRow_of_zero 6 2
  · intro x hx hleft hright
    have hx6 : (6 : Real) ≤ x := hleft
    have hx7 : x < 7 := by norm_num at hright ⊢; exact hright
    apply (Nat.floor_eq_iff (by positivity : (0 : Real) ≤ Real.sqrt x)).2
    constructor
    · norm_num
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    · norm_num
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · ring_nf at hpsi htheta htheta_two ⊢
    linarith [hpsi, htheta, htheta_two]

def dusartLemma33FiniteRow_seven : DusartLemma33FiniteRow := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 7
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 7
  have htheta_two := Chebyshev.theta_eq_sum_primesLE_log 2
  have hp7 : Nat.primesLE 7 = {2, 3, 5, 7} := by decide
  have hp2 : Nat.primesLE 2 = {2} := by decide
  rw [hp7] at hpsi htheta
  rw [hp2] at htheta_two
  norm_num [Nat.log, Nat.log.go] at hpsi htheta htheta_two
  apply dusartLemma33FiniteRow_of_zero 7 2
  · intro x hx hleft hright
    have hx7 : (7 : Real) ≤ x := hleft
    have hx8 : x < 8 := by norm_num at hright ⊢; exact hright
    apply (Nat.floor_eq_iff (by positivity : (0 : Real) ≤ Real.sqrt x)).2
    constructor
    · norm_num
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    · norm_num
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · ring_nf at hpsi htheta htheta_two ⊢
    linarith [hpsi, htheta, htheta_two]

theorem dusartLemma33FiniteRowsCover_seven :
    DusartLemma33FiniteRowsCover
      [dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven] 7 := by
  intro x hx hX
  by_cases hsmall : x < 2
  · refine ⟨dusartLemma33FiniteRow_zero_one, by simp, ?_, ?_⟩
    · norm_num [dusartLemma33FiniteRow_zero_one]
      exact hx.le
    · norm_num [dusartLemma33FiniteRow_zero_one]
      linarith
  · by_cases htwo : x < 3
    · refine ⟨dusartLemma33FiniteRow_two, by simp, ?_, ?_⟩
      · norm_num [dusartLemma33FiniteRow_two]
        exact le_of_not_gt hsmall
      · norm_num [dusartLemma33FiniteRow_two]
        linarith
    · by_cases hthree : x < 4
      · refine ⟨dusartLemma33FiniteRow_three, by simp, ?_, ?_⟩
        · norm_num [dusartLemma33FiniteRow_three]
          exact le_of_not_gt htwo
        · norm_num [dusartLemma33FiniteRow_three]
          linarith
      · by_cases hfour : x < 5
        · refine ⟨dusartLemma33FiniteRow_four, by simp, ?_, ?_⟩
          · norm_num [dusartLemma33FiniteRow_four]
            exact le_of_not_gt hthree
          · norm_num [dusartLemma33FiniteRow_four]
            linarith
        · by_cases hfive : x < 6
          · refine ⟨dusartLemma33FiniteRow_five, by simp, ?_, ?_⟩
            · norm_num [dusartLemma33FiniteRow_five]
              exact le_of_not_gt hfour
            · have hright : x < 6 := by linarith
              convert hright using 1 <;>
                norm_num [dusartLemma33FiniteRow_five,
                  dusartLemma33FiniteRow_of_zero]
          · by_cases hsix : x < 7
            · refine ⟨dusartLemma33FiniteRow_six, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_six]
                exact le_of_not_gt hfive
              · have hright : x < 7 := by linarith
                convert hright using 1 <;>
                  norm_num [dusartLemma33FiniteRow_six,
                    dusartLemma33FiniteRow_of_zero]
            · refine ⟨dusartLemma33FiniteRow_seven, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_seven]
                exact le_of_not_gt hsix
              · have hright : x < 8 := by linarith
                convert hright using 1 <;>
                  norm_num [dusartLemma33FiniteRow_seven,
                    dusartLemma33FiniteRow_of_zero]

def dusartLemma33FiniteRow_eight : DusartLemma33FiniteRow :=
  { left := 8
    right := 8
    left_le_right := by norm_num
    valid := by
      intro x hx hleft hright
      have hx8 : (8 : Real) ≤ x := by exact_mod_cast hleft
      have hx9 : x < 9 := by norm_num at hright ⊢; exact hright
      have hfloor : ⌊x⌋₊ = 8 := by
        apply (Nat.floor_eq_iff (by linarith : (0 : Real) ≤ x)).2
        constructor <;> norm_num <;> linarith
      have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 8
      have htheta := Chebyshev.theta_eq_sum_primesLE_log 8
      have htheta_two := Chebyshev.theta_eq_sum_primesLE_log 2
      have hp8 : Nat.primesLE 8 = {2, 3, 5, 7} := by decide
      have hp2 : Nat.primesLE 2 = {2} := by decide
      rw [hp8] at hpsi htheta
      rw [hp2] at htheta_two
      norm_num [Nat.log, Nat.log.go] at hpsi htheta htheta_two
      have hsqrt_lower : (2 : Real) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      have hsqrt_upper : Real.sqrt x < 3 := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      have hsqrt_floor : ⌊Real.sqrt x⌋₊ = 2 := by
        apply (Nat.floor_eq_iff (by positivity : (0 : Real) ≤ Real.sqrt x)).2
        constructor <;> norm_num <;> linarith
      rw [Chebyshev.psi_eq_psi_coe_floor,
        Chebyshev.theta_eq_theta_coe_floor, hfloor]
      have htheta_sqrt_floor : Chebyshev.theta (Real.sqrt x) =
          Chebyshev.theta (2 : Real) := by
        rw [Chebyshev.theta_eq_theta_coe_floor, hsqrt_floor]
        norm_num
      rw [htheta_sqrt_floor]
      norm_num
      have hvalue : Chebyshev.psi (8 : Real) - Chebyshev.theta 8 -
          Chebyshev.theta 2 < 1 := by
        nlinarith [hpsi, htheta, htheta_two, Real.log_two_lt_d9]
      have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
        hx8 (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at hpow ⊢
      nlinarith [hvalue] }

theorem dusartLemma33FiniteRowsCover_eight :
    DusartLemma33FiniteRowsCover
      [dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight] 8 := by
  intro x hx hX
  by_cases hsmall : x < 2
  · refine ⟨dusartLemma33FiniteRow_zero_one, by simp, ?_, ?_⟩
    · norm_num [dusartLemma33FiniteRow_zero_one]
      exact hx.le
    · norm_num [dusartLemma33FiniteRow_zero_one]
      linarith
  · by_cases htwo : x < 3
    · refine ⟨dusartLemma33FiniteRow_two, by simp, ?_, ?_⟩
      · norm_num [dusartLemma33FiniteRow_two]
        exact le_of_not_gt hsmall
      · norm_num [dusartLemma33FiniteRow_two]
        linarith
    · by_cases hthree : x < 4
      · refine ⟨dusartLemma33FiniteRow_three, by simp, ?_, ?_⟩
        · norm_num [dusartLemma33FiniteRow_three]
          exact le_of_not_gt htwo
        · norm_num [dusartLemma33FiniteRow_three]
          linarith
      · by_cases hfour : x < 5
        · refine ⟨dusartLemma33FiniteRow_four, by simp, ?_, ?_⟩
          · norm_num [dusartLemma33FiniteRow_four]
            exact le_of_not_gt hthree
          · norm_num [dusartLemma33FiniteRow_four]
            linarith
        · by_cases hfive : x < 6
          · refine ⟨dusartLemma33FiniteRow_five, by simp, ?_, ?_⟩
            · norm_num [dusartLemma33FiniteRow_five]
              exact le_of_not_gt hfour
            · have hright : x < 6 := by linarith
              convert hright using 1 <;>
                norm_num [dusartLemma33FiniteRow_five,
                  dusartLemma33FiniteRow_of_zero]
          · by_cases hsix : x < 7
            · refine ⟨dusartLemma33FiniteRow_six, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_six]
                exact le_of_not_gt hfive
              · have hright : x < 7 := by linarith
                convert hright using 1 <;>
                  norm_num [dusartLemma33FiniteRow_six,
                    dusartLemma33FiniteRow_of_zero]
            · by_cases hseven : x < 8
              · refine ⟨dusartLemma33FiniteRow_seven, by simp, ?_, ?_⟩
                · norm_num [dusartLemma33FiniteRow_seven]
                  exact le_of_not_gt hsix
                · have hright : x < 8 := by linarith
                  convert hright using 1 <;>
                    norm_num [dusartLemma33FiniteRow_seven,
                      dusartLemma33FiniteRow_of_zero]
              · refine ⟨dusartLemma33FiniteRow_eight, by simp, ?_, ?_⟩
                · norm_num [dusartLemma33FiniteRow_eight]
                  exact le_of_not_gt hseven
                · have hright : x < 9 := by linarith
                  convert hright using 1 <;>
                    norm_num [dusartLemma33FiniteRow_eight,
                      dusartLemma33FiniteRow_of_zero]

def dusartLemma33FiniteRow_nine : DusartLemma33FiniteRow :=
  { left := 9
    right := 9
    left_le_right := by norm_num
    valid := by
      intro x hx hleft hright
      have hx9 : (9 : Real) ≤ x := by exact_mod_cast hleft
      have hx10 : x < 10 := by norm_num at hright ⊢; exact hright
      have hfloor : ⌊x⌋₊ = 9 := by
        apply (Nat.floor_eq_iff (by linarith : (0 : Real) ≤ x)).2
        constructor <;> norm_num <;> linarith
      have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 9
      have htheta := Chebyshev.theta_eq_sum_primesLE_log 9
      have htheta_three := Chebyshev.theta_eq_sum_primesLE_log 3
      have hp9 : Nat.primesLE 9 = {2, 3, 5, 7} := by decide
      have hp3 : Nat.primesLE 3 = {2, 3} := by decide
      rw [hp9] at hpsi htheta
      rw [hp3] at htheta_three
      norm_num [Nat.log, Nat.log.go] at hpsi htheta htheta_three
      have hsqrt_lower : (3 : Real) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      have hsqrt_upper : Real.sqrt x < 4 := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      have hsqrt_floor : ⌊Real.sqrt x⌋₊ = 3 := by
        apply (Nat.floor_eq_iff (by positivity : (0 : Real) ≤ Real.sqrt x)).2
        constructor <;> norm_num <;> linarith
      rw [Chebyshev.psi_eq_psi_coe_floor,
        Chebyshev.theta_eq_theta_coe_floor, hfloor]
      have htheta_sqrt_floor : Chebyshev.theta (Real.sqrt x) =
          Chebyshev.theta (3 : Real) := by
        rw [Chebyshev.theta_eq_theta_coe_floor, hsqrt_floor]
        norm_num
      rw [htheta_sqrt_floor]
      norm_num
      have hvalue : Chebyshev.psi (9 : Real) - Chebyshev.theta 9 -
          Chebyshev.theta 3 < 1 := by
        nlinarith [hpsi, htheta, htheta_three, Real.log_two_lt_d9]
      have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
        (by linarith : (8 : Real) ≤ x)
        (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at hpow ⊢
      nlinarith [hvalue] }

theorem dusartLemma33FiniteRowsCover_nine :
    DusartLemma33FiniteRowsCover
      [dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
        dusartLemma33FiniteRow_nine] 9 := by
  intro x hx hX
  by_cases hsmall : x < 2
  · refine ⟨dusartLemma33FiniteRow_zero_one, by simp, ?_, ?_⟩
    · norm_num [dusartLemma33FiniteRow_zero_one]
      exact hx.le
    · norm_num [dusartLemma33FiniteRow_zero_one]
      linarith
  · by_cases htwo : x < 3
    · refine ⟨dusartLemma33FiniteRow_two, by simp, ?_, ?_⟩
      · norm_num [dusartLemma33FiniteRow_two]
        exact le_of_not_gt hsmall
      · norm_num [dusartLemma33FiniteRow_two]
        linarith
    · by_cases hthree : x < 4
      · refine ⟨dusartLemma33FiniteRow_three, by simp, ?_, ?_⟩
        · norm_num [dusartLemma33FiniteRow_three]
          exact le_of_not_gt htwo
        · norm_num [dusartLemma33FiniteRow_three]
          linarith
      · by_cases hfour : x < 5
        · refine ⟨dusartLemma33FiniteRow_four, by simp, ?_, ?_⟩
          · norm_num [dusartLemma33FiniteRow_four]
            exact le_of_not_gt hthree
          · norm_num [dusartLemma33FiniteRow_four]
            linarith
        · by_cases hfive : x < 6
          · refine ⟨dusartLemma33FiniteRow_five, by simp, ?_, ?_⟩
            · norm_num [dusartLemma33FiniteRow_five]
              exact le_of_not_gt hfour
            · have hright : x < 6 := by linarith
              convert hright using 1 <;>
                norm_num [dusartLemma33FiniteRow_five,
                  dusartLemma33FiniteRow_of_zero]
          · by_cases hsix : x < 7
            · refine ⟨dusartLemma33FiniteRow_six, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_six]
                exact le_of_not_gt hfive
              · have hright : x < 7 := by linarith
                convert hright using 1 <;>
                  norm_num [dusartLemma33FiniteRow_six,
                    dusartLemma33FiniteRow_of_zero]
            · by_cases hseven : x < 8
              · refine ⟨dusartLemma33FiniteRow_seven, by simp, ?_, ?_⟩
                · norm_num [dusartLemma33FiniteRow_seven]
                  exact le_of_not_gt hsix
                · have hright : x < 8 := by linarith
                  convert hright using 1 <;>
                    norm_num [dusartLemma33FiniteRow_seven,
                      dusartLemma33FiniteRow_of_zero]
              · by_cases height : x < 9
                · refine ⟨dusartLemma33FiniteRow_eight, by simp, ?_, ?_⟩
                  · norm_num [dusartLemma33FiniteRow_eight]
                    exact le_of_not_gt hseven
                  · have hright : x < 9 := by linarith
                    convert hright using 1 <;>
                      norm_num [dusartLemma33FiniteRow_eight,
                        dusartLemma33FiniteRow_of_zero]
                · refine ⟨dusartLemma33FiniteRow_nine, by simp, ?_, ?_⟩
                  · norm_num [dusartLemma33FiniteRow_nine]
                    exact le_of_not_gt height
                  · have hright : x < 10 := by linarith
                    convert hright using 1 <;>
                      norm_num [dusartLemma33FiniteRow_nine,
                        dusartLemma33FiniteRow_of_zero]

theorem dusart_lemma_3_3_finite_of_rows
    {rows : List DusartLemma33FiniteRow} {X : Real}
    (cover : DusartLemma33FiniteRowsCover rows X) :
    ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  exact row.valid x hx hleft hright

/-! Indexed assembly is the compact counterpart of the list assembler.  It
allows a generated bounded computation to expose one row function and one
cover proof without expanding the computation into a declaration per band. -/
def DusartLemma33FiniteRowsIndexedCover
  {n : Nat} (rows : Fin n → DusartLemma33FiniteRow) (X : Real) : Prop :=
  ∀ x : Real, 0 < x → x ≤ X →
    ∃ i : Fin n, ((rows i).left : Real) ≤ x ∧
      x < (rows i).right + 1

theorem dusart_lemma_3_3_finite_of_indexed_rows
    {n : Nat} {rows : Fin n → DusartLemma33FiniteRow} {X : Real}
    (cover : DusartLemma33FiniteRowsIndexedCover rows X) :
    ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  intro x hx hX
  obtain ⟨i, hleft, hright⟩ := cover x hx hX
  exact (rows i).valid x hx hleft hright

/-! List-to-indexed conversion for generated bounded tables.  This preserves
the strict right-endpoint convention used by the real-valued cover. -/
theorem dusartLemma33FiniteRowsIndexedCover_of_list
    {rows : List DusartLemma33FiniteRow} {X : Real}
    (cover : DusartLemma33FiniteRowsCover rows X) :
    DusartLemma33FiniteRowsIndexedCover
      (fun i : Fin rows.length => rows.get i) X := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hrow
  refine ⟨⟨i, hi⟩, ?_, ?_⟩
  · simpa [List.get_eq_getElem, hget] using hleft
  · simpa [List.get_eq_getElem, hget] using hright

theorem dusartLemma33FiniteRowsIndexedCover_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → DusartLemma33FiniteRow}
    {right : Fin n₂ → DusartLemma33FiniteRow}
    (hleft : DusartLemma33FiniteRowsIndexedCover left m)
    (hright : DusartLemma33FiniteRowsIndexedCover right X) :
    DusartLemma33FiniteRowsIndexedCover (Fin.append left right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨i, hleft_lower, hleft_upper⟩ := hleft x hx hxm
    refine ⟨Fin.castAdd n₂ i, ?_, ?_⟩
    · simpa [Fin.append_left] using hleft_lower
    · simpa [Fin.append_left] using hleft_upper
  · obtain ⟨i, hright_lower, hright_upper⟩ := hright x hx hX
    refine ⟨Fin.natAdd n₁ i, ?_, ?_⟩
    · simpa [Fin.append_right] using hright_lower
    · simpa [Fin.append_right] using hright_upper

/-! A bounded computation is assembled from reusable indexed chunks.  The
    chunk stores one row function and one coverage proof; concatenation keeps
    the kernel-facing representation independent of the number of generated
    witness declarations. -/
structure DusartLemma33FiniteChunk where
  n : Nat
  cutoff : Real
  rows : Fin n → DusartLemma33FiniteRow
  cover : DusartLemma33FiniteRowsIndexedCover rows cutoff

def DusartLemma33FiniteChunk.of_list
    {rows : List DusartLemma33FiniteRow} {cutoff : Real}
    (cover : DusartLemma33FiniteRowsCover rows cutoff) :
    DusartLemma33FiniteChunk :=
  { n := rows.length
    cutoff := cutoff
    rows := fun i => rows.get i
    cover := dusartLemma33FiniteRowsIndexedCover_of_list cover }

theorem DusartLemma33FiniteChunk.provides
    (chunk : DusartLemma33FiniteChunk) :
    ∀ x : Real, 0 < x → x ≤ chunk.cutoff →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact dusart_lemma_3_3_finite_of_indexed_rows chunk.cover

def DusartLemma33FiniteChunk.append
    (left right : DusartLemma33FiniteChunk) : DusartLemma33FiniteChunk :=
  { n := left.n + right.n
    cutoff := right.cutoff
    rows := Fin.append left.rows right.rows
    cover := dusartLemma33FiniteRowsIndexedCover_append
      left.cover right.cover }

/-! A generated block may also expose its already assembled interval proof
    directly.  This keeps the data representation independent of the number
    of internal rows while retaining a composable cutoff boundary. -/
structure DusartLemma33FiniteProofChunk where
  cutoff : Real
  valid : ∀ x : Real, 0 < x → x ≤ cutoff →
    Chebyshev.psi x - Chebyshev.theta x -
        Chebyshev.theta (Real.sqrt x) <
      (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real))

def DusartLemma33FiniteChunk.toProofChunk
    (chunk : DusartLemma33FiniteChunk) : DusartLemma33FiniteProofChunk :=
  { cutoff := chunk.cutoff
    valid := chunk.provides }

def DusartLemma33FiniteProofChunk.append
    (left right : DusartLemma33FiniteProofChunk) :
    DusartLemma33FiniteProofChunk := by
  refine { cutoff := right.cutoff, valid := ?_ }
  intro x hx hX
  by_cases hxm : x ≤ left.cutoff
  · exact left.valid x hx hxm
  · exact right.valid x hx hX

def DusartLemma33FiniteProofChunk.appendMany
    (first : DusartLemma33FiniteProofChunk)
    (rest : List DusartLemma33FiniteProofChunk) :
    DusartLemma33FiniteProofChunk :=
  match rest with
  | [] => first
  | next :: tail =>
      DusartLemma33FiniteProofChunk.appendMany
        (DusartLemma33FiniteProofChunk.append first next) tail

theorem DusartLemma33FiniteProofChunk.appendMany_valid
    (first : DusartLemma33FiniteProofChunk)
    (rest : List DusartLemma33FiniteProofChunk) :
    ∀ x : Real, 0 < x → x ≤
      (DusartLemma33FiniteProofChunk.appendMany first rest).cutoff →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  induction rest generalizing first with
  | nil =>
      exact first.valid
  | cons next tail ih =>
      exact ih (DusartLemma33FiniteProofChunk.append first next)

theorem dusart_lemma_3_3_finite_of_proof_chunks
    (first : DusartLemma33FiniteProofChunk)
    (rest : List DusartLemma33FiniteProofChunk) :
    ∀ x : Real, 0 < x → x ≤
      (DusartLemma33FiniteProofChunk.appendMany first rest).cutoff →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  exact DusartLemma33FiniteProofChunk.appendMany_valid first rest

theorem dusart_lemma_3_3_finite_rows_cover_append
    {left right : List DusartLemma33FiniteRow} {m X : Real}
    (hleft : DusartLemma33FiniteRowsCover left m)
    (hright : DusartLemma33FiniteRowsCover right X) :
    DusartLemma33FiniteRowsCover (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ :=
      hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem dusart_lemma_3_3_finite_rows_cover_append_on
    {left right : List DusartLemma33FiniteRow} {m lower X : Real}
    (hleft : DusartLemma33FiniteRowsCover left m)
    (hright : DusartLemma33FiniteRowsCoverOn right lower X)
    (hm : lower ≤ m) :
    DusartLemma33FiniteRowsCover (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hright_row_left, hright_row_right⟩ :=
      hright x (le_trans hm (le_of_not_ge hxm)) hX
    exact ⟨row, by simp [hrow], hright_row_left, hright_row_right⟩

theorem dusartLemma33FiniteRowsCover_append_row
    {rows : List DusartLemma33FiniteRow} {row : DusartLemma33FiniteRow}
    {m X : Real}
    (cover : DusartLemma33FiniteRowsCover rows m)
    (hrow : ∀ x : Real, m < x → 0 < x → x ≤ X →
      (row.left : Real) ≤ x ∧ x < (row.right : Real) + 1) :
    DusartLemma33FiniteRowsCover (rows ++ [row]) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨old, hold, hleft, hright⟩ := cover x hx hxm
    exact ⟨old, by simp [hold], hleft, hright⟩
  · obtain ⟨hleft, hright⟩ := hrow x (lt_of_not_ge hxm) hx hX
    exact ⟨row, by simp, hleft, hright⟩

end

end PrimeFactorUnimodality
