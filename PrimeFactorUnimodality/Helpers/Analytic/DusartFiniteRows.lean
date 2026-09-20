import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! Compact bounded rows for the direct-computation part of Dusart's Lemma 3.3.

The row validity field is the only place where a bounded numerical proof is
stored.  Coverage and assembly are independent of the eventual row data, so
the finite computation can be split into stable, cacheable chunks. -/
structure DusartLemma33FiniteRow where
  left : Nat
  right : Nat
  left_le_right : left ≤ right
  valid : ∀ x : Real, 0 < x → (left : Real) ≤ x →
    x < (right : Real) + 1 →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real))

def DusartLemma33FiniteRowsCover
    (rows : List DusartLemma33FiniteRow) (X : Real) : Prop :=
  ∀ x : Real, 0 < x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧
      x < (row.right : Real) + 1

def dusartLemma33FiniteRow_of_zero
    (n m : Nat)
    (hsqrt_floor : ∀ x : Real, 0 < x → (n : Real) ≤ x →
      x < (n : Real) + 1 → ⌊Real.sqrt x⌋₊ = m)
    (hzero : Chebyshev.psi (n : Real) - Chebyshev.theta n -
      Chebyshev.theta m = 0) : DusartLemma33FiniteRow :=
  { left := n
    right := n
    left_le_right := by rfl
    valid := by
      intro x hx hleft hright
      have hfloor : ⌊x⌋₊ = n := by
        apply (Nat.floor_eq_iff (by linarith : (0 : Real) ≤ x)).2
        constructor
        · exact hleft
        · simpa using hright
      have hpsi_floor := Chebyshev.psi_eq_psi_coe_floor x
      have htheta_floor := Chebyshev.theta_eq_theta_coe_floor x
      rw [hpsi_floor, htheta_floor, hfloor]
      have htheta_sqrt_floor : Chebyshev.theta (Real.sqrt x) =
          Chebyshev.theta (m : Real) := by
        rw [Chebyshev.theta_eq_theta_coe_floor,
          hsqrt_floor x hx hleft hright]
      rw [htheta_sqrt_floor]
      have hzero' : Chebyshev.psi (↑n : Real) - Chebyshev.theta (↑n : Real) -
          Chebyshev.theta (↑m : Real) = 0 := by
        simpa using hzero
      rw [hzero']
      norm_num
      positivity }

def dusartLemma33FiniteRow_zero_one : DusartLemma33FiniteRow :=
  { left := 0
    right := 1
    left_le_right := by norm_num
    valid := by
      intro x hx _ hright
      have hx2 : x < 2 := by norm_num at hright ⊢; exact hright
      have hsqrt : Real.sqrt x < 2 := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      rw [Chebyshev.psi_eq_zero_of_lt_two hx2,
        Chebyshev.theta_eq_zero_of_lt_two hx2,
        Chebyshev.theta_eq_zero_of_lt_two hsqrt]
      norm_num
      positivity }

theorem dusartLemma33FiniteRow_zero_one_cover :
    DusartLemma33FiniteRowsCover [dusartLemma33FiniteRow_zero_one] 1 := by
  intro x hx hX
  refine ⟨dusartLemma33FiniteRow_zero_one, by simp, ?_, ?_⟩
  · simpa [dusartLemma33FiniteRow_zero_one] using hx.le
  · norm_num [dusartLemma33FiniteRow_zero_one]
    linarith

def dusartLemma33FiniteRow_two : DusartLemma33FiniteRow :=
  { left := 2
    right := 2
    left_le_right := by norm_num
    valid := by
      intro x hx hleft hright
      have hx2 : (2 : Real) ≤ x := by exact_mod_cast hleft
      have hx3 : x < 3 := by norm_num at hright ⊢; exact hright
      have hfloor : ⌊x⌋₊ = 2 := by
        apply (Nat.floor_eq_iff (by linarith : (0 : Real) ≤ x)).2
        constructor <;> norm_num <;> linarith
      have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 2
      have htheta := Chebyshev.theta_eq_sum_primesLE_log 2
      have hp : Nat.primesLE 2 = {2} := by decide
      rw [hp] at hpsi htheta
      norm_num [Nat.log, Nat.log.go] at hpsi htheta
      have hzero : Chebyshev.psi (2 : Real) - Chebyshev.theta 2 = 0 := by
        nlinarith [hpsi, htheta]
      have hsqrt : Real.sqrt x < 2 := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      rw [Chebyshev.psi_eq_psi_coe_floor,
        Chebyshev.theta_eq_theta_coe_floor, hfloor]
      have hzero' : Chebyshev.psi (↑(2 : Nat) : Real) -
          Chebyshev.theta (↑(2 : Nat) : Real) = 0 := by
        simpa using hzero
      rw [hzero',
        Chebyshev.theta_eq_zero_of_lt_two hsqrt]
      norm_num
      positivity }

theorem dusartLemma33FiniteRowsCover_two :
    DusartLemma33FiniteRowsCover
      [dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two] 2 := by
  intro x hx hX
  by_cases hsmall : x < 2
  · refine ⟨dusartLemma33FiniteRow_zero_one, by simp, ?_, ?_⟩
    · norm_num [dusartLemma33FiniteRow_zero_one]
      exact hx.le
    · norm_num [dusartLemma33FiniteRow_zero_one]
      linarith
  · refine ⟨dusartLemma33FiniteRow_two, by simp, ?_, ?_⟩
    · norm_num [dusartLemma33FiniteRow_two]
      exact le_of_not_gt hsmall
    · norm_num [dusartLemma33FiniteRow_two]
      linarith

def dusartLemma33FiniteRow_three : DusartLemma33FiniteRow :=
  { left := 3
    right := 3
    left_le_right := by norm_num
    valid := by
      intro x hx hleft hright
      have hx3 : (3 : Real) ≤ x := by exact_mod_cast hleft
      have hx4 : x < 4 := by norm_num at hright ⊢; exact hright
      have hfloor : ⌊x⌋₊ = 3 := by
        apply (Nat.floor_eq_iff (by linarith : (0 : Real) ≤ x)).2
        constructor <;> norm_num <;> linarith
      have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 3
      have htheta := Chebyshev.theta_eq_sum_primesLE_log 3
      have hp : Nat.primesLE 3 = {2, 3} := by decide
      rw [hp] at hpsi htheta
      norm_num [Nat.log, Nat.log.go] at hpsi htheta
      have hzero : Chebyshev.psi (3 : Real) - Chebyshev.theta 3 = 0 := by
        nlinarith [hpsi, htheta]
      have hsqrt : Real.sqrt x < 2 := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      rw [Chebyshev.psi_eq_psi_coe_floor,
        Chebyshev.theta_eq_theta_coe_floor, hfloor]
      have hzero' : Chebyshev.psi (↑(3 : Nat) : Real) -
          Chebyshev.theta (↑(3 : Nat) : Real) = 0 := by
        simpa using hzero
      rw [hzero', Chebyshev.theta_eq_zero_of_lt_two hsqrt]
      norm_num
      positivity }

theorem dusartLemma33FiniteRowsCover_three :
    DusartLemma33FiniteRowsCover
      [dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three] 3 := by
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
    · refine ⟨dusartLemma33FiniteRow_three, by simp, ?_, ?_⟩
      · norm_num [dusartLemma33FiniteRow_three]
        exact le_of_not_gt htwo
      · norm_num [dusartLemma33FiniteRow_three]
        linarith

def dusartLemma33FiniteRow_four : DusartLemma33FiniteRow :=
  { left := 4
    right := 4
    left_le_right := by norm_num
    valid := by
      intro x hx hleft hright
      have hx4 : (4 : Real) ≤ x := by exact_mod_cast hleft
      have hx5 : x < 5 := by norm_num at hright ⊢; exact hright
      have hfloor : ⌊x⌋₊ = 4 := by
        apply (Nat.floor_eq_iff (by linarith : (0 : Real) ≤ x)).2
        constructor <;> norm_num <;> linarith
      have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 4
      have htheta := Chebyshev.theta_eq_sum_primesLE_log 4
      have htheta_two := Chebyshev.theta_eq_sum_primesLE_log 2
      have hp4 : Nat.primesLE 4 = {2, 3} := by decide
      have hp2 : Nat.primesLE 2 = {2} := by decide
      rw [hp4] at hpsi htheta
      rw [hp2] at htheta_two
      norm_num [Nat.log, Nat.log.go] at hpsi htheta htheta_two
      have hzero : Chebyshev.psi (4 : Real) - Chebyshev.theta 4 -
          Chebyshev.theta 2 = 0 := by
        nlinarith [hpsi, htheta, htheta_two]
      have hsqrt_lower : (2 : Real) ≤ Real.sqrt x := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      have hsqrt_upper : Real.sqrt x < 3 := by
        nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
      have hsqrt_floor : ⌊Real.sqrt x⌋₊ = 2 := by
        apply (Nat.floor_eq_iff (by positivity : (0 : Real) ≤ Real.sqrt x)).2
        constructor <;> norm_num <;> linarith
      have hpsi_floor := Chebyshev.psi_eq_psi_coe_floor x
      have htheta_floor := Chebyshev.theta_eq_theta_coe_floor x
      rw [hpsi_floor, htheta_floor, hfloor]
      have htheta_sqrt_floor : Chebyshev.theta (Real.sqrt x) =
          Chebyshev.theta (2 : Real) := by
        rw [Chebyshev.theta_eq_theta_coe_floor, hsqrt_floor]
      rw [htheta_sqrt_floor]
      have hzero' : Chebyshev.psi (↑(4 : Nat) : Real) -
          Chebyshev.theta (↑(4 : Nat) : Real) -
            Chebyshev.theta (↑(2 : Nat) : Real) = 0 := by
        simpa using hzero
      rw [hzero']
      norm_num
      positivity }

theorem dusartLemma33FiniteRowsCover_four :
    DusartLemma33FiniteRowsCover
      [dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four] 4 := by
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
      · refine ⟨dusartLemma33FiniteRow_four, by simp, ?_, ?_⟩
        · norm_num [dusartLemma33FiniteRow_four]
          exact le_of_not_gt hthree
        · norm_num [dusartLemma33FiniteRow_four]
          linarith

def dusartLemma33FiniteRow_five : DusartLemma33FiniteRow := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 5
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 5
  have htheta_two := Chebyshev.theta_eq_sum_primesLE_log 2
  have hp5 : Nat.primesLE 5 = {2, 3, 5} := by decide
  have hp2 : Nat.primesLE 2 = {2} := by decide
  rw [hp5] at hpsi htheta
  rw [hp2] at htheta_two
  norm_num [Nat.log, Nat.log.go] at hpsi htheta htheta_two
  apply dusartLemma33FiniteRow_of_zero 5 2
  · intro x hx hleft hright
    have hx5 : (5 : Real) ≤ x := hleft
    have hx6 : x < 6 := by simpa using hright
    apply (Nat.floor_eq_iff (by positivity : (0 : Real) ≤ Real.sqrt x)).2
    constructor <;> norm_num <;>
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · nlinarith [hpsi, htheta, htheta_two]

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
          · norm_num [dusartLemma33FiniteRow_five]
            linarith

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
    have hx7 : x < 7 := by simpa using hright
    apply (Nat.floor_eq_iff (by positivity : (0 : Real) ≤ Real.sqrt x)).2
    constructor <;> norm_num <;>
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · nlinarith [hpsi, htheta, htheta_two]

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
    have hx8 : x < 8 := by simpa using hright
    apply (Nat.floor_eq_iff (by positivity : (0 : Real) ≤ Real.sqrt x)).2
    constructor <;> norm_num <;>
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · nlinarith [hpsi, htheta, htheta_two]

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
            · norm_num [dusartLemma33FiniteRow_five]
              linarith
          · by_cases hsix : x < 7
            · refine ⟨dusartLemma33FiniteRow_six, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_six]
                exact le_of_not_gt hfive
              · norm_num [dusartLemma33FiniteRow_six]
                linarith
            · refine ⟨dusartLemma33FiniteRow_seven, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_seven]
                exact le_of_not_gt hsix
              · norm_num [dusartLemma33FiniteRow_seven]
                linarith

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

end

end PrimeFactorUnimodality
