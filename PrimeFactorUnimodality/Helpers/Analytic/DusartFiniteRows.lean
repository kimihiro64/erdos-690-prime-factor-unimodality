import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

/-! Integer power certificates for the floors appearing in the finite
    Lemma 3.3 endpoint computation. -/
theorem nat_floor_rpow_eq_of_pow_le_pow_lt
    {n k r : Nat} (hk : 0 < k)
    (hlo : r ^ k ≤ n) (hhi : n < (r + 1) ^ k) :
    ⌊(n : Real) ^ (1 / (k : Real))⌋₊ = r := by
  have hn_nonneg : (0 : Real) ≤ n := by positivity
  have hroot_nonneg : 0 ≤ (n : Real) ^ (1 / (k : Real)) := by
    positivity
  have hroot_pow :
      ((n : Real) ^ (1 / (k : Real))) ^ k = (n : Real) := by
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow hn_nonneg (Nat.ne_of_gt hk))
  apply (Nat.floor_eq_iff hroot_nonneg).2
  constructor
  · have hpow : (r : Real) ^ k ≤
        ((n : Real) ^ (1 / (k : Real))) ^ k := by
      calc
        (r : Real) ^ k ≤ (n : Real) := by exact_mod_cast hlo
        _ = ((n : Real) ^ (1 / (k : Real))) ^ k := hroot_pow.symm
    have hpow' : (r : Real) ^ (k : Real) ≤
        ((n : Real) ^ (1 / (k : Real))) ^ (k : Real) := by
      simpa only [Real.rpow_natCast] using hpow
    exact (Real.rpow_le_rpow_iff (by positivity) (by positivity)
      (show (0 : Real) < (k : Real) by exact_mod_cast hk)).mp hpow'
  · have hpow : ((n : Real) ^ (1 / (k : Real))) ^ k <
        ((r + 1 : Nat) : Real) ^ k := by
      calc
        ((n : Real) ^ (1 / (k : Real))) ^ k = (n : Real) := hroot_pow
        _ < ((r + 1 : Nat) : Real) ^ k := by exact_mod_cast hhi
    have hpow' : ((n : Real) ^ (1 / (k : Real))) ^ (k : Real) <
        ((r + 1 : Nat) : Real) ^ (k : Real) := by
      simpa only [Real.rpow_natCast] using hpow
    have hpow'' : ((n : Real) ^ (1 / (k : Real))) ^ (k : Real) <
        ((r : Real) + 1) ^ (k : Real) := by
      convert hpow' using 1 <;> norm_num
    exact (Real.rpow_lt_rpow_iff (by positivity) (by positivity)
      (show (0 : Real) < (k : Real) by exact_mod_cast hk)).mp hpow''

/-! Compact rows for the bounded part of Dusart's Proposition 3.1.  The row
validity field contains the numerical gap proof; coverage and the analytic
tail are assembled separately. -/
structure DusartProposition31FiniteRow where
  left : Nat
  right : Nat
  left_le_right : left ≤ right
  valid : ∀ x : Real, (121 : Real) < x →
    (left : Real) ≤ x → x < (right : Real) + 1 →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x

def dusartProposition31FiniteRow_of_integer_endpoint
    (n : Nat)
    (hvalid : (9999 : Real) / 10000 * Real.sqrt ((n : Real) + 1) <
      Chebyshev.psi (n : Real) - Chebyshev.theta n) :
    DusartProposition31FiniteRow := by
  refine {
    left := n
    right := n
    left_le_right := le_rfl
    valid := ?_ }
  intro x hx hleft hright
  have hfloor : ⌊x⌋₊ = n := by
    apply (Nat.floor_eq_iff (by linarith : (0 : Real) ≤ x)).2
    constructor
    · exact hleft
    · simpa using hright
  have hgap : Chebyshev.psi x - Chebyshev.theta x =
      Chebyshev.psi (n : Real) - Chebyshev.theta n := by
    rw [Chebyshev.psi_eq_psi_coe_floor,
      Chebyshev.theta_eq_theta_coe_floor, hfloor]
  have hsqrt : Real.sqrt x < Real.sqrt ((n : Real) + 1) := by
    have hsqrt_x_nonneg : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hsqrt_n_nonneg : 0 ≤ Real.sqrt ((n : Real) + 1) :=
      Real.sqrt_nonneg _
    have hsquare_x : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
    have hsquare_n : (Real.sqrt ((n : Real) + 1)) ^ 2 = (n : Real) + 1 :=
      Real.sq_sqrt (by positivity)
    by_contra hnot
    have hreverse : Real.sqrt ((n : Real) + 1) ≤ Real.sqrt x :=
      le_of_not_gt hnot
    nlinarith
  rw [hgap]
  have hcoef : (0 : Real) < (9999 : Real) / 10000 := by norm_num
  exact (mul_lt_mul_of_pos_left hsqrt hcoef).trans hvalid

def DusartProposition31FiniteRowsCover
    (rows : List DusartProposition31FiniteRow) (X : Real) : Prop :=
  ∀ x : Real, (121 : Real) < x → x ≤ X →
    ∃ row ∈ rows, (row.left : Real) ≤ x ∧
      x < (row.right : Real) + 1

theorem dusartProposition31Finite_of_integer_endpoint_check
    {X : Real}
    (endpoint : ∀ n : Nat, 121 ≤ n →
      (9999 : Real) / 10000 * Real.sqrt ((n : Real) + 1) <
        Chebyshev.psi (n : Real) - Chebyshev.theta n) :
    ∀ x : Real, (121 : Real) < x → x ≤ X →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x := by
  intro x hx hX
  let n : Nat := ⌊x⌋₊
  have hn121 : 121 ≤ n := by
    dsimp [n]
    exact Nat.le_floor (by simpa using (show (121 : Real) ≤ x by linarith))
  have hn_lower : (n : Real) ≤ x := by
    dsimp [n]
    exact Nat.floor_le (by linarith)
  have hn_upper : x < (n : Real) + 1 := by
    simpa only [n] using Nat.lt_floor_add_one x
  exact (dusartProposition31FiniteRow_of_integer_endpoint
    n (endpoint n hn121)).valid x hx hn_lower (by
      simpa [dusartProposition31FiniteRow_of_integer_endpoint] using hn_upper)

def DusartProposition31FiniteIndexedRowsCover {n : Nat}
    (rows : Fin n → DusartProposition31FiniteRow) (X : Real) : Prop :=
  ∀ x : Real, (121 : Real) < x → x ≤ X →
    ∃ i : Fin n, (rows i).left ≤ x ∧
      x < (rows i).right + 1

theorem dusartProposition31FiniteIndexedRowsCover_of_list
    {X : Real} {rows : List DusartProposition31FiniteRow}
    (cover : DusartProposition31FiniteRowsCover rows X) :
    DusartProposition31FiniteIndexedRowsCover
      (fun i : Fin rows.length => rows.get i) X := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hrow
  refine ⟨⟨i, hi⟩, ?_⟩
  simpa [List.get_eq_getElem, hget] using And.intro hleft hright

theorem dusartProposition31Finite_of_rows
    {X : Real} {rows : List DusartProposition31FiniteRow}
    (cover : DusartProposition31FiniteRowsCover rows X) :
    ∀ x : Real, (121 : Real) < x → x ≤ X →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x := by
  intro x hx hX
  obtain ⟨row, hrow, hleft, hright⟩ := cover x hx hX
  exact row.valid x hx hleft hright

theorem dusartProposition31Finite_of_indexed_rows
    {n : Nat} {X : Real}
    {rows : Fin n → DusartProposition31FiniteRow}
    (cover : DusartProposition31FiniteIndexedRowsCover rows X) :
    ∀ x : Real, (121 : Real) < x → x ≤ X →
      (9999 : Real) / 10000 * Real.sqrt x <
        Chebyshev.psi x - Chebyshev.theta x := by
  intro x hx hX
  obtain ⟨i, hleft, hright⟩ := cover x hx hX
  exact (rows i).valid x hx hleft hright

theorem dusartProposition31FiniteRowsCover_append
    {m X : Real} {left right : List DusartProposition31FiniteRow}
    (hleft : DusartProposition31FiniteRowsCover left m)
    (hright : DusartProposition31FiniteRowsCover right X) :
    DusartProposition31FiniteRowsCover (left ++ right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hleft x hx hxm
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩
  · obtain ⟨row, hrow, hleft_row, hright_row⟩ := hright x hx hX
    exact ⟨row, by simp [hrow], hleft_row, hright_row⟩

theorem dusartProposition31FiniteIndexedRowsCover_append
    {m X : Real} {n₁ n₂ : Nat}
    {left : Fin n₁ → DusartProposition31FiniteRow}
    {right : Fin n₂ → DusartProposition31FiniteRow}
    (hleft : DusartProposition31FiniteIndexedRowsCover left m)
    (hright : DusartProposition31FiniteIndexedRowsCover right X) :
    DusartProposition31FiniteIndexedRowsCover (Fin.append left right) X := by
  intro x hx hX
  by_cases hxm : x ≤ m
  · obtain ⟨i, hleft_lower, hleft_upper⟩ := hleft x hx hxm
    refine ⟨Fin.castAdd n₂ i, ?_⟩
    simpa [Fin.append_left] using And.intro hleft_lower hleft_upper
  · obtain ⟨i, hright_lower, hright_upper⟩ := hright x hx hX
    refine ⟨Fin.natAdd n₁ i, ?_⟩
    simpa [Fin.append_right] using And.intro hright_lower hright_upper

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

/-! A nonzero endpoint check controls the whole half-open unit interval.  This
is the reduction used by the bounded computation: the two Chebyshev terms at
`x` are constant on `[n,n+1)`, while the square-root term only increases and
the target power is monotone. -/
def dusartLemma33FiniteRow_of_integer_endpoint
    (n : Nat)
    (hvalid : Chebyshev.psi (n : Real) - Chebyshev.theta n -
        Chebyshev.theta (Real.sqrt n) <
      (1777745 : Real) / 1000000 * (n : Real) ^ (1 / (3 : Real))) :
    DusartLemma33FiniteRow := by
  refine {
    left := n
    right := n
    left_le_right := by rfl
    valid := ?_ }
  intro x hx hleft hright
  have hn_le_x : (n : Real) ≤ x := hleft
  have hfloor : ⌊x⌋₊ = n := by
    apply (Nat.floor_eq_iff (by linarith : (0 : Real) ≤ x)).2
    constructor
    · exact hleft
    · simpa using hright
  have hpsi_floor := Chebyshev.psi_eq_psi_coe_floor x
  have htheta_floor := Chebyshev.theta_eq_theta_coe_floor x
  rw [hpsi_floor, htheta_floor, hfloor]
  have hsqrt : Real.sqrt (n : Real) ≤ Real.sqrt x := by
    exact Real.sqrt_le_sqrt hn_le_x
  have htheta_sqrt : Chebyshev.theta (Real.sqrt (n : Real)) ≤
      Chebyshev.theta (Real.sqrt x) := Chebyshev.theta_mono hsqrt
  have hleft_value : Chebyshev.psi (n : Real) - Chebyshev.theta (n : Real) -
      Chebyshev.theta (Real.sqrt x) ≤
      Chebyshev.psi (n : Real) - Chebyshev.theta (n : Real) -
        Chebyshev.theta (Real.sqrt (n : Real)) := by
    linarith
  have hrpow : (n : Real) ^ (1 / (3 : Real)) ≤
      x ^ (1 / (3 : Real)) := by
    exact Real.rpow_le_rpow (by positivity) hn_le_x (by norm_num)
  calc
    Chebyshev.psi (n : Real) - Chebyshev.theta (n : Real) -
        Chebyshev.theta (Real.sqrt x) ≤
      Chebyshev.psi (n : Real) - Chebyshev.theta (n : Real) -
        Chebyshev.theta (Real.sqrt (n : Real)) := hleft_value
    _ < (1777745 : Real) / 1000000 * (n : Real) ^ (1 / (3 : Real)) := hvalid
    _ ≤ (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
      exact mul_le_mul_of_nonneg_left hrpow (by norm_num)

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

theorem dusart_lemma_3_3_finite_of_integer_endpoints
    {X : Real}
    (endpoint : ∀ n : Nat, 1 ≤ n → (n : Real) ≤ X →
      Chebyshev.psi (n : Real) - Chebyshev.theta n -
          Chebyshev.theta (Real.sqrt n) <
        (1777745 : Real) / 1000000 * (n : Real) ^ (1 / (3 : Real))) :
    ∀ x : Real, 0 < x → x ≤ X →
      Chebyshev.psi x - Chebyshev.theta x -
          Chebyshev.theta (Real.sqrt x) <
        (1777745 : Real) / 1000000 * x ^ (1 / (3 : Real)) := by
  intro x hx hX
  by_cases hx1 : x < 1
  · exact dusartLemma33FiniteRow_zero_one.valid x hx
      (by simpa [dusartLemma33FiniteRow_zero_one] using hx.le)
      (by norm_num; linarith)
  · let n : Nat := ⌊x⌋₊
    have hx1' : (1 : Real) ≤ x := le_of_not_gt hx1
    have hn_one : 1 ≤ n := by
      dsimp [n]
      exact Nat.le_floor (by simpa using hx1')
    have hn_lower : (n : Real) ≤ x := by
      dsimp [n]
      exact Nat.floor_le hx.le
    have hn_upper : x < (n : Real) + 1 := by
      simpa only [n] using Nat.lt_floor_add_one x
    have hn_X : (n : Real) ≤ X := hn_lower.trans hX
    have hend := endpoint n hn_one hn_X
    exact (dusartLemma33FiniteRow_of_integer_endpoint n hend).valid x hx
      hn_lower hn_upper

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
        norm_num
      rw [htheta_sqrt_floor]
      have hzero' : Chebyshev.psi (↑(4 : Nat) : Real) -
          Chebyshev.theta (↑(4 : Nat) : Real) -
            Chebyshev.theta (↑(2 : Nat) : Real) = 0 := by
        simpa using hzero
      have hzero'' : Chebyshev.psi (↑(4 : Nat) : Real) -
          Chebyshev.theta (↑(4 : Nat) : Real) -
            Chebyshev.theta (↑(2 : Nat) : Real) = 0 := by
        simpa using hzero'
      have hzero''' : Chebyshev.psi (↑(4 : Nat) : Real) -
          Chebyshev.theta (↑(4 : Nat) : Real) -
            Chebyshev.theta 2 = 0 := by
        convert hzero'' using 1 <;> norm_num
      rw [hzero''']
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
    have hx6 : x < 6 := by norm_num at hright ⊢; exact hright
    apply (Nat.floor_eq_iff (by positivity : (0 : Real) ≤ Real.sqrt x)).2
    constructor
    · norm_num
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    · norm_num
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · ring_nf at hpsi htheta htheta_two ⊢
    linarith [hpsi, htheta, htheta_two]

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
          · simpa [dusartLemma33FiniteRow_five] using (show x < 6 by linarith)

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
            · simpa [dusartLemma33FiniteRow_five,
                dusartLemma33FiniteRow_of_zero] using (show x < 6 by linarith)
          · by_cases hsix : x < 7
            · refine ⟨dusartLemma33FiniteRow_six, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_six]
                exact le_of_not_gt hfive
              · simpa [dusartLemma33FiniteRow_six,
                  dusartLemma33FiniteRow_of_zero] using (show x < 7 by linarith)
            · refine ⟨dusartLemma33FiniteRow_seven, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_seven]
                exact le_of_not_gt hsix
              · change x < 8
                linarith

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
      rw [Chebyshev.theta_eq_theta_coe_floor, hsqrt_floor]
      have hvalue : Chebyshev.psi (8 : Real) - Chebyshev.theta 8 -
          Chebyshev.theta 2 < 1 := by
        nlinarith [hpsi, htheta, htheta_two, Real.log_two_lt_d9]
      have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
        hx8 (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at hpow ⊢
      nlinarith [hvalue]

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
            · simpa [dusartLemma33FiniteRow_five] using (show x < 6 by linarith)
          · by_cases hsix : x < 7
            · refine ⟨dusartLemma33FiniteRow_six, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_six]
                exact le_of_not_gt hfive
              · simpa [dusartLemma33FiniteRow_six] using (show x < 7 by linarith)
            · by_cases hseven : x < 8
              · refine ⟨dusartLemma33FiniteRow_seven, by simp, ?_, ?_⟩
                · norm_num [dusartLemma33FiniteRow_seven]
                  exact le_of_not_gt hsix
                · simpa [dusartLemma33FiniteRow_seven,
                    dusartLemma33FiniteRow_of_zero] using (show x < 8 by linarith)
              · refine ⟨dusartLemma33FiniteRow_eight, by simp, ?_, ?_⟩
                · norm_num [dusartLemma33FiniteRow_eight]
                  exact le_of_not_gt hseven
                · simpa [dusartLemma33FiniteRow_eight,
                    dusartLemma33FiniteRow_of_zero] using (show x < 9 by linarith)

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
      rw [Chebyshev.theta_eq_theta_coe_floor, hsqrt_floor]
      have hvalue : Chebyshev.psi (9 : Real) - Chebyshev.theta 9 -
          Chebyshev.theta 3 < 1 := by
        nlinarith [hpsi, htheta, htheta_three, Real.log_two_lt_d9]
      have hpow := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8)
        (by linarith : (8 : Real) ≤ x)
        (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at hpow ⊢
      nlinarith [hvalue]

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
            · simpa [dusartLemma33FiniteRow_five,
                dusartLemma33FiniteRow_of_zero] using (show x < 6 by linarith)
          · by_cases hsix : x < 7
            · refine ⟨dusartLemma33FiniteRow_six, by simp, ?_, ?_⟩
              · norm_num [dusartLemma33FiniteRow_six]
                exact le_of_not_gt hfive
              · simpa [dusartLemma33FiniteRow_six,
                  dusartLemma33FiniteRow_of_zero] using (show x < 7 by linarith)
            · by_cases hseven : x < 8
              · refine ⟨dusartLemma33FiniteRow_seven, by simp, ?_, ?_⟩
                · norm_num [dusartLemma33FiniteRow_seven]
                  exact le_of_not_gt hsix
                · simpa [dusartLemma33FiniteRow_seven,
                    dusartLemma33FiniteRow_of_zero] using (show x < 8 by linarith)
              · by_cases height : x < 9
                · refine ⟨dusartLemma33FiniteRow_eight, by simp, ?_, ?_⟩
                  · norm_num [dusartLemma33FiniteRow_eight]
                    exact le_of_not_gt hseven
                  · simpa [dusartLemma33FiniteRow_eight,
                      dusartLemma33FiniteRow_of_zero] using (show x < 9 by linarith)
                · refine ⟨dusartLemma33FiniteRow_nine, by simp, ?_, ?_⟩
                  · norm_num [dusartLemma33FiniteRow_nine]
                    exact le_of_not_gt height
                  · simpa [dusartLemma33FiniteRow_nine,
                      dusartLemma33FiniteRow_of_zero] using (show x < 10 by linarith)

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
