import PrimeFactorUnimodality.Helpers.Analytic.DusartLemma33MidrangeEndpoints

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-! # Midrange rows for Dusart's Lemma 3.3

This module contains the reusable bounded row definitions. -/

namespace PrimeFactorUnimodality

noncomputable section

def dusartLemma33MidrangeRow_2402_2808 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 2402 2808 49
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (49 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_2402_2808
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 2402)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_2809_3124 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 2809 3124 53
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (53 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_2809_3124
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 2809)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_3125_3480 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 3125 3480 55
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (55 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_3125_3480
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 3125)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_3481_3720 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 3481 3720 59
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (59 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_3481_3720
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 3481)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_3721_4488 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 3721 4488 61
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (61 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_3721_4488
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 3721)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_4489_5040 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 4489 5040 67
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (67 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_4489_5040
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 4489)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_5041_5328 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 5041 5328 71
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (71 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_5041_5328
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 5041)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_5329_6240 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 5329 6240 73
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (73 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_5329_6240
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 5329)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_6241_6858 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 6241 6858 79
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (79 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_6241_6858
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 6241)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_6859_6888 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 6859 6888 82
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (82 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_6859_6888
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 6859)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_6889_7920 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 6889 7920 83
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (83 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_6889_7920
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 6889)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_7921_9408 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 7921 9408 89
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (89 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_7921_9408
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 7921)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_9409_10200 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 9409 10200 97
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (97 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_9409_10200
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 9409)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_10201_11448 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 10201 11448 101
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (101 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_10201_11448
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 10201)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_11449_12166 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 11449 12166 107
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (107 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_11449_12166
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 11449)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_12167_12768 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 12167 12768 110
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (110 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_12167_12768
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 12167)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_12769_16128 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 12769 16128 113
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (113 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_12769_16128
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 12769)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_16129_17160 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 16129 17160 127
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (127 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_16129_17160
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 16129)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_17161_18768 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 17161 18768 131
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (131 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_17161_18768
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 17161)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_18769_19320 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 18769 19320 137
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (137 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_18769_19320
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 18769)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_19321_22200 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 19321 22200 139
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (139 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_19321_22200
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 19321)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_22201_24388 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 22201 24388 149
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (149 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_22201_24388
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 22201)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_24389_24648 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 24389 24648 156
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (156 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_24389_24648
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 24389)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_24649_26568 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 24649 26568 157
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (157 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_24649_26568
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 24649)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_26569_28560 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 26569 28560 163
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (163 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_26569_28560
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 26569)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_28561_29928 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 28561 29928 169
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (169 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_28561_29928
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 28561)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_29929_32040 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 29929 32040 173
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (173 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_29929_32040
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 29929)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_32041_32760 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 32041 32760 179
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (179 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_32041_32760
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 32041)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_32761_36480 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 32761 36480 181
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (181 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_32761_36480
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 32761)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_36481_37248 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 36481 37248 191
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (191 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_36481_37248
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 36481)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_37249_38808 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 37249 38808 193
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (193 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_37249_38808
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 37249)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_38809_44520 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 38809 44520 197
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (197 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_38809_44520
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 38809)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_44521_50652 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 44521 50652 211
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (211 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_44521_50652
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 44521)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_50653_52440 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 50653 52440 225
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (225 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_50653_52440
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 50653)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_52441_57120 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 52441 57120 229
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (229 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_52441_57120
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 52441)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_57121_63000 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 57121 63000 239
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (239 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_57121_63000
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 57121)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_63001_69168 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 63001 69168 251
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (251 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_63001_69168
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 63001)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_69169_73440 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 69169 73440 263
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (263 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_69169_73440
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 69169)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_73441_78960 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 73441 78960 271
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (271 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_73441_78960
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 73441)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_78961_83520 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 78961 83520 281
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (281 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_78961_83520
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 78961)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_83521_94248 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 83521 94248 289
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (289 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_83521_94248
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 83521)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_94249_97968 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 94249 97968 307
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (307 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_94249_97968
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 94249)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_97969_109560 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 97969 109560 313
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (313 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_97969_109560
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 97969)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_109561_120408 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 109561 120408 331
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (331 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_109561_120408
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 109561)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_120409_124608 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 120409 124608 347
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (347 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_120409_124608
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 120409)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_124609_134688 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 124609 134688 353
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (353 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_124609_134688
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 124609)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_134689_143640 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 134689 143640 367
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (367 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_134689_143640
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 134689)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_143641_151320 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 143641 151320 379
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (379 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_143641_151320
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 143641)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_151321_160800 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 151321 160800 389
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (389 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_151321_160800
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 151321)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_160801_175560 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 160801 175560 401
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (401 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_160801_175560
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 160801)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_175561_185760 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 175561 185760 419
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (419 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_175561_185760
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 175561)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_185761_196248 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 185761 196248 431
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (431 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_185761_196248
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 185761)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_196249_208848 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 196249 208848 443
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (443 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_196249_208848
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 196249)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_208849_218088 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 208849 218088 457
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (457 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_208849_218088
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 208849)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_218089_237168 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 218089 237168 467
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (467 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_218089_237168
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 218089)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_237169_253008 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 237169 253008 487
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (487 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_237169_253008
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 237169)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_253009_273528 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 253009 273528 503
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (503 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_253009_273528
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 253009)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_273529_300762 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 273529 300762 523
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (523 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_273529_300762
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 273529)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_300763_323760 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 300763 323760 548
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (548 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_300763_323760
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 300763)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_323761_344568 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 323761 344568 569
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (569 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_323761_344568
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 323761)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_344569_361200 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 344569 361200 587
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (587 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_344569_361200
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 344569)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_361201_380688 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 361201 380688 601
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (601 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_361201_380688
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 361201)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_380689_398160 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 380689 398160 617
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (617 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_380689_398160
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 380689)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_398161_418608 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 398161 418608 631
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (631 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_398161_418608
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 398161)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_418609_436920 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 418609 436920 647
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (647 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_418609_436920
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 418609)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_436921_466488 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 436921 466488 661
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (661 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_436921_466488
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 436921)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_466489_502680 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 466489 502680 683
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (683 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_466489_502680
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 466489)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_502681_537288 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 502681 537288 709
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (709 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_502681_537288
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 502681)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_537289_571786 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 537289 571786 733
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (733 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_537289_571786
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 537289)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_571787_591360 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 571787 591360 756
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (756 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_571787_591360
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 571787)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_591361_654480 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 591361 654480 769
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (769 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_591361_654480
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 591361)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_654481_683928 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 654481 683928 809
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (809 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_654481_683928
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 654481)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_683929_734448 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 683929 734448 827
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (827 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_683929_734448
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 683929)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_734449_776160 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 734449 776160 857
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (857 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_734449_776160
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 734449)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_776161_829920 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 776161 829920 881
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (881 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_776161_829920
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 776161)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_829921_896808 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 829921 896808 911
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (911 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_829921_896808
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 829921)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_896809_954528 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 896809 954528 947
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (947 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_896809_954528
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 896809)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_954529_1026168 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 954529 1026168 977
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (977 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_954529_1026168
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 954529)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1026169_1079520 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1026169 1079520 1013
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1013 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1026169_1079520
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1026169)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1079521_1129968 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1079521 1129968 1039
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1039 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1079521_1129968
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1079521)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1129969_1203408 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1129969 1203408 1063
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1063 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1129969_1203408
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1129969)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1203409_1274640 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1203409 1274640 1097
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1097 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1203409_1274640
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1203409)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1274641_1371240 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1274641 1371240 1129
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1129 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1274641_1371240
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1274641)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1371241_1442896 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1371241 1442896 1171
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1171 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1371241_1442896
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1371241)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1442897_1510440 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1442897 1510440 1201
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1201 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1442897_1510440
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1442897)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1510441_1630728 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1510441 1630728 1229
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1229 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1510441_1630728
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1510441)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1630729_1682208 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1630729 1682208 1277
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1277 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1630729_1682208
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1630729)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1682209_1760928 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1682209 1760928 1297
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1297 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1682209_1760928
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1682209)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1760929_1957200 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1760929 1957200 1327
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1327 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1760929_1957200
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1760929)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_1957201_2053488 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 1957201 2053488 1399
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1399 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_1957201_2053488
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1957201)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_2053489_2163840 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 2053489 2163840 1433
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1433 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_2053489_2163840
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 2053489)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_2163841_2247000 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 2163841 2247000 1471
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1471 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_2163841_2247000
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 2163841)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_2247001_2411808 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 2247001 2411808 1499
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1499 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_2247001_2411808
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 2247001)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_2411809_2550408 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 2411809 2550408 1553
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1553 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_2411809_2550408
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 2411809)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_2550409_2627640 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 2550409 2627640 1597
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1597 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_2550409_2627640
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 2550409)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_2627641_2785560 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 2627641 2785560 1621
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1621 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_2627641_2785560
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 2627641)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_2785561_2968728 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 2785561 2968728 1669
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1669 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_2785561_2968728
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 2785561)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_2968729_3179088 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 2968729 3179088 1723
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1723 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_2968729_3179088
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 2968729)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_3179089_3411408 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 3179089 3411408 1783
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1783 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_3179089_3411408
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 3179089)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_3411409_3530640 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 3411409 3530640 1847
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1847 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_3411409_3530640
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 3411409)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_3530641_3798600 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 3530641 3798600 1879
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1879 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_3530641_3798600
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 3530641)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_3798601_3996000 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 3798601 3996000 1949
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1949 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_3798601_3996000
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 3798601)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_3996001_4255968 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 3996001 4255968 1999
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (1999 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_3996001_4255968
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 3996001)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_4255969_4464768 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 4255969 4464768 2063
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2063 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_4255969_4464768
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 4255969)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_4464769_4748040 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 4464769 4748040 2113
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2113 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_4464769_4748040
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 4464769)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_4748041_5031048 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 4748041 5031048 2179
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2179 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_4748041_5031048
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 4748041)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_5031049_5257848 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 5031049 5257848 2243
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2243 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_5031049_5257848
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 5031049)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_5257849_5527200 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 5257849 5527200 2293
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2293 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_5257849_5527200
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 5257849)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_5527201_5755200 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 5527201 5755200 2351
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2351 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_5527201_5755200
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 5527201)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_5755201_6086088 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 5755201 6086088 2399
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2399 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_5755201_6086088
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 5755201)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_6086089_6497400 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 6086089 6497400 2467
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2467 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_6086089_6497400
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 6086089)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_6497401_6932688 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 6497401 6932688 2549
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2549 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_6497401_6932688
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 6497401)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_6932689_7219968 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 6932689 7219968 2633
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2633 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_6932689_7219968
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 6932689)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_7219969_7458360 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 7219969 7458360 2687
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2687 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_7219969_7458360
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 7219969)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_7458361_7845600 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 7458361 7845600 2731
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2731 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_7458361_7845600
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 7458361)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_7845601_8185320 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 7845601 8185320 2801
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2801 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_7845601_8185320
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 7845601)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_8185321_8720208 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 8185321 8720208 2861
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2861 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_8185321_8720208
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8185321)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_8720209_9223368 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 8720209 9223368 2953
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (2953 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_8720209_9223368
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 8720209)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_9223369_9740640 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 9223369 9740640 3037
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (3037 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_9223369_9740640
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 9223369)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRow_9740641_10000000 : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_endpoint_left_power 9740641 10000000 3121
    (by norm_num)
    (by
      intro x hx hleft hright
      have hroot_sq : (3121 : Real) ^ 2 ≤ x := by
        have hleft' : (0 : Real) ≤ x := by linarith
        norm_num at hleft ⊢
        nlinarith
      nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
    dusart_lemma33_row_endpoint_9740641_10000000
    (by
      intro x hx hleft
      have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 9740641)
        (by exact_mod_cast hleft) (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
      norm_num at h ⊢
      exact h)

def dusartLemma33MidrangeRows : List DusartLemma33FiniteRow := [
  dusartLemma33MidrangeRow_2402_2808,
  dusartLemma33MidrangeRow_2809_3124,
  dusartLemma33MidrangeRow_3125_3480,
  dusartLemma33MidrangeRow_3481_3720,
  dusartLemma33MidrangeRow_3721_4488,
  dusartLemma33MidrangeRow_4489_5040,
  dusartLemma33MidrangeRow_5041_5328,
  dusartLemma33MidrangeRow_5329_6240,
  dusartLemma33MidrangeRow_6241_6858,
  dusartLemma33MidrangeRow_6859_6888,
  dusartLemma33MidrangeRow_6889_7920,
  dusartLemma33MidrangeRow_7921_9408,
  dusartLemma33MidrangeRow_9409_10200,
  dusartLemma33MidrangeRow_10201_11448,
  dusartLemma33MidrangeRow_11449_12166,
  dusartLemma33MidrangeRow_12167_12768,
  dusartLemma33MidrangeRow_12769_16128,
  dusartLemma33MidrangeRow_16129_17160,
  dusartLemma33MidrangeRow_17161_18768,
  dusartLemma33MidrangeRow_18769_19320,
  dusartLemma33MidrangeRow_19321_22200,
  dusartLemma33MidrangeRow_22201_24388,
  dusartLemma33MidrangeRow_24389_24648,
  dusartLemma33MidrangeRow_24649_26568,
  dusartLemma33MidrangeRow_26569_28560,
  dusartLemma33MidrangeRow_28561_29928,
  dusartLemma33MidrangeRow_29929_32040,
  dusartLemma33MidrangeRow_32041_32760,
  dusartLemma33MidrangeRow_32761_36480,
  dusartLemma33MidrangeRow_36481_37248,
  dusartLemma33MidrangeRow_37249_38808,
  dusartLemma33MidrangeRow_38809_44520,
  dusartLemma33MidrangeRow_44521_50652,
  dusartLemma33MidrangeRow_50653_52440,
  dusartLemma33MidrangeRow_52441_57120,
  dusartLemma33MidrangeRow_57121_63000,
  dusartLemma33MidrangeRow_63001_69168,
  dusartLemma33MidrangeRow_69169_73440,
  dusartLemma33MidrangeRow_73441_78960,
  dusartLemma33MidrangeRow_78961_83520,
  dusartLemma33MidrangeRow_83521_94248,
  dusartLemma33MidrangeRow_94249_97968,
  dusartLemma33MidrangeRow_97969_109560,
  dusartLemma33MidrangeRow_109561_120408,
  dusartLemma33MidrangeRow_120409_124608,
  dusartLemma33MidrangeRow_124609_134688,
  dusartLemma33MidrangeRow_134689_143640,
  dusartLemma33MidrangeRow_143641_151320,
  dusartLemma33MidrangeRow_151321_160800,
  dusartLemma33MidrangeRow_160801_175560,
  dusartLemma33MidrangeRow_175561_185760,
  dusartLemma33MidrangeRow_185761_196248,
  dusartLemma33MidrangeRow_196249_208848,
  dusartLemma33MidrangeRow_208849_218088,
  dusartLemma33MidrangeRow_218089_237168,
  dusartLemma33MidrangeRow_237169_253008,
  dusartLemma33MidrangeRow_253009_273528,
  dusartLemma33MidrangeRow_273529_300762,
  dusartLemma33MidrangeRow_300763_323760,
  dusartLemma33MidrangeRow_323761_344568,
  dusartLemma33MidrangeRow_344569_361200,
  dusartLemma33MidrangeRow_361201_380688,
  dusartLemma33MidrangeRow_380689_398160,
  dusartLemma33MidrangeRow_398161_418608,
  dusartLemma33MidrangeRow_418609_436920,
  dusartLemma33MidrangeRow_436921_466488,
  dusartLemma33MidrangeRow_466489_502680,
  dusartLemma33MidrangeRow_502681_537288,
  dusartLemma33MidrangeRow_537289_571786,
  dusartLemma33MidrangeRow_571787_591360,
  dusartLemma33MidrangeRow_591361_654480,
  dusartLemma33MidrangeRow_654481_683928,
  dusartLemma33MidrangeRow_683929_734448,
  dusartLemma33MidrangeRow_734449_776160,
  dusartLemma33MidrangeRow_776161_829920,
  dusartLemma33MidrangeRow_829921_896808,
  dusartLemma33MidrangeRow_896809_954528,
  dusartLemma33MidrangeRow_954529_1026168,
  dusartLemma33MidrangeRow_1026169_1079520,
  dusartLemma33MidrangeRow_1079521_1129968,
  dusartLemma33MidrangeRow_1129969_1203408,
  dusartLemma33MidrangeRow_1203409_1274640,
  dusartLemma33MidrangeRow_1274641_1371240,
  dusartLemma33MidrangeRow_1371241_1442896,
  dusartLemma33MidrangeRow_1442897_1510440,
  dusartLemma33MidrangeRow_1510441_1630728,
  dusartLemma33MidrangeRow_1630729_1682208,
  dusartLemma33MidrangeRow_1682209_1760928,
  dusartLemma33MidrangeRow_1760929_1957200,
  dusartLemma33MidrangeRow_1957201_2053488,
  dusartLemma33MidrangeRow_2053489_2163840,
  dusartLemma33MidrangeRow_2163841_2247000,
  dusartLemma33MidrangeRow_2247001_2411808,
  dusartLemma33MidrangeRow_2411809_2550408,
  dusartLemma33MidrangeRow_2550409_2627640,
  dusartLemma33MidrangeRow_2627641_2785560,
  dusartLemma33MidrangeRow_2785561_2968728,
  dusartLemma33MidrangeRow_2968729_3179088,
  dusartLemma33MidrangeRow_3179089_3411408,
  dusartLemma33MidrangeRow_3411409_3530640,
  dusartLemma33MidrangeRow_3530641_3798600,
  dusartLemma33MidrangeRow_3798601_3996000,
  dusartLemma33MidrangeRow_3996001_4255968,
  dusartLemma33MidrangeRow_4255969_4464768,
  dusartLemma33MidrangeRow_4464769_4748040,
  dusartLemma33MidrangeRow_4748041_5031048,
  dusartLemma33MidrangeRow_5031049_5257848,
  dusartLemma33MidrangeRow_5257849_5527200,
  dusartLemma33MidrangeRow_5527201_5755200,
  dusartLemma33MidrangeRow_5755201_6086088,
  dusartLemma33MidrangeRow_6086089_6497400,
  dusartLemma33MidrangeRow_6497401_6932688,
  dusartLemma33MidrangeRow_6932689_7219968,
  dusartLemma33MidrangeRow_7219969_7458360,
  dusartLemma33MidrangeRow_7458361_7845600,
  dusartLemma33MidrangeRow_7845601_8185320,
  dusartLemma33MidrangeRow_8185321_8720208,
  dusartLemma33MidrangeRow_8720209_9223368,
  dusartLemma33MidrangeRow_9223369_9740640,
  dusartLemma33MidrangeRow_9740641_10000000,
]

end

end PrimeFactorUnimodality
