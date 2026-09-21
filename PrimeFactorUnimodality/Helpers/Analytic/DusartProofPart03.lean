import PrimeFactorUnimodality.Helpers.Analytic.DusartProofPart02


set_option autoImplicit false

namespace PrimeFactorUnimodality

noncomputable section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/- The finite boundary in Dusart's Lemma 3.3 is exactly 10^33. -/

/-! # DusartProof source part 03

This module is a sequential source split of the analytic development.
-/

theorem log_47_lt_three_point_eight_eight : Real.log 47 < (388 : Real) / 100 := by
  have h := Real.log_lt_log (by norm_num : (0 : Real) < 47)
    (by norm_num : (47 : Real) < 48)
  rw [show (48 : Real) = 2 ^ (4 : Nat) * 3 by norm_num,
    Real.log_mul, Real.log_pow] at h
  · nlinarith [LogTables.log_2_lt, LogTables.log_3_lt]
  all_goals positivity

theorem psi_sub_theta_nat_2400_lt_sixtythree :
    Chebyshev.psi (2400 : Real) - Chebyshev.theta 2400 < 63 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 2400
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 2400
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 2401,
      ↑(Nat.log p 2400) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 2401, Real.log ↑p < 63
  have hp : Nat.primesBelow 2401 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
        709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
        797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
        967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031,
        1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093,
        1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171,
        1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237,
        1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303,
        1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409,
        1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471,
        1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543,
        1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607,
        1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669,
        1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753,
        1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847,
        1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913,
        1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999,
        2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081,
        2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141,
        2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239,
        2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309,
        2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381,
        2383, 2389, 2393, 2399} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven, log_37_lt_three_point_seven,
    log_41_lt_three_point_eight, log_43_lt_three_point_nine,
    log_47_lt_three_point_eight_eight]

theorem dusart_lemma_3_3_at_2401 :
    Chebyshev.psi (2401 : Real) - Chebyshev.theta 2401 -
        Chebyshev.theta (49 : Real) <
      (1777745 : Real) / 1000000 * (2401 : Real) ^ (1 / (3 : Real)) := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 2401
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 2401
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  norm_num [Nat.log, Nat.log.go]
  interval_decide

def dusartLemma33FiniteRow_twothousandtwohundrednine_twothousandfourhundred :
    DusartLemma33FiniteRow := by
  have htheta_fortyseven := Chebyshev.theta_eq_sum_primesLE_log 47
  have hp47 : Nat.primesLE 47 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} := by decide
  rw [hp47] at htheta_fortyseven
  norm_num [Nat.log, Nat.log.go] at htheta_fortyseven
  have hlog42_le47 : Real.log 42 ≤ Real.log 47 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 2209 2400 47
    (63 : Real) 40 13
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_2400_lt_sixtythree
  · nlinarith [htheta_fortyseven, hlog42_le47,
      LogTables.log_30_gt, Real.log_two_gt_d9, Real.log_three_gt_d9,
      Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((13 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (13 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (13 : Real) = ((13 : Real) ^ (3 : Nat)) ^ (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

def dusartLemma33FiniteRow_exact_twofourzeroone : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_integer_endpoint 2401 dusart_lemma_3_3_at_2401

theorem dusart_lemma_3_3_at_2402 :
    Chebyshev.psi (2402 : Real) - Chebyshev.theta 2402 -
        Chebyshev.theta (Real.sqrt (2402 : Real)) <
      (1777745 : Real) / 1000000 * (2402 : Real) ^ (1 / (3 : Real)) := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 2402
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 2402
  have hsqrt_floor : ⌊Real.sqrt (2402 : Real)⌋₊ = 49 := by
    apply (Nat.floor_eq_iff (by positivity : (0 : Real) ≤ Real.sqrt 2402)).2
    constructor
    · norm_num
    · nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ (2402 : Real)),
        Real.sqrt_nonneg (2402 : Real)]
  norm_num at hpsi htheta
  rw [hpsi, htheta, Chebyshev.theta_eq_theta_coe_floor, hsqrt_floor]
  norm_num [Nat.log, Nat.log.go]
  interval_decide

def dusartLemma33FiniteRow_exact_twofourzeroone_two : DusartLemma33FiniteRow :=
  dusartLemma33FiniteRow_of_integer_endpoint 2402 dusart_lemma_3_3_at_2402

theorem psi_sub_theta_nat_2047_lt_fiftysix :
    Chebyshev.psi (2047 : Real) - Chebyshev.theta 2047 < 56 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 2047
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 2047
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 2048,
      ↑(Nat.log p 2047) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 2048, Real.log ↑p < 56
  have hp : Nat.primesBelow 2048 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
        709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
        797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
        967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031,
        1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093,
        1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171,
        1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237,
        1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303,
        1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409,
        1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471,
        1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543,
        1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607,
        1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669,
        1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753,
        1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847,
        1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913,
        1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999,
        2003, 2011, 2017, 2027, 2029, 2039} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven, log_37_lt_three_point_seven,
    log_41_lt_three_point_eight, log_43_lt_three_point_nine]

def dusartLemma33FiniteRow_eighteenfortynine_twothousandfortyseven :
    DusartLemma33FiniteRow := by
  have htheta_fortythree := Chebyshev.theta_eq_sum_primesLE_log 43
  have hp43 : Nat.primesLE 43 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} := by decide
  rw [hp43] at htheta_fortythree
  norm_num [Nat.log, Nat.log.go] at htheta_fortythree
  apply dusartLemma33FiniteRow_of_endpoint_bounds 1849 2047 43
    (56 : Real) 36 (61 / 5)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_2047_lt_fiftysix
  · have hlog29_le31 : Real.log 29 ≤ Real.log 31 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le37 : Real.log 29 ≤ Real.log 37 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le41 : Real.log 29 ≤ Real.log 41 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le43 : Real.log 29 ≤ Real.log 43 :=
      Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [htheta_fortythree, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt,
      LogTables.log_11_gt, LogTables.log_13_gt, LogTables.log_17_gt,
      LogTables.log_19_gt, LogTables.log_23_gt, LogTables.log_29_gt,
      hlog29_le31, hlog29_le37, hlog29_le41, hlog29_le43]
  · intro x hx hleft
    have hbase : ((61 / 5 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (61 / 5 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (61 / 5 : Real) = ((61 / 5 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_1848_lt_fiftytwo :
    Chebyshev.psi (1848 : Real) - Chebyshev.theta 1848 < 52 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 1848
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 1848
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 1849,
      ↑(Nat.log p 1848) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 1849, Real.log ↑p < 52
  have hp : Nat.primesBelow 1849 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
        709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
        797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
        967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031,
        1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093,
        1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171,
        1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237,
        1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303,
        1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409,
        1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471,
        1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543,
        1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607,
        1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669,
        1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753,
        1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven, log_37_lt_three_point_seven,
    log_41_lt_three_point_eight]

def dusartLemma33FiniteRow_sixteeneighty_one_eighteenfortyeight :
    DusartLemma33FiniteRow := by
  have htheta_fortyone := Chebyshev.theta_eq_sum_primesLE_log 41
  have hp41 : Nat.primesLE 41 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41} := by decide
  rw [hp41] at htheta_fortyone
  norm_num [Nat.log, Nat.log.go] at htheta_fortyone
  apply dusartLemma33FiniteRow_of_endpoint_bounds 1681 1848 41
    (52 : Real) 32 (59 / 5)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_1848_lt_fiftytwo
  · have hlog29_le31 : Real.log 29 ≤ Real.log 31 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le37 : Real.log 29 ≤ Real.log 37 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le41 : Real.log 29 ≤ Real.log 41 :=
      Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [htheta_fortyone, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt,
      LogTables.log_11_gt, LogTables.log_13_gt, LogTables.log_17_gt,
      LogTables.log_19_gt, LogTables.log_23_gt, LogTables.log_29_gt,
      hlog29_le31, hlog29_le37, hlog29_le41]
  · intro x hx hleft
    have hbase : ((59 / 5 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (59 / 5 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (59 / 5 : Real) = ((59 / 5 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_1680_lt_fortyeight :
    Chebyshev.psi (1680 : Real) - Chebyshev.theta 1680 < 48 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 1680
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 1680
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 1681,
      ↑(Nat.log p 1680) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 1681, Real.log ↑p < 48
  have hp : Nat.primesBelow 1681 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
        709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
        797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
        967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031,
        1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093,
        1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171,
        1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237,
        1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303,
        1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409,
        1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471,
        1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543,
        1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607,
        1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven, log_37_lt_three_point_seven]

def dusartLemma33FiniteRow_thirteenhundredsixtynine_sixteeneighty :
    DusartLemma33FiniteRow := by
  have htheta_thirtyseven := Chebyshev.theta_eq_sum_primesLE_log 37
  have hp37 : Nat.primesLE 37 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} := by decide
  rw [hp37] at htheta_thirtyseven
  norm_num [Nat.log, Nat.log.go] at htheta_thirtyseven
  apply dusartLemma33FiniteRow_of_endpoint_bounds 1369 1680 37
    (48 : Real) 29 (111 / 10)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_1680_lt_fortyeight
  · have hlog29_le31 : Real.log 29 ≤ Real.log 31 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hlog29_le37 : Real.log 29 ≤ Real.log 37 :=
      Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [htheta_thirtyseven, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt,
      LogTables.log_11_gt, LogTables.log_13_gt, LogTables.log_17_gt,
      LogTables.log_19_gt, LogTables.log_23_gt, LogTables.log_29_gt,
      hlog29_le31, hlog29_le37]
  · intro x hx hleft
    have hbase : ((111 / 10 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (111 / 10 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (111 / 10 : Real) = ((111 / 10 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_1368_lt_fortythree_point_seven :
    Chebyshev.psi (1368 : Real) - Chebyshev.theta 1368 < (437 : Real) / 10 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 1368
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 1368
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 1369,
      ↑(Nat.log p 1368) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 1369, Real.log ↑p < (437 : Real) / 10
  have hp : Nat.primesBelow 1369 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
        709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
        797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
        967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031,
        1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093,
        1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171,
        1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237,
        1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303,
        1307, 1319, 1321, 1327, 1361, 1367} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven]

def dusartLemma33FiniteRow_tenthousandtwentyfour_thirteenhundredsixtyeight :
    DusartLemma33FiniteRow := by
  have htheta_thirtyone := Chebyshev.theta_eq_sum_primesLE_log 31
  have hp31 : Nat.primesLE 31 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by decide
  rw [hp31] at htheta_thirtyone
  norm_num [Nat.log, Nat.log.go] at htheta_thirtyone
  apply dusartLemma33FiniteRow_of_endpoint_bounds 1024 1368 32
    ((437 : Real) / 10) 26 10
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_1368_lt_fortythree_point_seven
  · have hlog29_le31 : Real.log 29 ≤ Real.log 31 :=
      Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [htheta_thirtyone, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt,
      LogTables.log_11_gt, LogTables.log_13_gt, LogTables.log_17_gt,
      LogTables.log_19_gt, LogTables.log_23_gt, LogTables.log_29_gt,
      hlog29_le31]
  · intro x hx hleft
    have hbase : ((10 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (10 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (10 : Real) = ((10 : Real) ^ (3 : Nat)) ^ (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_1023_lt_fortyone :
    Chebyshev.psi (1023 : Real) - Chebyshev.theta 1023 < 41 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 1023
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 1023
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 1024,
      ↑(Nat.log p 1023) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 1024, Real.log ↑p < 41
  have hp : Nat.primesBelow 1024 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
        631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
        709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
        797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
        877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
        967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt, ElementaryLogBounds.log_29_lt,
    log_31_lt_three_point_four_seven]

def dusartLemma33FiniteRow_ninehundredsixtyone_tenthousandtwentythree :
    DusartLemma33FiniteRow := by
  have htheta_thirtyone := Chebyshev.theta_eq_sum_primesLE_log 31
  have hp31 : Nat.primesLE 31 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by decide
  rw [hp31] at htheta_thirtyone
  norm_num [Nat.log, Nat.log.go] at htheta_thirtyone
  apply dusartLemma33FiniteRow_of_endpoint_bounds 961 1023 31
    (41 : Real) 24 (49 / 5)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_1023_lt_fortyone
  · have hlog29_le31 : Real.log 29 ≤ Real.log 31 :=
      Real.log_le_log (by norm_num) (by norm_num)
    nlinarith [htheta_thirtyone, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt,
      LogTables.log_11_gt, LogTables.log_13_gt, LogTables.log_17_gt,
      LogTables.log_19_gt, LogTables.log_23_gt, LogTables.log_29_gt,
      hlog29_le31]
  · intro x hx hleft
    have hbase : ((49 / 5 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (49 / 5 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (49 / 5 : Real) = ((49 / 5 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem psi_sub_theta_nat_575_lt_thirty :
    Chebyshev.psi (575 : Real) - Chebyshev.theta 575 < 30 := by
  have hpsi := Chebyshev.psi_eq_sum_mul_log_prime 575
  have htheta := Chebyshev.theta_eq_sum_primesLE_log 575
  norm_num at hpsi htheta
  rw [hpsi, htheta]
  change (∑ p ∈ Nat.primesBelow 576,
      ↑(Nat.log p 575) * Real.log ↑p) -
    ∑ p ∈ Nat.primesBelow 576, Real.log ↑p < 30
  have hp : Nat.primesBelow 576 =
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
        59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
        127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
        191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
        257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
        331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
        401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
        467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
        563, 569, 571} := by
    decide
  rw [hp]
  norm_num [Nat.log, Nat.log.go]
  nlinarith [Real.log_two_lt_d9, Real.log_three_lt_d9,
    Real.log_five_lt_d9, LogTables.log_7_lt,
    ElementaryLogBounds.log_11_lt, ElementaryLogBounds.log_13_lt,
    ElementaryLogBounds.log_17_lt, ElementaryLogBounds.log_19_lt,
    ElementaryLogBounds.log_23_lt]

def dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive :
    DusartLemma33FiniteRow := by
  have htheta_twentytwo := Chebyshev.theta_eq_sum_primesLE_log 22
  have hp22 : Nat.primesLE 22 = {2, 3, 5, 7, 11, 13, 17, 19} := by decide
  rw [hp22] at htheta_twentytwo
  norm_num [Nat.log, Nat.log.go] at htheta_twentytwo
  apply dusartLemma33FiniteRow_of_endpoint_bounds 529 575 23
    (30 : Real) 16 8
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_575_lt_thirty
  · have hmono : Chebyshev.theta (22 : Real) ≤ Chebyshev.theta 23 := by
      apply Chebyshev.theta_mono
      norm_num
    exact lt_of_lt_of_le (by
      nlinarith [htheta_twentytwo, Real.log_two_gt_d9,
        Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt]) hmono
  · intro x hx hleft
    have hbase : ((8 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (8 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (8 : Real) = ((8 : Real) ^ (3 : Nat)) ^ (1 / 3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

def dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven :
    DusartLemma33FiniteRow := by
  have htheta_nineteen := Chebyshev.theta_eq_sum_primesLE_log 19
  have hp19 : Nat.primesLE 19 = {2, 3, 5, 7, 11, 13, 17, 19} := by decide
  rw [hp19] at htheta_nineteen
  norm_num [Nat.log, Nat.log.go] at htheta_nineteen
  have hlog10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [show (10 : Real) = 2 * 5 by norm_num, Real.log_mul]
    · norm_num
    all_goals positivity
  have hlog10_le11 : Real.log 10 ≤ Real.log 11 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog10_le13 : Real.log 10 ≤ Real.log 13 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog10_le17 : Real.log 10 ≤ Real.log 17 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlog10_le19 : Real.log 10 ≤ Real.log 19 :=
    Real.log_le_log (by norm_num) (by norm_num)
  apply dusartLemma33FiniteRow_of_endpoint_bounds 361 511 19
    ((271 : Real) / 10) (29 / 2) (71 / 10)
  · norm_num
  · intro x hx hleft hright
    nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg x]
  · exact psi_sub_theta_nat_511_lt_twentyseven_point_one
  · nlinarith [htheta_nineteen, hlog10, hlog10_le11, hlog10_le13,
      hlog10_le17, hlog10_le19, Real.log_two_gt_d9,
      Real.log_three_gt_d9, Real.log_five_gt_d9, LogTables.log_7_gt]
  · intro x hx hleft
    have hbase : ((71 / 10 : Real) ^ (3 : Nat)) ≤ x := by
      norm_num
      linarith
    have hpow := Real.rpow_le_rpow (by positivity :
        (0 : Real) ≤ (71 / 10 : Real) ^ (3 : Nat)) hbase
      (by norm_num : (0 : Real) ≤ (1 / 3 : Real))
    calc
      (71 / 10 : Real) = ((71 / 10 : Real) ^ (3 : Nat)) ^
          (1 / 3 : Real) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
      _ ≤ x ^ (1 / 3 : Real) := hpow
  · norm_num

theorem dusartLemma33FiniteRowsCover_fivehundredeleven :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
        dusartLemma33FiniteRow_nine, dusartLemma33FiniteRow_ten_twentyfour,
        dusartLemma33FiniteRow_twentyfive_thirtyfive,
        dusartLemma33FiniteRow_thirtysix_sixtythree,
        dusartLemma33FiniteRow_sixtyfour_onetwenty,
        dusartLemma33FiniteRow_onetwentyone_onehundredsixtyseven,
        dusartLemma33FiniteRow_onehundredsixtyeight,
        dusartLemma33FiniteRow_onenine_sixtythree,
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty] ++
        [dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven]) 511 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_threesixty
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_fivehundredeight :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
        dusartLemma33FiniteRow_nine, dusartLemma33FiniteRow_ten_twentyfour,
        dusartLemma33FiniteRow_twentyfive_thirtyfive,
        dusartLemma33FiniteRow_thirtysix_sixtythree,
        dusartLemma33FiniteRow_sixtyfour_onetwenty,
        dusartLemma33FiniteRow_onetwentyone_onehundredsixtyseven,
        dusartLemma33FiniteRow_onehundredsixtyeight,
        dusartLemma33FiniteRow_onenine_sixtythree,
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven] ++
        [dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight]) 528 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_fivehundredeleven
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_fivehundredseventyfive :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
        dusartLemma33FiniteRow_nine, dusartLemma33FiniteRow_ten_twentyfour,
        dusartLemma33FiniteRow_twentyfive_thirtyfive,
        dusartLemma33FiniteRow_thirtysix_sixtythree,
        dusartLemma33FiniteRow_sixtyfour_onetwenty,
        dusartLemma33FiniteRow_onetwentyone_onehundredsixtyseven,
        dusartLemma33FiniteRow_onehundredsixtyeight,
        dusartLemma33FiniteRow_onenine_sixtythree,
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight] ++
        [dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive]) 575 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_fivehundredeight
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

theorem dusartLemma33FiniteRowsCover_sixhundredtwentyfour :
    DusartLemma33FiniteRowsCover
      ([dusartLemma33FiniteRow_zero_one, dusartLemma33FiniteRow_two,
        dusartLemma33FiniteRow_three, dusartLemma33FiniteRow_four,
        dusartLemma33FiniteRow_five, dusartLemma33FiniteRow_six,
        dusartLemma33FiniteRow_seven, dusartLemma33FiniteRow_eight,
        dusartLemma33FiniteRow_nine, dusartLemma33FiniteRow_ten_twentyfour,
        dusartLemma33FiniteRow_twentyfive_thirtyfive,
        dusartLemma33FiniteRow_thirtysix_sixtythree,
        dusartLemma33FiniteRow_sixtyfour_onetwenty,
        dusartLemma33FiniteRow_onetwentyone_onehundredsixtyseven,
        dusartLemma33FiniteRow_onehundredsixtyeight,
        dusartLemma33FiniteRow_onenine_sixtythree,
        dusartLemma33FiniteRow_twohundredfiftysix_twohundredeightyeight,
        dusartLemma33FiniteRow_twohundredeightynine_threehundredfortytwo,
        dusartLemma33FiniteRow_threehundredfortythree_threehundredsixty,
        dusartLemma33FiniteRow_threehundredsixtyone_fivehundredeleven,
        dusartLemma33FiniteRow_fivehundredtwelve_fivehundredeight,
        dusartLemma33FiniteRow_fivehundredtwentynine_fivehundredseventyfive] ++
        [dusartLemma33FiniteRow_fivehundredseventysix_sixhundredtwentyfour]) 624 := by
  apply dusartLemma33FiniteRowsCover_append_row
    dusartLemma33FiniteRowsCover_fivehundredseventyfive
  intro x hgt hx hX
  constructor
  · linarith
  · norm_num
    linarith

end

end PrimeFactorUnimodality
