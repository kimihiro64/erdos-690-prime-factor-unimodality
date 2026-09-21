import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 01 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData01 : List PocklingtonData := [
    { n := 3299, F := 3298, R := 1, a := 2, factors := [2, 17, 97], residues := [(2, 1649), (17, 2551), (97, 2776)] },
    { n := 3301, F := 3300, R := 1, a := 6, factors := [2, 2, 3, 5, 5, 11], residues := [(2, 1650), (3, 2725), (5, 233), (11, 2209)] },
    { n := 3307, F := 3306, R := 1, a := 2, factors := [2, 3, 19, 29], residues := [(2, 1653), (3, 2185), (19, 264), (29, 3069)] },
    { n := 3313, F := 3312, R := 1, a := 10, factors := [2, 2, 2, 2, 3, 3, 23], residues := [(2, 1656), (3, 2938), (23, 1903)] },
    { n := 3319, F := 3318, R := 1, a := 6, factors := [2, 3, 7, 79], residues := [(2, 1659), (3, 1703), (7, 166), (79, 1821)] },
    { n := 3323, F := 3322, R := 1, a := 2, factors := [2, 11, 151], residues := [(2, 1661), (11, 600), (151, 1340)] },
    { n := 3329, F := 3328, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 2, 13], residues := [(2, 1664), (13, 823)] },
    { n := 3331, F := 3330, R := 1, a := 3, factors := [2, 3, 3, 5, 37], residues := [(2, 1665), (3, 2708), (5, 558), (37, 325)] },
    { n := 3343, F := 3342, R := 1, a := 5, factors := [2, 3, 557], residues := [(2, 1671), (3, 2703), (557, 1385)] },
    { n := 3347, F := 3346, R := 1, a := 2, factors := [2, 7, 239], residues := [(2, 1673), (7, 2540), (239, 561)] },
    { n := 3359, F := 3358, R := 1, a := 11, factors := [2, 23, 73], residues := [(2, 1679), (23, 2555), (73, 1249)] },
    { n := 3361, F := 3360, R := 1, a := 22, factors := [2, 2, 2, 2, 2, 3, 5, 7], residues := [(2, 1680), (3, 297), (5, 3209), (7, 917)] },
    { n := 3371, F := 3370, R := 1, a := 2, factors := [2, 5, 337], residues := [(2, 1685), (5, 1563), (337, 1239)] },
    { n := 3373, F := 3372, R := 1, a := 5, factors := [2, 2, 3, 281], residues := [(2, 1686), (3, 1342), (281, 607)] },
    { n := 3389, F := 3388, R := 1, a := 3, factors := [2, 2, 7, 11, 11], residues := [(2, 1694), (7, 1341), (11, 1674)] },
    { n := 3391, F := 3390, R := 1, a := 3, factors := [2, 3, 5, 113], residues := [(2, 1695), (3, 1315), (5, 1689), (113, 2710)] },
    { n := 3407, F := 3406, R := 1, a := 5, factors := [2, 13, 131], residues := [(2, 1703), (13, 1695), (131, 2199)] },
    { n := 3413, F := 3412, R := 1, a := 2, factors := [2, 2, 853], residues := [(2, 1706), (853, 2958)] },
    { n := 3433, F := 3432, R := 1, a := 5, factors := [2, 2, 2, 3, 11, 13], residues := [(2, 1716), (3, 3343), (11, 2907), (13, 1746)] },
    { n := 3449, F := 3448, R := 1, a := 3, factors := [2, 2, 2, 431], residues := [(2, 1724), (431, 500)] },
    { n := 3457, F := 3456, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3], residues := [(2, 1728), (3, 911)] },
    { n := 3461, F := 3460, R := 1, a := 2, factors := [2, 2, 5, 173], residues := [(2, 1730), (5, 3335), (173, 2083)] },
    { n := 3463, F := 3462, R := 1, a := 3, factors := [2, 3, 577], residues := [(2, 1731), (3, 3340), (577, 2250)] },
    { n := 3467, F := 3466, R := 1, a := 2, factors := [2, 1733], residues := [(2, 1733), (1733, 1156)] },
    { n := 3469, F := 3468, R := 1, a := 2, factors := [2, 2, 3, 17, 17], residues := [(2, 1734), (3, 1717), (17, 371)] },
    { n := 3491, F := 3490, R := 1, a := 2, factors := [2, 5, 349], residues := [(2, 1745), (5, 1842), (349, 3218)] },
    { n := 3499, F := 3498, R := 1, a := 2, factors := [2, 3, 11, 53], residues := [(2, 1749), (3, 2280), (11, 2443), (53, 747)] },
    { n := 3511, F := 3510, R := 1, a := 7, factors := [2, 3, 3, 3, 5, 13], residues := [(2, 1755), (3, 1422), (5, 1130), (13, 2165)] },
    { n := 3517, F := 3516, R := 1, a := 2, factors := [2, 2, 3, 293], residues := [(2, 1758), (3, 2258), (293, 3158)] },
    { n := 3527, F := 3526, R := 1, a := 5, factors := [2, 41, 43], residues := [(2, 1763), (41, 1907), (43, 2318)] },
    { n := 3529, F := 3528, R := 1, a := 17, factors := [2, 2, 2, 3, 3, 7, 7], residues := [(2, 1764), (3, 149), (7, 257)] },
    { n := 3533, F := 3532, R := 1, a := 2, factors := [2, 2, 883], residues := [(2, 1766), (883, 3062)] },
    { n := 3539, F := 3538, R := 1, a := 2, factors := [2, 29, 61], residues := [(2, 1769), (29, 1358), (61, 752)] },
    { n := 3541, F := 3540, R := 1, a := 7, factors := [2, 2, 3, 5, 59], residues := [(2, 1770), (3, 1160), (5, 2944), (59, 1894)] },
    { n := 3547, F := 3546, R := 1, a := 2, factors := [2, 3, 3, 197], residues := [(2, 1773), (3, 387), (197, 3367)] },
    { n := 3557, F := 3556, R := 1, a := 2, factors := [2, 2, 7, 127], residues := [(2, 1778), (7, 1143), (127, 1741)] },
    { n := 3559, F := 3558, R := 1, a := 3, factors := [2, 3, 593], residues := [(2, 1779), (3, 478), (593, 44)] },
    { n := 3571, F := 3570, R := 1, a := 2, factors := [2, 3, 5, 7, 17], residues := [(2, 1785), (3, 34), (5, 2066), (7, 936), (17, 1151)] },
    { n := 3581, F := 3580, R := 1, a := 2, factors := [2, 2, 5, 179], residues := [(2, 1790), (5, 1290), (179, 1649)] },
    { n := 3583, F := 3582, R := 1, a := 3, factors := [2, 3, 3, 199], residues := [(2, 1791), (3, 2042), (199, 52)] },
    { n := 3593, F := 3592, R := 1, a := 3, factors := [2, 2, 2, 449], residues := [(2, 1796), (449, 2072)] },
    { n := 3607, F := 3606, R := 1, a := 5, factors := [2, 3, 601], residues := [(2, 1803), (3, 3140), (601, 3417)] },
    { n := 3613, F := 3612, R := 1, a := 2, factors := [2, 2, 3, 7, 43], residues := [(2, 1806), (3, 558), (7, 636), (43, 3172)] },
    { n := 3617, F := 3616, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 113], residues := [(2, 1808), (113, 3522)] },
    { n := 3623, F := 3622, R := 1, a := 5, factors := [2, 1811], residues := [(2, 1811), (1811, 151)] },
    { n := 3631, F := 3630, R := 1, a := 15, factors := [2, 3, 5, 11, 11], residues := [(2, 1815), (3, 2532), (5, 3135), (11, 216)] },
    { n := 3637, F := 3636, R := 1, a := 2, factors := [2, 2, 3, 3, 101], residues := [(2, 1818), (3, 2656), (101, 840)] },
    { n := 3643, F := 3642, R := 1, a := 2, factors := [2, 3, 607], residues := [(2, 1821), (3, 1073), (607, 1330)] },
    { n := 3659, F := 3658, R := 1, a := 2, factors := [2, 31, 59], residues := [(2, 1829), (31, 3320), (59, 446)] },
    { n := 3671, F := 3670, R := 1, a := 13, factors := [2, 5, 367], residues := [(2, 1835), (5, 3015), (367, 1851)] },
    { n := 3673, F := 3672, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 3, 17], residues := [(2, 1836), (3, 2832), (17, 2110)] },
    { n := 3677, F := 3676, R := 1, a := 2, factors := [2, 2, 919], residues := [(2, 1838), (919, 1716)] },
    { n := 3691, F := 3690, R := 1, a := 2, factors := [2, 3, 3, 5, 41], residues := [(2, 1845), (3, 1388), (5, 1857), (41, 3027)] },
    { n := 3697, F := 3696, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 7, 11], residues := [(2, 1848), (3, 2291), (7, 2433), (11, 3232)] },
    { n := 3701, F := 3700, R := 1, a := 2, factors := [2, 2, 5, 5, 37], residues := [(2, 1850), (5, 465), (37, 2101)] },
    { n := 3709, F := 3708, R := 1, a := 2, factors := [2, 2, 3, 3, 103], residues := [(2, 1854), (3, 2306), (103, 2326)] },
    { n := 3719, F := 3718, R := 1, a := 7, factors := [2, 11, 13, 13], residues := [(2, 1859), (11, 2161), (13, 2836)] },
    { n := 3727, F := 3726, R := 1, a := 3, factors := [2, 3, 3, 3, 3, 23], residues := [(2, 1863), (3, 1638), (23, 3421)] },
    { n := 3733, F := 3732, R := 1, a := 2, factors := [2, 2, 3, 311], residues := [(2, 1866), (3, 2172), (311, 1949)] },
    { n := 3739, F := 3738, R := 1, a := 7, factors := [2, 3, 7, 89], residues := [(2, 1869), (3, 231), (7, 2631), (89, 1859)] },
    { n := 3761, F := 3760, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 47], residues := [(2, 1880), (5, 1947), (47, 1463)] },
    { n := 3767, F := 3766, R := 1, a := 5, factors := [2, 7, 269], residues := [(2, 1883), (7, 1788), (269, 2468)] },
    { n := 3769, F := 3768, R := 1, a := 7, factors := [2, 2, 2, 3, 157], residues := [(2, 1884), (3, 154), (157, 3425)] },
    { n := 3779, F := 3778, R := 1, a := 2, factors := [2, 1889], residues := [(2, 1889), (1889, 1260)] },
    { n := 3793, F := 3792, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 79], residues := [(2, 1896), (3, 2172), (79, 1569)] },
    { n := 3797, F := 3796, R := 1, a := 2, factors := [2, 2, 13, 73], residues := [(2, 1898), (13, 2059), (73, 3357)] },
    { n := 3803, F := 3802, R := 1, a := 2, factors := [2, 1901], residues := [(2, 1901), (1901, 1268)] },
    { n := 3821, F := 3820, R := 1, a := 3, factors := [2, 2, 5, 191], residues := [(2, 1910), (5, 1350), (191, 2270)] },
    { n := 3823, F := 3822, R := 1, a := 3, factors := [2, 3, 7, 7, 13], residues := [(2, 1911), (3, 2943), (7, 1305), (13, 1194)] },
    { n := 3833, F := 3832, R := 1, a := 3, factors := [2, 2, 2, 479], residues := [(2, 1916), (479, 3379)] },
    { n := 3847, F := 3846, R := 1, a := 5, factors := [2, 3, 641], residues := [(2, 1923), (3, 3195), (641, 1842)] },
    { n := 3851, F := 3850, R := 1, a := 2, factors := [2, 5, 5, 7, 11], residues := [(2, 1925), (5, 3803), (7, 2535), (11, 2407)] },
    { n := 3853, F := 3852, R := 1, a := 2, factors := [2, 2, 3, 3, 107], residues := [(2, 1926), (3, 2948), (107, 1765)] },
    { n := 3863, F := 3862, R := 1, a := 5, factors := [2, 1931], residues := [(2, 1931), (1931, 161)] },
    { n := 3877, F := 3876, R := 1, a := 2, factors := [2, 2, 3, 17, 19], residues := [(2, 1938), (3, 1217), (17, 2439), (19, 3474)] },
    { n := 3881, F := 3880, R := 1, a := 13, factors := [2, 2, 2, 5, 97], residues := [(2, 1940), (5, 1358), (97, 2283)] },
    { n := 3889, F := 3888, R := 1, a := 11, factors := [2, 2, 2, 2, 3, 3, 3, 3, 3], residues := [(2, 1944), (3, 1962)] },
    { n := 3907, F := 3906, R := 1, a := 2, factors := [2, 3, 3, 7, 31], residues := [(2, 1953), (3, 2625), (7, 90), (31, 832)] },
    { n := 3911, F := 3910, R := 1, a := 13, factors := [2, 5, 17, 23], residues := [(2, 1955), (5, 2216), (17, 3501), (23, 1104)] },
    { n := 3917, F := 3916, R := 1, a := 2, factors := [2, 2, 11, 89], residues := [(2, 1958), (11, 312), (89, 853)] },
    { n := 3919, F := 3918, R := 1, a := 3, factors := [2, 3, 653], residues := [(2, 1959), (3, 3002), (653, 3020)] },
    { n := 3923, F := 3922, R := 1, a := 2, factors := [2, 37, 53], residues := [(2, 1961), (37, 2009), (53, 1754)] },
    { n := 3929, F := 3928, R := 1, a := 3, factors := [2, 2, 2, 491], residues := [(2, 1964), (491, 2582)] },
    { n := 3931, F := 3930, R := 1, a := 2, factors := [2, 3, 5, 131], residues := [(2, 1965), (3, 2826), (5, 2173), (131, 704)] },
    { n := 3943, F := 3942, R := 1, a := 3, factors := [2, 3, 3, 3, 73], residues := [(2, 1971), (3, 3564), (73, 2318)] },
    { n := 3947, F := 3946, R := 1, a := 2, factors := [2, 1973], residues := [(2, 1973), (1973, 1316)] },
    { n := 3967, F := 3966, R := 1, a := 6, factors := [2, 3, 661], residues := [(2, 1983), (3, 2348), (661, 464)] },
    { n := 3989, F := 3988, R := 1, a := 2, factors := [2, 2, 997], residues := [(2, 1994), (997, 266)] },
    { n := 4001, F := 4000, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 5, 5, 5], residues := [(2, 2000), (5, 2855)] },
    { n := 4003, F := 4002, R := 1, a := 2, factors := [2, 3, 23, 29], residues := [(2, 2001), (3, 2394), (23, 1961), (29, 1192)] },
    { n := 4007, F := 4006, R := 1, a := 5, factors := [2, 2003], residues := [(2, 2003), (2003, 167)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData01_valid : PocklingtonRow.Valid lowPocklingtonData01 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime01 (i : Fin lowPocklingtonData01.length) :
    Nat.Prime (lowPocklingtonData01.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData01_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3275) (q := 3299) (by
      have hp := lowPocklingtonPrime01 ⟨0, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3299) (q := 3301) (by
      have hp := lowPocklingtonPrime01 ⟨1, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3301) (q := 3307) (by
      have hp := lowPocklingtonPrime01 ⟨2, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3307) (q := 3313) (by
      have hp := lowPocklingtonPrime01 ⟨3, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3313) (q := 3319) (by
      have hp := lowPocklingtonPrime01 ⟨4, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3319) (q := 3323) (by
      have hp := lowPocklingtonPrime01 ⟨5, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3323) (q := 3329) (by
      have hp := lowPocklingtonPrime01 ⟨6, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3329) (q := 3331) (by
      have hp := lowPocklingtonPrime01 ⟨7, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part01_chain :
    DusartPrimeRowsChain 3275 3330 dusartPrimeRows_3275_3802_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3331) (q := 3343) (by
      have hp := lowPocklingtonPrime01 ⟨8, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3343) (q := 3347) (by
      have hp := lowPocklingtonPrime01 ⟨9, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3347) (q := 3359) (by
      have hp := lowPocklingtonPrime01 ⟨10, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3359) (q := 3361) (by
      have hp := lowPocklingtonPrime01 ⟨11, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3361) (q := 3371) (by
      have hp := lowPocklingtonPrime01 ⟨12, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3371) (q := 3373) (by
      have hp := lowPocklingtonPrime01 ⟨13, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3373) (q := 3389) (by
      have hp := lowPocklingtonPrime01 ⟨14, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3389) (q := 3391) (by
      have hp := lowPocklingtonPrime01 ⟨15, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part02_chain :
    DusartPrimeRowsChain 3331 3390 dusartPrimeRows_3275_3802_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3391) (q := 3407) (by
      have hp := lowPocklingtonPrime01 ⟨16, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3407) (q := 3413) (by
      have hp := lowPocklingtonPrime01 ⟨17, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3413) (q := 3433) (by
      have hp := lowPocklingtonPrime01 ⟨18, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3433) (q := 3449) (by
      have hp := lowPocklingtonPrime01 ⟨19, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3449) (q := 3457) (by
      have hp := lowPocklingtonPrime01 ⟨20, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3457) (q := 3461) (by
      have hp := lowPocklingtonPrime01 ⟨21, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3461) (q := 3463) (by
      have hp := lowPocklingtonPrime01 ⟨22, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3463) (q := 3467) (by
      have hp := lowPocklingtonPrime01 ⟨23, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part03_chain :
    DusartPrimeRowsChain 3391 3466 dusartPrimeRows_3275_3802_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3467) (q := 3469) (by
      have hp := lowPocklingtonPrime01 ⟨24, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3469) (q := 3491) (by
      have hp := lowPocklingtonPrime01 ⟨25, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3491) (q := 3499) (by
      have hp := lowPocklingtonPrime01 ⟨26, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3499) (q := 3511) (by
      have hp := lowPocklingtonPrime01 ⟨27, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3511) (q := 3517) (by
      have hp := lowPocklingtonPrime01 ⟨28, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3517) (q := 3527) (by
      have hp := lowPocklingtonPrime01 ⟨29, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3527) (q := 3529) (by
      have hp := lowPocklingtonPrime01 ⟨30, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3529) (q := 3533) (by
      have hp := lowPocklingtonPrime01 ⟨31, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part04_chain :
    DusartPrimeRowsChain 3467 3532 dusartPrimeRows_3275_3802_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3533) (q := 3539) (by
      have hp := lowPocklingtonPrime01 ⟨32, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3539) (q := 3541) (by
      have hp := lowPocklingtonPrime01 ⟨33, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3541) (q := 3547) (by
      have hp := lowPocklingtonPrime01 ⟨34, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3547) (q := 3557) (by
      have hp := lowPocklingtonPrime01 ⟨35, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3557) (q := 3559) (by
      have hp := lowPocklingtonPrime01 ⟨36, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3559) (q := 3571) (by
      have hp := lowPocklingtonPrime01 ⟨37, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3571) (q := 3581) (by
      have hp := lowPocklingtonPrime01 ⟨38, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3581) (q := 3583) (by
      have hp := lowPocklingtonPrime01 ⟨39, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part05_chain :
    DusartPrimeRowsChain 3533 3582 dusartPrimeRows_3275_3802_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3583) (q := 3593) (by
      have hp := lowPocklingtonPrime01 ⟨40, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3593) (q := 3607) (by
      have hp := lowPocklingtonPrime01 ⟨41, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3607) (q := 3613) (by
      have hp := lowPocklingtonPrime01 ⟨42, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3613) (q := 3617) (by
      have hp := lowPocklingtonPrime01 ⟨43, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3617) (q := 3623) (by
      have hp := lowPocklingtonPrime01 ⟨44, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3623) (q := 3631) (by
      have hp := lowPocklingtonPrime01 ⟨45, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3631) (q := 3637) (by
      have hp := lowPocklingtonPrime01 ⟨46, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3637) (q := 3643) (by
      have hp := lowPocklingtonPrime01 ⟨47, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part06_chain :
    DusartPrimeRowsChain 3583 3642 dusartPrimeRows_3275_3802_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3643) (q := 3659) (by
      have hp := lowPocklingtonPrime01 ⟨48, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3659) (q := 3671) (by
      have hp := lowPocklingtonPrime01 ⟨49, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3671) (q := 3673) (by
      have hp := lowPocklingtonPrime01 ⟨50, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3673) (q := 3677) (by
      have hp := lowPocklingtonPrime01 ⟨51, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3677) (q := 3691) (by
      have hp := lowPocklingtonPrime01 ⟨52, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3691) (q := 3697) (by
      have hp := lowPocklingtonPrime01 ⟨53, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3697) (q := 3701) (by
      have hp := lowPocklingtonPrime01 ⟨54, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3701) (q := 3709) (by
      have hp := lowPocklingtonPrime01 ⟨55, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part07_chain :
    DusartPrimeRowsChain 3643 3708 dusartPrimeRows_3275_3802_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3709) (q := 3719) (by
      have hp := lowPocklingtonPrime01 ⟨56, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3719) (q := 3727) (by
      have hp := lowPocklingtonPrime01 ⟨57, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3727) (q := 3733) (by
      have hp := lowPocklingtonPrime01 ⟨58, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3733) (q := 3739) (by
      have hp := lowPocklingtonPrime01 ⟨59, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3739) (q := 3761) (by
      have hp := lowPocklingtonPrime01 ⟨60, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3761) (q := 3767) (by
      have hp := lowPocklingtonPrime01 ⟨61, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3767) (q := 3769) (by
      have hp := lowPocklingtonPrime01 ⟨62, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3769) (q := 3779) (by
      have hp := lowPocklingtonPrime01 ⟨63, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part08_chain :
    DusartPrimeRowsChain 3709 3778 dusartPrimeRows_3275_3802_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · norm_num [dusartPrimeRow_of_explicit_3802]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · norm_num [dusartPrimeRow_of_explicit_3802]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · norm_num [dusartPrimeRow_of_explicit_3802]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · norm_num [dusartPrimeRow_of_explicit_3802]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · norm_num [dusartPrimeRow_of_explicit_3802]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3779) (q := 3793) (by
      have hp := lowPocklingtonPrime01 ⟨64, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3793) (q := 3797) (by
      have hp := lowPocklingtonPrime01 ⟨65, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3797) (q := 3803) (by
      have hp := lowPocklingtonPrime01 ⟨66, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part09_chain :
    DusartPrimeRowsChain 3779 3802 dusartPrimeRows_3275_3802_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.empty
        norm_num [dusartPrimeRow_of_explicit_3802, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3803) (q := 3821) (by
      have hp := lowPocklingtonPrime01 ⟨67, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3821) (q := 3823) (by
      have hp := lowPocklingtonPrime01 ⟨68, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3823) (q := 3833) (by
      have hp := lowPocklingtonPrime01 ⟨69, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3833) (q := 3847) (by
      have hp := lowPocklingtonPrime01 ⟨70, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3847) (q := 3851) (by
      have hp := lowPocklingtonPrime01 ⟨71, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3851) (q := 3853) (by
      have hp := lowPocklingtonPrime01 ⟨72, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3853) (q := 3863) (by
      have hp := lowPocklingtonPrime01 ⟨73, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3863) (q := 3877) (by
      have hp := lowPocklingtonPrime01 ⟨74, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part01_chain :
    DusartPrimeRowsChain 3803 3876 dusartPrimeRows_3803_4672_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3877) (q := 3881) (by
      have hp := lowPocklingtonPrime01 ⟨75, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3881) (q := 3889) (by
      have hp := lowPocklingtonPrime01 ⟨76, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3889) (q := 3907) (by
      have hp := lowPocklingtonPrime01 ⟨77, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3907) (q := 3911) (by
      have hp := lowPocklingtonPrime01 ⟨78, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3911) (q := 3917) (by
      have hp := lowPocklingtonPrime01 ⟨79, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3917) (q := 3919) (by
      have hp := lowPocklingtonPrime01 ⟨80, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3919) (q := 3923) (by
      have hp := lowPocklingtonPrime01 ⟨81, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3923) (q := 3929) (by
      have hp := lowPocklingtonPrime01 ⟨82, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part02_chain :
    DusartPrimeRowsChain 3877 3928 dusartPrimeRows_3803_4672_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3929) (q := 3931) (by
      have hp := lowPocklingtonPrime01 ⟨83, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3931) (q := 3943) (by
      have hp := lowPocklingtonPrime01 ⟨84, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3943) (q := 3947) (by
      have hp := lowPocklingtonPrime01 ⟨85, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3947) (q := 3967) (by
      have hp := lowPocklingtonPrime01 ⟨86, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3967) (q := 3989) (by
      have hp := lowPocklingtonPrime01 ⟨87, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3989) (q := 4001) (by
      have hp := lowPocklingtonPrime01 ⟨88, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4001) (q := 4003) (by
      have hp := lowPocklingtonPrime01 ⟨89, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4003) (q := 4007) (by
      have hp := lowPocklingtonPrime01 ⟨90, by simp [lowPocklingtonData01]⟩
      simpa [lowPocklingtonData01] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part03_chain :
    DusartPrimeRowsChain 3929 4006 dusartPrimeRows_3803_4672_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]
