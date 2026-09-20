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

theorem lowPrime_3299 : Nat.Prime 3299 := by
  let d := lowPocklingtonData01.get ⟨0, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3301 : Nat.Prime 3301 := by
  let d := lowPocklingtonData01.get ⟨1, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3307 : Nat.Prime 3307 := by
  let d := lowPocklingtonData01.get ⟨2, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3313 : Nat.Prime 3313 := by
  let d := lowPocklingtonData01.get ⟨3, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3319 : Nat.Prime 3319 := by
  let d := lowPocklingtonData01.get ⟨4, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3323 : Nat.Prime 3323 := by
  let d := lowPocklingtonData01.get ⟨5, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3329 : Nat.Prime 3329 := by
  let d := lowPocklingtonData01.get ⟨6, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3331 : Nat.Prime 3331 := by
  let d := lowPocklingtonData01.get ⟨7, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3343 : Nat.Prime 3343 := by
  let d := lowPocklingtonData01.get ⟨8, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3347 : Nat.Prime 3347 := by
  let d := lowPocklingtonData01.get ⟨9, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3359 : Nat.Prime 3359 := by
  let d := lowPocklingtonData01.get ⟨10, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3361 : Nat.Prime 3361 := by
  let d := lowPocklingtonData01.get ⟨11, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3371 : Nat.Prime 3371 := by
  let d := lowPocklingtonData01.get ⟨12, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3373 : Nat.Prime 3373 := by
  let d := lowPocklingtonData01.get ⟨13, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3389 : Nat.Prime 3389 := by
  let d := lowPocklingtonData01.get ⟨14, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3391 : Nat.Prime 3391 := by
  let d := lowPocklingtonData01.get ⟨15, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3407 : Nat.Prime 3407 := by
  let d := lowPocklingtonData01.get ⟨16, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3413 : Nat.Prime 3413 := by
  let d := lowPocklingtonData01.get ⟨17, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3433 : Nat.Prime 3433 := by
  let d := lowPocklingtonData01.get ⟨18, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3449 : Nat.Prime 3449 := by
  let d := lowPocklingtonData01.get ⟨19, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3457 : Nat.Prime 3457 := by
  let d := lowPocklingtonData01.get ⟨20, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3461 : Nat.Prime 3461 := by
  let d := lowPocklingtonData01.get ⟨21, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3463 : Nat.Prime 3463 := by
  let d := lowPocklingtonData01.get ⟨22, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3467 : Nat.Prime 3467 := by
  let d := lowPocklingtonData01.get ⟨23, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3469 : Nat.Prime 3469 := by
  let d := lowPocklingtonData01.get ⟨24, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3491 : Nat.Prime 3491 := by
  let d := lowPocklingtonData01.get ⟨25, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3499 : Nat.Prime 3499 := by
  let d := lowPocklingtonData01.get ⟨26, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3511 : Nat.Prime 3511 := by
  let d := lowPocklingtonData01.get ⟨27, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3517 : Nat.Prime 3517 := by
  let d := lowPocklingtonData01.get ⟨28, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3527 : Nat.Prime 3527 := by
  let d := lowPocklingtonData01.get ⟨29, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3529 : Nat.Prime 3529 := by
  let d := lowPocklingtonData01.get ⟨30, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3533 : Nat.Prime 3533 := by
  let d := lowPocklingtonData01.get ⟨31, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3539 : Nat.Prime 3539 := by
  let d := lowPocklingtonData01.get ⟨32, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3541 : Nat.Prime 3541 := by
  let d := lowPocklingtonData01.get ⟨33, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3547 : Nat.Prime 3547 := by
  let d := lowPocklingtonData01.get ⟨34, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3557 : Nat.Prime 3557 := by
  let d := lowPocklingtonData01.get ⟨35, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3559 : Nat.Prime 3559 := by
  let d := lowPocklingtonData01.get ⟨36, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3571 : Nat.Prime 3571 := by
  let d := lowPocklingtonData01.get ⟨37, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3581 : Nat.Prime 3581 := by
  let d := lowPocklingtonData01.get ⟨38, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3583 : Nat.Prime 3583 := by
  let d := lowPocklingtonData01.get ⟨39, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3593 : Nat.Prime 3593 := by
  let d := lowPocklingtonData01.get ⟨40, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3607 : Nat.Prime 3607 := by
  let d := lowPocklingtonData01.get ⟨41, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3613 : Nat.Prime 3613 := by
  let d := lowPocklingtonData01.get ⟨42, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3617 : Nat.Prime 3617 := by
  let d := lowPocklingtonData01.get ⟨43, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3623 : Nat.Prime 3623 := by
  let d := lowPocklingtonData01.get ⟨44, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3631 : Nat.Prime 3631 := by
  let d := lowPocklingtonData01.get ⟨45, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3637 : Nat.Prime 3637 := by
  let d := lowPocklingtonData01.get ⟨46, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3643 : Nat.Prime 3643 := by
  let d := lowPocklingtonData01.get ⟨47, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3659 : Nat.Prime 3659 := by
  let d := lowPocklingtonData01.get ⟨48, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3671 : Nat.Prime 3671 := by
  let d := lowPocklingtonData01.get ⟨49, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3673 : Nat.Prime 3673 := by
  let d := lowPocklingtonData01.get ⟨50, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3677 : Nat.Prime 3677 := by
  let d := lowPocklingtonData01.get ⟨51, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3691 : Nat.Prime 3691 := by
  let d := lowPocklingtonData01.get ⟨52, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3697 : Nat.Prime 3697 := by
  let d := lowPocklingtonData01.get ⟨53, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3701 : Nat.Prime 3701 := by
  let d := lowPocklingtonData01.get ⟨54, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3709 : Nat.Prime 3709 := by
  let d := lowPocklingtonData01.get ⟨55, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3719 : Nat.Prime 3719 := by
  let d := lowPocklingtonData01.get ⟨56, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3727 : Nat.Prime 3727 := by
  let d := lowPocklingtonData01.get ⟨57, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3733 : Nat.Prime 3733 := by
  let d := lowPocklingtonData01.get ⟨58, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3739 : Nat.Prime 3739 := by
  let d := lowPocklingtonData01.get ⟨59, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3761 : Nat.Prime 3761 := by
  let d := lowPocklingtonData01.get ⟨60, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3767 : Nat.Prime 3767 := by
  let d := lowPocklingtonData01.get ⟨61, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3769 : Nat.Prime 3769 := by
  let d := lowPocklingtonData01.get ⟨62, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3779 : Nat.Prime 3779 := by
  let d := lowPocklingtonData01.get ⟨63, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3793 : Nat.Prime 3793 := by
  let d := lowPocklingtonData01.get ⟨64, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3797 : Nat.Prime 3797 := by
  let d := lowPocklingtonData01.get ⟨65, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3803 : Nat.Prime 3803 := by
  let d := lowPocklingtonData01.get ⟨66, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3821 : Nat.Prime 3821 := by
  let d := lowPocklingtonData01.get ⟨67, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3823 : Nat.Prime 3823 := by
  let d := lowPocklingtonData01.get ⟨68, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3833 : Nat.Prime 3833 := by
  let d := lowPocklingtonData01.get ⟨69, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3847 : Nat.Prime 3847 := by
  let d := lowPocklingtonData01.get ⟨70, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3851 : Nat.Prime 3851 := by
  let d := lowPocklingtonData01.get ⟨71, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3853 : Nat.Prime 3853 := by
  let d := lowPocklingtonData01.get ⟨72, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3863 : Nat.Prime 3863 := by
  let d := lowPocklingtonData01.get ⟨73, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3877 : Nat.Prime 3877 := by
  let d := lowPocklingtonData01.get ⟨74, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3881 : Nat.Prime 3881 := by
  let d := lowPocklingtonData01.get ⟨75, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3889 : Nat.Prime 3889 := by
  let d := lowPocklingtonData01.get ⟨76, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3907 : Nat.Prime 3907 := by
  let d := lowPocklingtonData01.get ⟨77, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3911 : Nat.Prime 3911 := by
  let d := lowPocklingtonData01.get ⟨78, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3917 : Nat.Prime 3917 := by
  let d := lowPocklingtonData01.get ⟨79, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3919 : Nat.Prime 3919 := by
  let d := lowPocklingtonData01.get ⟨80, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3923 : Nat.Prime 3923 := by
  let d := lowPocklingtonData01.get ⟨81, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3929 : Nat.Prime 3929 := by
  let d := lowPocklingtonData01.get ⟨82, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3931 : Nat.Prime 3931 := by
  let d := lowPocklingtonData01.get ⟨83, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3943 : Nat.Prime 3943 := by
  let d := lowPocklingtonData01.get ⟨84, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3947 : Nat.Prime 3947 := by
  let d := lowPocklingtonData01.get ⟨85, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3967 : Nat.Prime 3967 := by
  let d := lowPocklingtonData01.get ⟨86, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_3989 : Nat.Prime 3989 := by
  let d := lowPocklingtonData01.get ⟨87, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_4001 : Nat.Prime 4001 := by
  let d := lowPocklingtonData01.get ⟨88, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_4003 : Nat.Prime 4003 := by
  let d := lowPocklingtonData01.get ⟨89, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp

theorem lowPrime_4007 : Nat.Prime 4007 := by
  let d := lowPocklingtonData01.get ⟨90, by simp [lowPocklingtonData01]⟩
  have hd : d ∈ lowPocklingtonData01 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData01_valid hd
  simpa [d, lowPocklingtonData01] using hp
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3275) (q := 3299) (by exact lowPrime_3299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3299) (q := 3301) (by exact lowPrime_3301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3301) (q := 3307) (by exact lowPrime_3307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3307) (q := 3313) (by exact lowPrime_3313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3313) (q := 3319) (by exact lowPrime_3319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3319) (q := 3323) (by exact lowPrime_3323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3323) (q := 3329) (by exact lowPrime_3329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3329) (q := 3331) (by exact lowPrime_3331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_3802 (p := 3331) (q := 3343) (by exact lowPrime_3343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3343) (q := 3347) (by exact lowPrime_3347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3347) (q := 3359) (by exact lowPrime_3359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3359) (q := 3361) (by exact lowPrime_3361) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3361) (q := 3371) (by exact lowPrime_3371) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3371) (q := 3373) (by exact lowPrime_3373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3373) (q := 3389) (by exact lowPrime_3389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3389) (q := 3391) (by exact lowPrime_3391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_3802 (p := 3391) (q := 3407) (by exact lowPrime_3407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3407) (q := 3413) (by exact lowPrime_3413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3413) (q := 3433) (by exact lowPrime_3433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3433) (q := 3449) (by exact lowPrime_3449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3449) (q := 3457) (by exact lowPrime_3457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3457) (q := 3461) (by exact lowPrime_3461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3461) (q := 3463) (by exact lowPrime_3463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3463) (q := 3467) (by exact lowPrime_3467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_3802 (p := 3467) (q := 3469) (by exact lowPrime_3469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3469) (q := 3491) (by exact lowPrime_3491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3491) (q := 3499) (by exact lowPrime_3499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3499) (q := 3511) (by exact lowPrime_3511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3511) (q := 3517) (by exact lowPrime_3517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3517) (q := 3527) (by exact lowPrime_3527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3527) (q := 3529) (by exact lowPrime_3529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3529) (q := 3533) (by exact lowPrime_3533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_3802 (p := 3533) (q := 3539) (by exact lowPrime_3539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3539) (q := 3541) (by exact lowPrime_3541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3541) (q := 3547) (by exact lowPrime_3547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3547) (q := 3557) (by exact lowPrime_3557) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3557) (q := 3559) (by exact lowPrime_3559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3559) (q := 3571) (by exact lowPrime_3571) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3571) (q := 3581) (by exact lowPrime_3581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3581) (q := 3583) (by exact lowPrime_3583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_3802 (p := 3583) (q := 3593) (by exact lowPrime_3593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3593) (q := 3607) (by exact lowPrime_3607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3607) (q := 3613) (by exact lowPrime_3613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3613) (q := 3617) (by exact lowPrime_3617) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3617) (q := 3623) (by exact lowPrime_3623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3623) (q := 3631) (by exact lowPrime_3631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3631) (q := 3637) (by exact lowPrime_3637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3637) (q := 3643) (by exact lowPrime_3643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_3802 (p := 3643) (q := 3659) (by exact lowPrime_3659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3659) (q := 3671) (by exact lowPrime_3671) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3671) (q := 3673) (by exact lowPrime_3673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3673) (q := 3677) (by exact lowPrime_3677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3677) (q := 3691) (by exact lowPrime_3691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3691) (q := 3697) (by exact lowPrime_3697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3697) (q := 3701) (by exact lowPrime_3701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3701) (q := 3709) (by exact lowPrime_3709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_3802 (p := 3709) (q := 3719) (by exact lowPrime_3719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3719) (q := 3727) (by exact lowPrime_3727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3727) (q := 3733) (by exact lowPrime_3733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3733) (q := 3739) (by exact lowPrime_3739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3739) (q := 3761) (by exact lowPrime_3761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3761) (q := 3767) (by exact lowPrime_3767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3767) (q := 3769) (by exact lowPrime_3769) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3769) (q := 3779) (by exact lowPrime_3779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_3802 (p := 3779) (q := 3793) (by exact lowPrime_3793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3793) (q := 3797) (by exact lowPrime_3797) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3797) (q := 3803) (by exact lowPrime_3803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_4670 (p := 3803) (q := 3821) (by exact lowPrime_3821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3821) (q := 3823) (by exact lowPrime_3823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3823) (q := 3833) (by exact lowPrime_3833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3833) (q := 3847) (by exact lowPrime_3847) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3847) (q := 3851) (by exact lowPrime_3851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3851) (q := 3853) (by exact lowPrime_3853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3853) (q := 3863) (by exact lowPrime_3863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3863) (q := 3877) (by exact lowPrime_3877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_4670 (p := 3877) (q := 3881) (by exact lowPrime_3881) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3881) (q := 3889) (by exact lowPrime_3889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3889) (q := 3907) (by exact lowPrime_3907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3907) (q := 3911) (by exact lowPrime_3911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3911) (q := 3917) (by exact lowPrime_3917) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3917) (q := 3919) (by exact lowPrime_3919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3919) (q := 3923) (by exact lowPrime_3923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3923) (q := 3929) (by exact lowPrime_3929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_4670 (p := 3929) (q := 3931) (by exact lowPrime_3931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3931) (q := 3943) (by exact lowPrime_3943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3943) (q := 3947) (by exact lowPrime_3947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3947) (q := 3967) (by exact lowPrime_3967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3967) (q := 3989) (by exact lowPrime_3989) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3989) (q := 4001) (by exact lowPrime_4001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4001) (q := 4003) (by exact lowPrime_4003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4003) (q := 4007) (by exact lowPrime_4007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
