import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 04 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData04 : List PocklingtonData := [
    { n := 5651, F := 5650, R := 1, a := 2, factors := [2, 5, 5, 113], residues := [(2, 2825), (5, 4590), (113, 2945)] },
    { n := 5653, F := 5652, R := 1, a := 5, factors := [2, 2, 3, 3, 157], residues := [(2, 2826), (3, 4015), (157, 3287)] },
    { n := 5657, F := 5656, R := 1, a := 3, factors := [2, 2, 2, 7, 101], residues := [(2, 2828), (7, 314), (101, 4683)] },
    { n := 5659, F := 5658, R := 1, a := 2, factors := [2, 3, 23, 41], residues := [(2, 2829), (3, 2374), (23, 271), (41, 5414)] },
    { n := 5669, F := 5668, R := 1, a := 3, factors := [2, 2, 13, 109], residues := [(2, 2834), (13, 1761), (109, 3393)] },
    { n := 5683, F := 5682, R := 1, a := 2, factors := [2, 3, 947], residues := [(2, 2841), (3, 2264), (947, 2616)] },
    { n := 5689, F := 5688, R := 1, a := 11, factors := [2, 2, 2, 3, 3, 79], residues := [(2, 2844), (3, 4882), (79, 4167)] },
    { n := 5693, F := 5692, R := 1, a := 2, factors := [2, 2, 1423], residues := [(2, 2846), (1423, 4934)] },
    { n := 5701, F := 5700, R := 1, a := 2, factors := [2, 2, 3, 5, 5, 19], residues := [(2, 2850), (3, 3775), (5, 421), (19, 4625)] },
    { n := 5711, F := 5710, R := 1, a := 19, factors := [2, 5, 571], residues := [(2, 2855), (5, 992), (571, 3596)] },
    { n := 5717, F := 5716, R := 1, a := 2, factors := [2, 2, 1429], residues := [(2, 2858), (1429, 2668)] },
    { n := 5737, F := 5736, R := 1, a := 5, factors := [2, 2, 2, 3, 239], residues := [(2, 2868), (3, 2735), (239, 3722)] },
    { n := 5741, F := 5740, R := 1, a := 2, factors := [2, 2, 5, 7, 41], residues := [(2, 2870), (5, 4259), (7, 1750), (41, 5260)] },
    { n := 5743, F := 5742, R := 1, a := 10, factors := [2, 3, 3, 11, 29], residues := [(2, 2871), (3, 1847), (11, 1228), (29, 2142)] },
    { n := 5749, F := 5748, R := 1, a := 2, factors := [2, 2, 3, 479], residues := [(2, 2874), (3, 2026), (479, 3090)] },
    { n := 5779, F := 5778, R := 1, a := 2, factors := [2, 3, 3, 3, 107], residues := [(2, 2889), (3, 4828), (107, 5671)] },
    { n := 5783, F := 5782, R := 1, a := 7, factors := [2, 7, 7, 59], residues := [(2, 2891), (7, 4720), (59, 2639)] },
    { n := 5791, F := 5790, R := 1, a := 6, factors := [2, 3, 5, 193], residues := [(2, 2895), (3, 3336), (5, 3242), (193, 4471)] },
    { n := 5801, F := 5800, R := 1, a := 3, factors := [2, 2, 2, 5, 5, 29], residues := [(2, 2900), (5, 3738), (29, 3226)] },
    { n := 5807, F := 5806, R := 1, a := 5, factors := [2, 2903], residues := [(2, 2903), (2903, 242)] },
    { n := 5813, F := 5812, R := 1, a := 2, factors := [2, 2, 1453], residues := [(2, 2906), (1453, 5038)] },
    { n := 5821, F := 5820, R := 1, a := 6, factors := [2, 2, 3, 5, 97], residues := [(2, 2910), (3, 3164), (5, 5019), (97, 2677)] },
    { n := 5827, F := 5826, R := 1, a := 2, factors := [2, 3, 971], residues := [(2, 2913), (3, 3434), (971, 185)] },
    { n := 5839, F := 5838, R := 1, a := 6, factors := [2, 3, 7, 139], residues := [(2, 2919), (3, 3274), (7, 5700), (139, 2008)] },
    { n := 5843, F := 5842, R := 1, a := 2, factors := [2, 23, 127], residues := [(2, 2921), (23, 5377), (127, 3562)] },
    { n := 5849, F := 5848, R := 1, a := 3, factors := [2, 2, 2, 17, 43], residues := [(2, 2924), (17, 3682), (43, 2232)] },
    { n := 5851, F := 5850, R := 1, a := 2, factors := [2, 3, 3, 5, 5, 13], residues := [(2, 2925), (3, 192), (5, 3802), (13, 1328)] },
    { n := 5857, F := 5856, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 3, 61], residues := [(2, 2928), (3, 421), (61, 353)] },
    { n := 5861, F := 5860, R := 1, a := 3, factors := [2, 2, 5, 293], residues := [(2, 2930), (5, 1431), (293, 5066)] },
    { n := 5867, F := 5866, R := 1, a := 5, factors := [2, 7, 419], residues := [(2, 2933), (7, 3478), (419, 1830)] },
    { n := 5869, F := 5868, R := 1, a := 2, factors := [2, 2, 3, 3, 163], residues := [(2, 2934), (3, 2215), (163, 2197)] },
    { n := 5879, F := 5878, R := 1, a := 11, factors := [2, 2939], residues := [(2, 2939), (2939, 49)] },
    { n := 5881, F := 5880, R := 1, a := 31, factors := [2, 2, 2, 3, 5, 7, 7], residues := [(2, 2940), (3, 2052), (5, 2343), (7, 4443)] },
    { n := 5897, F := 5896, R := 1, a := 3, factors := [2, 2, 2, 11, 67], residues := [(2, 2948), (11, 1122), (67, 2050)] },
    { n := 5903, F := 5902, R := 1, a := 5, factors := [2, 13, 227], residues := [(2, 2951), (13, 4424), (227, 307)] },
    { n := 5923, F := 5922, R := 1, a := 2, factors := [2, 3, 3, 7, 47], residues := [(2, 2961), (3, 4091), (7, 381), (47, 4316)] },
    { n := 5927, F := 5926, R := 1, a := 5, factors := [2, 2963], residues := [(2, 2963), (2963, 247)] },
    { n := 5939, F := 5938, R := 1, a := 2, factors := [2, 2969], residues := [(2, 2969), (2969, 1980)] },
    { n := 5953, F := 5952, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 3, 31], residues := [(2, 2976), (3, 4258), (31, 3196)] },
    { n := 5981, F := 5980, R := 1, a := 3, factors := [2, 2, 5, 13, 23], residues := [(2, 2990), (5, 5804), (13, 3197), (23, 4317)] },
    { n := 5987, F := 5986, R := 1, a := 2, factors := [2, 41, 73], residues := [(2, 2993), (41, 4621), (73, 4878)] },
    { n := 6007, F := 6006, R := 1, a := 3, factors := [2, 3, 7, 11, 13], residues := [(2, 3003), (3, 4030), (7, 2554), (11, 1704), (13, 931)] },
    { n := 6011, F := 6010, R := 1, a := 2, factors := [2, 5, 601], residues := [(2, 3005), (5, 4877), (601, 852)] },
    { n := 6029, F := 6028, R := 1, a := 2, factors := [2, 2, 11, 137], residues := [(2, 3014), (11, 1419), (137, 1592)] },
    { n := 6037, F := 6036, R := 1, a := 5, factors := [2, 2, 3, 503], residues := [(2, 3018), (3, 4194), (503, 3384)] },
    { n := 6043, F := 6042, R := 1, a := 5, factors := [2, 3, 19, 53], residues := [(2, 3021), (3, 1442), (19, 4832), (53, 3707)] },
    { n := 6047, F := 6046, R := 1, a := 5, factors := [2, 3023], residues := [(2, 3023), (3023, 252)] },
    { n := 6053, F := 6052, R := 1, a := 2, factors := [2, 2, 17, 89], residues := [(2, 3026), (17, 1842), (89, 2982)] },
    { n := 6067, F := 6066, R := 1, a := 2, factors := [2, 3, 3, 337], residues := [(2, 3033), (3, 1800), (337, 774)] },
    { n := 6073, F := 6072, R := 1, a := 10, factors := [2, 2, 2, 3, 11, 23], residues := [(2, 3036), (3, 3434), (11, 5796), (23, 2188)] },
    { n := 6079, F := 6078, R := 1, a := 17, factors := [2, 3, 1013], residues := [(2, 3039), (3, 1508), (1013, 4895)] },
    { n := 6089, F := 6088, R := 1, a := 3, factors := [2, 2, 2, 761], residues := [(2, 3044), (761, 1254)] },
    { n := 6091, F := 6090, R := 1, a := 7, factors := [2, 3, 5, 7, 29], residues := [(2, 3045), (3, 2278), (5, 1836), (7, 1226), (29, 3205)] },
    { n := 6101, F := 6100, R := 1, a := 2, factors := [2, 2, 5, 5, 61], residues := [(2, 3050), (5, 3503), (61, 4968)] },
    { n := 6113, F := 6112, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 191], residues := [(2, 3056), (191, 399)] },
    { n := 6121, F := 6120, R := 1, a := 7, factors := [2, 2, 2, 3, 3, 5, 17], residues := [(2, 3060), (3, 2424), (5, 4649), (17, 1797)] },
    { n := 6131, F := 6130, R := 1, a := 2, factors := [2, 5, 613], residues := [(2, 3065), (5, 4906), (613, 5256)] },
    { n := 6133, F := 6132, R := 1, a := 5, factors := [2, 2, 3, 7, 73], residues := [(2, 3066), (3, 316), (7, 443), (73, 5878)] },
    { n := 6143, F := 6142, R := 1, a := 5, factors := [2, 37, 83], residues := [(2, 3071), (37, 1546), (83, 2460)] },
    { n := 6151, F := 6150, R := 1, a := 3, factors := [2, 3, 5, 5, 41], residues := [(2, 3075), (3, 4031), (5, 5565), (41, 4265)] },
    { n := 6163, F := 6162, R := 1, a := 3, factors := [2, 3, 13, 79], residues := [(2, 3081), (3, 2080), (13, 2165), (79, 2693)] },
    { n := 6173, F := 6172, R := 1, a := 2, factors := [2, 2, 1543], residues := [(2, 3086), (1543, 5350)] },
    { n := 6197, F := 6196, R := 1, a := 2, factors := [2, 2, 1549], residues := [(2, 3098), (1549, 2892)] },
    { n := 6199, F := 6198, R := 1, a := 3, factors := [2, 3, 1033], residues := [(2, 3099), (3, 5014), (1033, 281)] },
    { n := 6203, F := 6202, R := 1, a := 2, factors := [2, 7, 443], residues := [(2, 3101), (7, 5943), (443, 666)] },
    { n := 6211, F := 6210, R := 1, a := 2, factors := [2, 3, 3, 3, 5, 23], residues := [(2, 3105), (3, 45), (5, 4797), (23, 1180)] },
    { n := 6217, F := 6216, R := 1, a := 5, factors := [2, 2, 2, 3, 7, 37], residues := [(2, 3108), (3, 4964), (7, 859), (37, 2409)] },
    { n := 6221, F := 6220, R := 1, a := 3, factors := [2, 2, 5, 311], residues := [(2, 3110), (5, 2722), (311, 1646)] },
    { n := 6229, F := 6228, R := 1, a := 2, factors := [2, 2, 3, 3, 173], residues := [(2, 3114), (3, 2386), (173, 290)] },
    { n := 6247, F := 6246, R := 1, a := 5, factors := [2, 3, 3, 347], residues := [(2, 3123), (3, 3392), (347, 5952)] },
    { n := 6257, F := 6256, R := 1, a := 3, factors := [2, 2, 2, 2, 17, 23], residues := [(2, 3128), (17, 4929), (23, 419)] },
    { n := 6263, F := 6262, R := 1, a := 5, factors := [2, 31, 101], residues := [(2, 3131), (31, 2109), (101, 295)] },
    { n := 6269, F := 6268, R := 1, a := 2, factors := [2, 2, 1567], residues := [(2, 3134), (1567, 418)] },
    { n := 6271, F := 6270, R := 1, a := 11, factors := [2, 3, 5, 11, 19], residues := [(2, 3135), (3, 5597), (5, 844), (11, 2881), (19, 4652)] },
    { n := 6277, F := 6276, R := 1, a := 2, factors := [2, 2, 3, 523], residues := [(2, 3138), (3, 5507), (523, 210)] },
    { n := 6287, F := 6286, R := 1, a := 7, factors := [2, 7, 449], residues := [(2, 3143), (7, 5345), (449, 4361)] },
    { n := 6299, F := 6298, R := 1, a := 2, factors := [2, 47, 67], residues := [(2, 3149), (47, 5040), (67, 4505)] },
    { n := 6301, F := 6300, R := 1, a := 10, factors := [2, 2, 3, 3, 5, 5, 7], residues := [(2, 3150), (3, 992), (5, 3219), (7, 1161)] },
    { n := 6311, F := 6310, R := 1, a := 7, factors := [2, 5, 631], residues := [(2, 3155), (5, 2500), (631, 3495)] },
    { n := 6317, F := 6316, R := 1, a := 2, factors := [2, 2, 1579], residues := [(2, 3158), (1579, 2948)] },
    { n := 6323, F := 6322, R := 1, a := 2, factors := [2, 29, 109], residues := [(2, 3161), (29, 3574), (109, 3368)] },
    { n := 6329, F := 6328, R := 1, a := 3, factors := [2, 2, 2, 7, 113], residues := [(2, 3164), (7, 474), (113, 1463)] },
    { n := 6337, F := 6336, R := 1, a := 10, factors := [2, 2, 2, 2, 2, 2, 3, 3, 11], residues := [(2, 3168), (3, 2616), (11, 1179)] },
    { n := 6343, F := 6342, R := 1, a := 3, factors := [2, 3, 7, 151], residues := [(2, 3171), (3, 4414), (7, 5787), (151, 2511)] },
    { n := 6353, F := 6352, R := 1, a := 3, factors := [2, 2, 2, 2, 397], residues := [(2, 3176), (397, 5054)] },
    { n := 6359, F := 6358, R := 1, a := 13, factors := [2, 11, 17, 17], residues := [(2, 3179), (11, 4634), (17, 2617)] },
    { n := 6361, F := 6360, R := 1, a := 19, factors := [2, 2, 2, 3, 5, 53], residues := [(2, 3180), (3, 5741), (5, 911), (53, 4265)] },
    { n := 6367, F := 6366, R := 1, a := 3, factors := [2, 3, 1061], residues := [(2, 3183), (3, 256), (1061, 3717)] },
    { n := 6373, F := 6372, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 59], residues := [(2, 3186), (3, 1916), (59, 2800)] },
    { n := 6379, F := 6378, R := 1, a := 2, factors := [2, 3, 1063], residues := [(2, 3189), (3, 3128), (1063, 5974)] },
    { n := 6389, F := 6388, R := 1, a := 2, factors := [2, 2, 1597], residues := [(2, 3194), (1597, 426)] },
    { n := 6397, F := 6396, R := 1, a := 2, factors := [2, 2, 3, 13, 41], residues := [(2, 3198), (3, 1367), (13, 408), (41, 581)] },
    { n := 6421, F := 6420, R := 1, a := 6, factors := [2, 2, 3, 5, 107], residues := [(2, 3210), (3, 1105), (5, 5845), (107, 32)] },
    { n := 6427, F := 6426, R := 1, a := 3, factors := [2, 3, 3, 3, 7, 17], residues := [(2, 3213), (3, 361), (7, 3782), (17, 1797)] },
    { n := 6449, F := 6448, R := 1, a := 3, factors := [2, 2, 2, 2, 13, 31], residues := [(2, 3224), (13, 706), (31, 5817)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData04_valid : PocklingtonRow.Valid lowPocklingtonData04 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime04 (i : Fin lowPocklingtonData04.length) :
    Nat.Prime (lowPocklingtonData04.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData04_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5647) (q := 5651) (by
      have hp := lowPocklingtonPrime04 ⟨0, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5651) (q := 5653) (by
      have hp := lowPocklingtonPrime04 ⟨1, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5653) (q := 5657) (by
      have hp := lowPocklingtonPrime04 ⟨2, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5657) (q := 5659) (by
      have hp := lowPocklingtonPrime04 ⟨3, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5659) (q := 5669) (by
      have hp := lowPocklingtonPrime04 ⟨4, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5669) (q := 5683) (by
      have hp := lowPocklingtonPrime04 ⟨5, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5683) (q := 5689) (by
      have hp := lowPocklingtonPrime04 ⟨6, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5689) (q := 5693) (by
      have hp := lowPocklingtonPrime04 ⟨7, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part04_chain :
    DusartPrimeRowsChain 5647 5692 dusartPrimeRows_5437_5710_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5710, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5693) (q := 5701) (by
      have hp := lowPocklingtonPrime04 ⟨8, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5701) (q := 5711) (by
      have hp := lowPocklingtonPrime04 ⟨9, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part05_chain :
    DusartPrimeRowsChain 5693 5710 dusartPrimeRows_5437_5710_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_5710, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5711) (q := 5717) (by
      have hp := lowPocklingtonPrime04 ⟨10, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5717) (q := 5737) (by
      have hp := lowPocklingtonPrime04 ⟨11, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5737) (q := 5741) (by
      have hp := lowPocklingtonPrime04 ⟨12, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5741) (q := 5743) (by
      have hp := lowPocklingtonPrime04 ⟨13, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5743) (q := 5749) (by
      have hp := lowPocklingtonPrime04 ⟨14, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5749) (q := 5779) (by
      have hp := lowPocklingtonPrime04 ⟨15, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5779) (q := 5783) (by
      have hp := lowPocklingtonPrime04 ⟨16, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5783) (q := 5791) (by
      have hp := lowPocklingtonPrime04 ⟨17, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part01_chain :
    DusartPrimeRowsChain 5711 5790 dusartPrimeRows_5711_6006_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6002, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5791) (q := 5801) (by
      have hp := lowPocklingtonPrime04 ⟨18, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5801) (q := 5807) (by
      have hp := lowPocklingtonPrime04 ⟨19, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5807) (q := 5813) (by
      have hp := lowPocklingtonPrime04 ⟨20, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5813) (q := 5821) (by
      have hp := lowPocklingtonPrime04 ⟨21, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5821) (q := 5827) (by
      have hp := lowPocklingtonPrime04 ⟨22, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5827) (q := 5839) (by
      have hp := lowPocklingtonPrime04 ⟨23, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5839) (q := 5843) (by
      have hp := lowPocklingtonPrime04 ⟨24, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5843) (q := 5849) (by
      have hp := lowPocklingtonPrime04 ⟨25, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part02_chain :
    DusartPrimeRowsChain 5791 5848 dusartPrimeRows_5711_6006_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6002, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5849) (q := 5851) (by
      have hp := lowPocklingtonPrime04 ⟨26, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5851) (q := 5857) (by
      have hp := lowPocklingtonPrime04 ⟨27, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5857) (q := 5861) (by
      have hp := lowPocklingtonPrime04 ⟨28, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5861) (q := 5867) (by
      have hp := lowPocklingtonPrime04 ⟨29, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5867) (q := 5869) (by
      have hp := lowPocklingtonPrime04 ⟨30, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5869) (q := 5879) (by
      have hp := lowPocklingtonPrime04 ⟨31, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5879) (q := 5881) (by
      have hp := lowPocklingtonPrime04 ⟨32, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5881) (q := 5897) (by
      have hp := lowPocklingtonPrime04 ⟨33, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part03_chain :
    DusartPrimeRowsChain 5849 5896 dusartPrimeRows_5711_6006_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6002, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5897) (q := 5903) (by
      have hp := lowPocklingtonPrime04 ⟨34, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5903) (q := 5923) (by
      have hp := lowPocklingtonPrime04 ⟨35, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5923) (q := 5927) (by
      have hp := lowPocklingtonPrime04 ⟨36, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5927) (q := 5939) (by
      have hp := lowPocklingtonPrime04 ⟨37, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5939) (q := 5953) (by
      have hp := lowPocklingtonPrime04 ⟨38, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5953) (q := 5981) (by
      have hp := lowPocklingtonPrime04 ⟨39, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5981) (q := 5987) (by
      have hp := lowPocklingtonPrime04 ⟨40, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5987) (q := 6007) (by
      have hp := lowPocklingtonPrime04 ⟨41, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part04_chain :
    DusartPrimeRowsChain 5897 6006 dusartPrimeRows_5711_6006_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6002, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6007) (q := 6011) (by
      have hp := lowPocklingtonPrime04 ⟨42, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6011) (q := 6029) (by
      have hp := lowPocklingtonPrime04 ⟨43, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6029) (q := 6037) (by
      have hp := lowPocklingtonPrime04 ⟨44, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6037) (q := 6043) (by
      have hp := lowPocklingtonPrime04 ⟨45, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6043) (q := 6047) (by
      have hp := lowPocklingtonPrime04 ⟨46, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6047) (q := 6053) (by
      have hp := lowPocklingtonPrime04 ⟨47, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6053) (q := 6067) (by
      have hp := lowPocklingtonPrime04 ⟨48, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6067) (q := 6073) (by
      have hp := lowPocklingtonPrime04 ⟨49, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part01_chain :
    DusartPrimeRowsChain 6007 6072 dusartPrimeRows_6007_6310_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6310, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6073) (q := 6079) (by
      have hp := lowPocklingtonPrime04 ⟨50, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6079) (q := 6089) (by
      have hp := lowPocklingtonPrime04 ⟨51, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6089) (q := 6091) (by
      have hp := lowPocklingtonPrime04 ⟨52, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6091) (q := 6101) (by
      have hp := lowPocklingtonPrime04 ⟨53, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6101) (q := 6113) (by
      have hp := lowPocklingtonPrime04 ⟨54, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6113) (q := 6121) (by
      have hp := lowPocklingtonPrime04 ⟨55, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6121) (q := 6131) (by
      have hp := lowPocklingtonPrime04 ⟨56, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6131) (q := 6133) (by
      have hp := lowPocklingtonPrime04 ⟨57, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part02_chain :
    DusartPrimeRowsChain 6073 6132 dusartPrimeRows_6007_6310_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6310, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6133) (q := 6143) (by
      have hp := lowPocklingtonPrime04 ⟨58, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6143) (q := 6151) (by
      have hp := lowPocklingtonPrime04 ⟨59, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6151) (q := 6163) (by
      have hp := lowPocklingtonPrime04 ⟨60, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6163) (q := 6173) (by
      have hp := lowPocklingtonPrime04 ⟨61, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6173) (q := 6197) (by
      have hp := lowPocklingtonPrime04 ⟨62, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6197) (q := 6199) (by
      have hp := lowPocklingtonPrime04 ⟨63, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6199) (q := 6203) (by
      have hp := lowPocklingtonPrime04 ⟨64, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6203) (q := 6211) (by
      have hp := lowPocklingtonPrime04 ⟨65, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part03_chain :
    DusartPrimeRowsChain 6133 6210 dusartPrimeRows_6007_6310_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6310, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6211) (q := 6217) (by
      have hp := lowPocklingtonPrime04 ⟨66, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6217) (q := 6221) (by
      have hp := lowPocklingtonPrime04 ⟨67, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6221) (q := 6229) (by
      have hp := lowPocklingtonPrime04 ⟨68, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6229) (q := 6247) (by
      have hp := lowPocklingtonPrime04 ⟨69, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6247) (q := 6257) (by
      have hp := lowPocklingtonPrime04 ⟨70, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6257) (q := 6263) (by
      have hp := lowPocklingtonPrime04 ⟨71, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6263) (q := 6269) (by
      have hp := lowPocklingtonPrime04 ⟨72, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6269) (q := 6271) (by
      have hp := lowPocklingtonPrime04 ⟨73, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part04_chain :
    DusartPrimeRowsChain 6211 6270 dusartPrimeRows_6007_6310_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6310, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6271) (q := 6277) (by
      have hp := lowPocklingtonPrime04 ⟨74, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6277) (q := 6287) (by
      have hp := lowPocklingtonPrime04 ⟨75, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6287) (q := 6299) (by
      have hp := lowPocklingtonPrime04 ⟨76, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6299) (q := 6301) (by
      have hp := lowPocklingtonPrime04 ⟨77, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6301) (q := 6311) (by
      have hp := lowPocklingtonPrime04 ⟨78, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part05_chain :
    DusartPrimeRowsChain 6271 6310 dusartPrimeRows_6007_6310_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · apply DusartPrimeRowsChain.empty
            norm_num [dusartPrimeRow_of_explicit_6310, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6311) (q := 6317) (by
      have hp := lowPocklingtonPrime04 ⟨79, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6317) (q := 6323) (by
      have hp := lowPocklingtonPrime04 ⟨80, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6323) (q := 6329) (by
      have hp := lowPocklingtonPrime04 ⟨81, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6329) (q := 6337) (by
      have hp := lowPocklingtonPrime04 ⟨82, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6337) (q := 6343) (by
      have hp := lowPocklingtonPrime04 ⟨83, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6343) (q := 6353) (by
      have hp := lowPocklingtonPrime04 ⟨84, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6353) (q := 6359) (by
      have hp := lowPocklingtonPrime04 ⟨85, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6359) (q := 6361) (by
      have hp := lowPocklingtonPrime04 ⟨86, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part01_chain :
    DusartPrimeRowsChain 6311 6360 dusartPrimeRows_6311_6636_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6634, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6361) (q := 6367) (by
      have hp := lowPocklingtonPrime04 ⟨87, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6367) (q := 6373) (by
      have hp := lowPocklingtonPrime04 ⟨88, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6373) (q := 6379) (by
      have hp := lowPocklingtonPrime04 ⟨89, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6379) (q := 6389) (by
      have hp := lowPocklingtonPrime04 ⟨90, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6389) (q := 6397) (by
      have hp := lowPocklingtonPrime04 ⟨91, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6397) (q := 6421) (by
      have hp := lowPocklingtonPrime04 ⟨92, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6421) (q := 6427) (by
      have hp := lowPocklingtonPrime04 ⟨93, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6427) (q := 6449) (by
      have hp := lowPocklingtonPrime04 ⟨94, by simp [lowPocklingtonData04]⟩
      simpa [lowPocklingtonData04] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part02_chain :
    DusartPrimeRowsChain 6361 6448 dusartPrimeRows_6311_6636_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6634, dusartPrimeRow_of_explicit_right]
