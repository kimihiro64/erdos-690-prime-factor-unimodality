import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 03 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData03 : List PocklingtonData := [
    { n := 4817, F := 4816, R := 1, a := 3, factors := [2, 2, 2, 2, 7, 43], residues := [(2, 2408), (7, 2310), (43, 4804)] },
    { n := 4831, F := 4830, R := 1, a := 3, factors := [2, 3, 5, 7, 23], residues := [(2, 2415), (3, 1633), (5, 3287), (7, 1231), (23, 1412)] },
    { n := 4861, F := 4860, R := 1, a := 11, factors := [2, 2, 3, 3, 3, 3, 3, 5], residues := [(2, 2430), (3, 106), (5, 4154)] },
    { n := 4871, F := 4870, R := 1, a := 11, factors := [2, 5, 487], residues := [(2, 2435), (5, 898), (487, 3989)] },
    { n := 4877, F := 4876, R := 1, a := 2, factors := [2, 2, 23, 53], residues := [(2, 2438), (23, 3871), (53, 326)] },
    { n := 4889, F := 4888, R := 1, a := 3, factors := [2, 2, 2, 13, 47], residues := [(2, 2444), (13, 3584), (47, 4116)] },
    { n := 4903, F := 4902, R := 1, a := 3, factors := [2, 3, 19, 43], residues := [(2, 2451), (3, 805), (19, 1009), (43, 788)] },
    { n := 4909, F := 4908, R := 1, a := 6, factors := [2, 2, 3, 409], residues := [(2, 2454), (3, 1827), (409, 322)] },
    { n := 4919, F := 4918, R := 1, a := 13, factors := [2, 2459], residues := [(2, 2459), (2459, 732)] },
    { n := 4931, F := 4930, R := 1, a := 6, factors := [2, 5, 17, 29], residues := [(2, 2465), (5, 3280), (17, 583), (29, 3570)] },
    { n := 4933, F := 4932, R := 1, a := 2, factors := [2, 2, 3, 3, 137], residues := [(2, 2466), (3, 4222), (137, 4175)] },
    { n := 4937, F := 4936, R := 1, a := 3, factors := [2, 2, 2, 617], residues := [(2, 2468), (617, 1089)] },
    { n := 4943, F := 4942, R := 1, a := 7, factors := [2, 7, 353], residues := [(2, 2471), (7, 3905), (353, 2315)] },
    { n := 4951, F := 4950, R := 1, a := 6, factors := [2, 3, 3, 5, 5, 11], residues := [(2, 2475), (3, 896), (5, 660), (11, 320)] },
    { n := 4957, F := 4956, R := 1, a := 2, factors := [2, 2, 3, 7, 59], residues := [(2, 2478), (3, 4065), (7, 4911), (59, 483)] },
    { n := 4967, F := 4966, R := 1, a := 5, factors := [2, 13, 191], residues := [(2, 2483), (13, 755), (191, 1551)] },
    { n := 4969, F := 4968, R := 1, a := 11, factors := [2, 2, 2, 3, 3, 3, 23], residues := [(2, 2484), (3, 1718), (23, 4585)] },
    { n := 4973, F := 4972, R := 1, a := 2, factors := [2, 2, 11, 113], residues := [(2, 2486), (11, 1889), (113, 604)] },
    { n := 4987, F := 4986, R := 1, a := 2, factors := [2, 3, 3, 277], residues := [(2, 2493), (3, 3703), (277, 835)] },
    { n := 4993, F := 4992, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 2, 3, 13], residues := [(2, 2496), (3, 4109), (13, 4169)] },
    { n := 4999, F := 4998, R := 1, a := 3, factors := [2, 3, 7, 7, 17], residues := [(2, 2499), (3, 2445), (7, 3517), (17, 3757)] },
    { n := 5003, F := 5002, R := 1, a := 2, factors := [2, 41, 61], residues := [(2, 2501), (41, 3107), (61, 4341)] },
    { n := 5009, F := 5008, R := 1, a := 3, factors := [2, 2, 2, 2, 313], residues := [(2, 2504), (313, 8)] },
    { n := 5011, F := 5010, R := 1, a := 2, factors := [2, 3, 5, 167], residues := [(2, 2505), (3, 2371), (5, 2745), (167, 604)] },
    { n := 5021, F := 5020, R := 1, a := 3, factors := [2, 2, 5, 251], residues := [(2, 2510), (5, 571), (251, 3545)] },
    { n := 5023, F := 5022, R := 1, a := 3, factors := [2, 3, 3, 3, 3, 31], residues := [(2, 2511), (3, 1356), (31, 4048)] },
    { n := 5039, F := 5038, R := 1, a := 11, factors := [2, 11, 229], residues := [(2, 2519), (11, 3953), (229, 874)] },
    { n := 5051, F := 5050, R := 1, a := 2, factors := [2, 5, 5, 101], residues := [(2, 2525), (5, 3446), (101, 2703)] },
    { n := 5059, F := 5058, R := 1, a := 2, factors := [2, 3, 3, 281], residues := [(2, 2529), (3, 637), (281, 3905)] },
    { n := 5077, F := 5076, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 47], residues := [(2, 2538), (3, 2235), (47, 3509)] },
    { n := 5081, F := 5080, R := 1, a := 3, factors := [2, 2, 2, 5, 127], residues := [(2, 2540), (5, 2336), (127, 2006)] },
    { n := 5087, F := 5086, R := 1, a := 5, factors := [2, 2543], residues := [(2, 2543), (2543, 212)] },
    { n := 5099, F := 5098, R := 1, a := 2, factors := [2, 2549], residues := [(2, 2549), (2549, 1700)] },
    { n := 5101, F := 5100, R := 1, a := 6, factors := [2, 2, 3, 5, 5, 17], residues := [(2, 2550), (3, 2238), (5, 4441), (17, 1688)] },
    { n := 5107, F := 5106, R := 1, a := 2, factors := [2, 3, 23, 37], residues := [(2, 2553), (3, 3508), (23, 298), (37, 4488)] },
    { n := 5113, F := 5112, R := 1, a := 19, factors := [2, 2, 2, 3, 3, 71], residues := [(2, 2556), (3, 3432), (71, 2372)] },
    { n := 5119, F := 5118, R := 1, a := 3, factors := [2, 3, 853], residues := [(2, 2559), (3, 1145), (853, 4451)] },
    { n := 5147, F := 5146, R := 1, a := 2, factors := [2, 31, 83], residues := [(2, 2573), (31, 1981), (83, 3958)] },
    { n := 5153, F := 5152, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 7, 23], residues := [(2, 2576), (7, 1229), (23, 3674)] },
    { n := 5167, F := 5166, R := 1, a := 6, factors := [2, 3, 3, 7, 41], residues := [(2, 2583), (3, 41), (7, 3224), (41, 1956)] },
    { n := 5171, F := 5170, R := 1, a := 2, factors := [2, 5, 11, 47], residues := [(2, 2585), (5, 3852), (11, 3760), (47, 2992)] },
    { n := 5179, F := 5178, R := 1, a := 2, factors := [2, 3, 863], residues := [(2, 2589), (3, 2953), (863, 2384)] },
    { n := 5189, F := 5188, R := 1, a := 2, factors := [2, 2, 1297], residues := [(2, 2594), (1297, 346)] },
    { n := 5197, F := 5196, R := 1, a := 7, factors := [2, 2, 3, 433], residues := [(2, 2598), (3, 2838), (433, 1148)] },
    { n := 5209, F := 5208, R := 1, a := 17, factors := [2, 2, 2, 3, 7, 31], residues := [(2, 2604), (3, 397), (7, 1458), (31, 4692)] },
    { n := 5227, F := 5226, R := 1, a := 2, factors := [2, 3, 13, 67], residues := [(2, 2613), (3, 5076), (13, 917), (67, 5132)] },
    { n := 5231, F := 5230, R := 1, a := 7, factors := [2, 5, 523], residues := [(2, 2615), (5, 2848), (523, 5034)] },
    { n := 5233, F := 5232, R := 1, a := 10, factors := [2, 2, 2, 2, 3, 109], residues := [(2, 2616), (3, 110), (109, 1956)] },
    { n := 5237, F := 5236, R := 1, a := 3, factors := [2, 2, 7, 11, 17], residues := [(2, 2618), (7, 276), (11, 1799), (17, 2657)] },
    { n := 5261, F := 5260, R := 1, a := 2, factors := [2, 2, 5, 263], residues := [(2, 2630), (5, 3505), (263, 4486)] },
    { n := 5273, F := 5272, R := 1, a := 3, factors := [2, 2, 2, 659], residues := [(2, 2636), (659, 4134)] },
    { n := 5279, F := 5278, R := 1, a := 7, factors := [2, 7, 13, 29], residues := [(2, 2639), (7, 2097), (13, 5198), (29, 1625)] },
    { n := 5281, F := 5280, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 3, 5, 11], residues := [(2, 2640), (3, 1292), (5, 1696), (11, 4317)] },
    { n := 5297, F := 5296, R := 1, a := 3, factors := [2, 2, 2, 2, 331], residues := [(2, 2648), (331, 3776)] },
    { n := 5303, F := 5302, R := 1, a := 5, factors := [2, 11, 241], residues := [(2, 2651), (11, 1881), (241, 5071)] },
    { n := 5309, F := 5308, R := 1, a := 2, factors := [2, 2, 1327], residues := [(2, 2654), (1327, 354)] },
    { n := 5323, F := 5322, R := 1, a := 5, factors := [2, 3, 887], residues := [(2, 2661), (3, 4895), (887, 108)] },
    { n := 5333, F := 5332, R := 1, a := 2, factors := [2, 2, 31, 43], residues := [(2, 2666), (31, 2862), (43, 587)] },
    { n := 5347, F := 5346, R := 1, a := 3, factors := [2, 3, 3, 3, 3, 3, 11], residues := [(2, 2673), (3, 3724), (11, 1863)] },
    { n := 5351, F := 5350, R := 1, a := 11, factors := [2, 5, 5, 107], residues := [(2, 2675), (5, 840), (107, 2396)] },
    { n := 5381, F := 5380, R := 1, a := 3, factors := [2, 2, 5, 269], residues := [(2, 2690), (5, 5247), (269, 427)] },
    { n := 5387, F := 5386, R := 1, a := 2, factors := [2, 2693], residues := [(2, 2693), (2693, 1796)] },
    { n := 5393, F := 5392, R := 1, a := 3, factors := [2, 2, 2, 2, 337], residues := [(2, 2696), (337, 1021)] },
    { n := 5399, F := 5398, R := 1, a := 7, factors := [2, 2699], residues := [(2, 2699), (2699, 2812)] },
    { n := 5407, F := 5406, R := 1, a := 3, factors := [2, 3, 17, 53], residues := [(2, 2703), (3, 347), (17, 4925), (53, 4042)] },
    { n := 5413, F := 5412, R := 1, a := 5, factors := [2, 2, 3, 11, 41], residues := [(2, 2706), (3, 3200), (11, 5066), (41, 1957)] },
    { n := 5417, F := 5416, R := 1, a := 3, factors := [2, 2, 2, 677], residues := [(2, 2708), (677, 1327)] },
    { n := 5419, F := 5418, R := 1, a := 3, factors := [2, 3, 3, 7, 43], residues := [(2, 2709), (3, 42), (7, 5333), (43, 4270)] },
    { n := 5431, F := 5430, R := 1, a := 3, factors := [2, 3, 5, 181], residues := [(2, 2715), (3, 2321), (5, 429), (181, 3566)] },
    { n := 5437, F := 5436, R := 1, a := 5, factors := [2, 2, 3, 3, 151], residues := [(2, 2718), (3, 2867), (151, 3113)] },
    { n := 5441, F := 5440, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 5, 17], residues := [(2, 2720), (5, 2168), (17, 4226)] },
    { n := 5443, F := 5442, R := 1, a := 2, factors := [2, 3, 907], residues := [(2, 2721), (3, 951), (907, 432)] },
    { n := 5449, F := 5448, R := 1, a := 7, factors := [2, 2, 2, 3, 227], residues := [(2, 2724), (3, 491), (227, 3591)] },
    { n := 5471, F := 5470, R := 1, a := 7, factors := [2, 5, 547], residues := [(2, 2735), (5, 285), (547, 4140)] },
    { n := 5477, F := 5476, R := 1, a := 2, factors := [2, 2, 37, 37], residues := [(2, 2738), (37, 4911)] },
    { n := 5479, F := 5478, R := 1, a := 3, factors := [2, 3, 11, 83], residues := [(2, 2739), (3, 925), (11, 3119), (83, 4626)] },
    { n := 5483, F := 5482, R := 1, a := 2, factors := [2, 2741], residues := [(2, 2741), (2741, 1828)] },
    { n := 5501, F := 5500, R := 1, a := 2, factors := [2, 2, 5, 5, 5, 11], residues := [(2, 2750), (5, 1127), (11, 2645)] },
    { n := 5503, F := 5502, R := 1, a := 3, factors := [2, 3, 7, 131], residues := [(2, 2751), (3, 3978), (7, 4163), (131, 2529)] },
    { n := 5507, F := 5506, R := 1, a := 2, factors := [2, 2753], residues := [(2, 2753), (2753, 1836)] },
    { n := 5519, F := 5518, R := 1, a := 13, factors := [2, 31, 89], residues := [(2, 2759), (31, 2745), (89, 943)] },
    { n := 5521, F := 5520, R := 1, a := 11, factors := [2, 2, 2, 2, 3, 5, 23], residues := [(2, 2760), (3, 113), (5, 571), (23, 2270)] },
    { n := 5527, F := 5526, R := 1, a := 5, factors := [2, 3, 3, 307], residues := [(2, 2763), (3, 3392), (307, 4760)] },
    { n := 5531, F := 5530, R := 1, a := 10, factors := [2, 5, 7, 79], residues := [(2, 2765), (5, 2080), (7, 2446), (79, 733)] },
    { n := 5557, F := 5556, R := 1, a := 2, factors := [2, 2, 3, 463], residues := [(2, 2778), (3, 3095), (463, 3972)] },
    { n := 5563, F := 5562, R := 1, a := 2, factors := [2, 3, 3, 3, 103], residues := [(2, 2781), (3, 3471), (103, 5473)] },
    { n := 5569, F := 5568, R := 1, a := 13, factors := [2, 2, 2, 2, 2, 2, 3, 29], residues := [(2, 2784), (3, 4821), (29, 996)] },
    { n := 5573, F := 5572, R := 1, a := 2, factors := [2, 2, 7, 199], residues := [(2, 2786), (7, 388), (199, 3319)] },
    { n := 5581, F := 5580, R := 1, a := 6, factors := [2, 2, 3, 3, 5, 31], residues := [(2, 2790), (3, 4761), (5, 3507), (31, 2354)] },
    { n := 5591, F := 5590, R := 1, a := 11, factors := [2, 5, 13, 43], residues := [(2, 2795), (5, 4696), (13, 3478), (43, 1124)] },
    { n := 5623, F := 5622, R := 1, a := 5, factors := [2, 3, 937], residues := [(2, 2811), (3, 3077), (937, 2606)] },
    { n := 5639, F := 5638, R := 1, a := 7, factors := [2, 2819], residues := [(2, 2819), (2819, 2937)] },
    { n := 5641, F := 5640, R := 1, a := 14, factors := [2, 2, 2, 3, 5, 47], residues := [(2, 2820), (3, 681), (5, 4332), (47, 977)] },
    { n := 5647, F := 5646, R := 1, a := 3, factors := [2, 3, 941], residues := [(2, 2823), (3, 5362), (941, 3669)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData03_valid : PocklingtonRow.Valid lowPocklingtonData03 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime03 (i : Fin lowPocklingtonData03.length) :
    Nat.Prime (lowPocklingtonData03.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData03_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4813) (q := 4817) (by
      have hp := lowPocklingtonPrime03 ⟨0, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4817) (q := 4831) (by
      have hp := lowPocklingtonPrime03 ⟨1, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4831) (q := 4861) (by
      have hp := lowPocklingtonPrime03 ⟨2, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4861) (q := 4871) (by
      have hp := lowPocklingtonPrime03 ⟨3, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4871) (q := 4877) (by
      have hp := lowPocklingtonPrime03 ⟨4, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4877) (q := 4889) (by
      have hp := lowPocklingtonPrime03 ⟨5, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4889) (q := 4903) (by
      have hp := lowPocklingtonPrime03 ⟨6, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4903) (q := 4909) (by
      have hp := lowPocklingtonPrime03 ⟨7, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part03_chain :
    DusartPrimeRowsChain 4813 4908 dusartPrimeRows_4673_4918_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4914, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4909) (q := 4919) (by
      have hp := lowPocklingtonPrime03 ⟨8, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part04_chain :
    DusartPrimeRowsChain 4909 4918 dusartPrimeRows_4673_4918_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_4914, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 4919) (q := 4931) (by
      have hp := lowPocklingtonPrime03 ⟨9, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4931) (q := 4933) (by
      have hp := lowPocklingtonPrime03 ⟨10, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4933) (q := 4937) (by
      have hp := lowPocklingtonPrime03 ⟨11, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4937) (q := 4943) (by
      have hp := lowPocklingtonPrime03 ⟨12, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4943) (q := 4951) (by
      have hp := lowPocklingtonPrime03 ⟨13, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4951) (q := 4957) (by
      have hp := lowPocklingtonPrime03 ⟨14, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4957) (q := 4967) (by
      have hp := lowPocklingtonPrime03 ⟨15, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4967) (q := 4969) (by
      have hp := lowPocklingtonPrime03 ⟨16, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part01_chain :
    DusartPrimeRowsChain 4919 4968 dusartPrimeRows_4919_5166_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5166, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 4969) (q := 4973) (by
      have hp := lowPocklingtonPrime03 ⟨17, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4973) (q := 4987) (by
      have hp := lowPocklingtonPrime03 ⟨18, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4987) (q := 4993) (by
      have hp := lowPocklingtonPrime03 ⟨19, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4993) (q := 4999) (by
      have hp := lowPocklingtonPrime03 ⟨20, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4999) (q := 5003) (by
      have hp := lowPocklingtonPrime03 ⟨21, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5003) (q := 5009) (by
      have hp := lowPocklingtonPrime03 ⟨22, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5009) (q := 5011) (by
      have hp := lowPocklingtonPrime03 ⟨23, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5011) (q := 5021) (by
      have hp := lowPocklingtonPrime03 ⟨24, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part02_chain :
    DusartPrimeRowsChain 4969 5020 dusartPrimeRows_4919_5166_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5166, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 5021) (q := 5023) (by
      have hp := lowPocklingtonPrime03 ⟨25, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5023) (q := 5039) (by
      have hp := lowPocklingtonPrime03 ⟨26, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5039) (q := 5051) (by
      have hp := lowPocklingtonPrime03 ⟨27, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5051) (q := 5059) (by
      have hp := lowPocklingtonPrime03 ⟨28, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5059) (q := 5077) (by
      have hp := lowPocklingtonPrime03 ⟨29, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5077) (q := 5081) (by
      have hp := lowPocklingtonPrime03 ⟨30, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5081) (q := 5087) (by
      have hp := lowPocklingtonPrime03 ⟨31, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5087) (q := 5099) (by
      have hp := lowPocklingtonPrime03 ⟨32, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part03_chain :
    DusartPrimeRowsChain 5021 5098 dusartPrimeRows_4919_5166_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5166, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 5099) (q := 5101) (by
      have hp := lowPocklingtonPrime03 ⟨33, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5101) (q := 5107) (by
      have hp := lowPocklingtonPrime03 ⟨34, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5107) (q := 5113) (by
      have hp := lowPocklingtonPrime03 ⟨35, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5113) (q := 5119) (by
      have hp := lowPocklingtonPrime03 ⟨36, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5119) (q := 5147) (by
      have hp := lowPocklingtonPrime03 ⟨37, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5147) (q := 5153) (by
      have hp := lowPocklingtonPrime03 ⟨38, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5153) (q := 5167) (by
      have hp := lowPocklingtonPrime03 ⟨39, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part04_chain :
    DusartPrimeRowsChain 5099 5166 dusartPrimeRows_4919_5166_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_5166, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5167) (q := 5171) (by
      have hp := lowPocklingtonPrime03 ⟨40, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5171) (q := 5179) (by
      have hp := lowPocklingtonPrime03 ⟨41, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5179) (q := 5189) (by
      have hp := lowPocklingtonPrime03 ⟨42, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5189) (q := 5197) (by
      have hp := lowPocklingtonPrime03 ⟨43, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5197) (q := 5209) (by
      have hp := lowPocklingtonPrime03 ⟨44, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5209) (q := 5227) (by
      have hp := lowPocklingtonPrime03 ⟨45, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5227) (q := 5231) (by
      have hp := lowPocklingtonPrime03 ⟨46, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5231) (q := 5233) (by
      have hp := lowPocklingtonPrime03 ⟨47, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part01_chain :
    DusartPrimeRowsChain 5167 5232 dusartPrimeRows_5167_5436_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5431, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5233) (q := 5237) (by
      have hp := lowPocklingtonPrime03 ⟨48, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5237) (q := 5261) (by
      have hp := lowPocklingtonPrime03 ⟨49, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5261) (q := 5273) (by
      have hp := lowPocklingtonPrime03 ⟨50, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5273) (q := 5279) (by
      have hp := lowPocklingtonPrime03 ⟨51, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5279) (q := 5281) (by
      have hp := lowPocklingtonPrime03 ⟨52, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5281) (q := 5297) (by
      have hp := lowPocklingtonPrime03 ⟨53, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5297) (q := 5303) (by
      have hp := lowPocklingtonPrime03 ⟨54, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5303) (q := 5309) (by
      have hp := lowPocklingtonPrime03 ⟨55, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part02_chain :
    DusartPrimeRowsChain 5233 5308 dusartPrimeRows_5167_5436_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5431, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5309) (q := 5323) (by
      have hp := lowPocklingtonPrime03 ⟨56, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5323) (q := 5333) (by
      have hp := lowPocklingtonPrime03 ⟨57, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5333) (q := 5347) (by
      have hp := lowPocklingtonPrime03 ⟨58, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5347) (q := 5351) (by
      have hp := lowPocklingtonPrime03 ⟨59, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5351) (q := 5381) (by
      have hp := lowPocklingtonPrime03 ⟨60, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5381) (q := 5387) (by
      have hp := lowPocklingtonPrime03 ⟨61, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5387) (q := 5393) (by
      have hp := lowPocklingtonPrime03 ⟨62, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5393) (q := 5399) (by
      have hp := lowPocklingtonPrime03 ⟨63, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part03_chain :
    DusartPrimeRowsChain 5309 5398 dusartPrimeRows_5167_5436_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5431, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5399) (q := 5407) (by
      have hp := lowPocklingtonPrime03 ⟨64, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5407) (q := 5413) (by
      have hp := lowPocklingtonPrime03 ⟨65, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5413) (q := 5417) (by
      have hp := lowPocklingtonPrime03 ⟨66, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5417) (q := 5419) (by
      have hp := lowPocklingtonPrime03 ⟨67, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5419) (q := 5431) (by
      have hp := lowPocklingtonPrime03 ⟨68, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5431) (q := 5437) (by
      have hp := lowPocklingtonPrime03 ⟨69, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part04_chain :
    DusartPrimeRowsChain 5399 5436 dusartPrimeRows_5167_5436_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_5431, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5437) (q := 5441) (by
      have hp := lowPocklingtonPrime03 ⟨70, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5441) (q := 5443) (by
      have hp := lowPocklingtonPrime03 ⟨71, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5443) (q := 5449) (by
      have hp := lowPocklingtonPrime03 ⟨72, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5449) (q := 5471) (by
      have hp := lowPocklingtonPrime03 ⟨73, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5471) (q := 5477) (by
      have hp := lowPocklingtonPrime03 ⟨74, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5477) (q := 5479) (by
      have hp := lowPocklingtonPrime03 ⟨75, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5479) (q := 5483) (by
      have hp := lowPocklingtonPrime03 ⟨76, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5483) (q := 5501) (by
      have hp := lowPocklingtonPrime03 ⟨77, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part01_chain :
    DusartPrimeRowsChain 5437 5500 dusartPrimeRows_5437_5710_part01 := by
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
def dusartPrimeRows_5437_5710_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5501) (q := 5503) (by
      have hp := lowPocklingtonPrime03 ⟨78, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5503) (q := 5507) (by
      have hp := lowPocklingtonPrime03 ⟨79, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5507) (q := 5519) (by
      have hp := lowPocklingtonPrime03 ⟨80, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5519) (q := 5521) (by
      have hp := lowPocklingtonPrime03 ⟨81, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5521) (q := 5527) (by
      have hp := lowPocklingtonPrime03 ⟨82, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5527) (q := 5531) (by
      have hp := lowPocklingtonPrime03 ⟨83, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5531) (q := 5557) (by
      have hp := lowPocklingtonPrime03 ⟨84, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5557) (q := 5563) (by
      have hp := lowPocklingtonPrime03 ⟨85, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part02_chain :
    DusartPrimeRowsChain 5501 5562 dusartPrimeRows_5437_5710_part02 := by
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
def dusartPrimeRows_5437_5710_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5563) (q := 5569) (by
      have hp := lowPocklingtonPrime03 ⟨86, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5569) (q := 5573) (by
      have hp := lowPocklingtonPrime03 ⟨87, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5573) (q := 5581) (by
      have hp := lowPocklingtonPrime03 ⟨88, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5581) (q := 5591) (by
      have hp := lowPocklingtonPrime03 ⟨89, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5591) (q := 5623) (by
      have hp := lowPocklingtonPrime03 ⟨90, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5623) (q := 5639) (by
      have hp := lowPocklingtonPrime03 ⟨91, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5639) (q := 5641) (by
      have hp := lowPocklingtonPrime03 ⟨92, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5641) (q := 5647) (by
      have hp := lowPocklingtonPrime03 ⟨93, by simp [lowPocklingtonData03]⟩
      simpa [lowPocklingtonData03] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part03_chain :
    DusartPrimeRowsChain 5563 5646 dusartPrimeRows_5437_5710_part03 := by
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
