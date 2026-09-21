import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart12


set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 13 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData13 : List PocklingtonData := [
    { n := 13249, F := 13248, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 3, 3, 23], residues := [(2, 6624), (3, 1069), (23, 11912)] },
    { n := 13259, F := 13258, R := 1, a := 6, factors := [2, 7, 947], residues := [(2, 6629), (7, 9405), (947, 4084)] },
    { n := 13267, F := 13266, R := 1, a := 3, factors := [2, 3, 3, 11, 67], residues := [(2, 6633), (3, 13200), (11, 5898), (67, 12133)] },
    { n := 13291, F := 13290, R := 1, a := 2, factors := [2, 3, 5, 443], residues := [(2, 6645), (3, 5512), (5, 8444), (443, 6881)] },
    { n := 13297, F := 13296, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 277], residues := [(2, 6648), (3, 3632), (277, 1776)] },
    { n := 13309, F := 13308, R := 1, a := 6, factors := [2, 2, 3, 1109], residues := [(2, 6654), (3, 7171), (1109, 10416)] },
    { n := 13313, F := 13312, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13], residues := [(2, 6656), (13, 11517)] },
    { n := 13327, F := 13326, R := 1, a := 3, factors := [2, 3, 2221], residues := [(2, 6663), (3, 12279), (2221, 11295)] },
    { n := 13331, F := 13330, R := 1, a := 2, factors := [2, 5, 31, 43], residues := [(2, 6665), (5, 8391), (31, 4902), (43, 1349)] },
    { n := 13337, F := 13336, R := 1, a := 3, factors := [2, 2, 2, 1667], residues := [(2, 6668), (1667, 12538)] },
    { n := 13339, F := 13338, R := 1, a := 2, factors := [2, 3, 3, 3, 13, 19], residues := [(2, 6669), (3, 10196), (13, 5147), (19, 2731)] },
    { n := 13367, F := 13366, R := 1, a := 5, factors := [2, 41, 163], residues := [(2, 6683), (41, 11901), (163, 566)] },
    { n := 13381, F := 13380, R := 1, a := 10, factors := [2, 2, 3, 5, 223], residues := [(2, 6690), (3, 467), (5, 3923), (223, 12699)] },
    { n := 13397, F := 13396, R := 1, a := 2, factors := [2, 2, 17, 197], residues := [(2, 6698), (17, 7020), (197, 9128)] },
    { n := 13399, F := 13398, R := 1, a := 3, factors := [2, 3, 7, 11, 29], residues := [(2, 6699), (3, 3492), (7, 3265), (11, 10715), (29, 377)] },
    { n := 13411, F := 13410, R := 1, a := 2, factors := [2, 3, 3, 5, 149], residues := [(2, 6705), (3, 12752), (5, 950), (149, 7784)] },
    { n := 13417, F := 13416, R := 1, a := 5, factors := [2, 2, 2, 3, 13, 43], residues := [(2, 6708), (3, 8108), (13, 10793), (43, 7977)] },
    { n := 13421, F := 13420, R := 1, a := 10, factors := [2, 2, 5, 11, 61], residues := [(2, 6710), (5, 2125), (11, 8581), (61, 12494)] },
    { n := 13441, F := 13440, R := 1, a := 11, factors := [2, 2, 2, 2, 2, 2, 2, 3, 5, 7], residues := [(2, 6720), (3, 8745), (5, 1156), (7, 1552)] },
    { n := 13451, F := 13450, R := 1, a := 2, factors := [2, 5, 5, 269], residues := [(2, 6725), (5, 3205), (269, 9663)] },
    { n := 13457, F := 13456, R := 1, a := 3, factors := [2, 2, 2, 2, 29, 29], residues := [(2, 6728), (29, 3592)] },
    { n := 13463, F := 13462, R := 1, a := 5, factors := [2, 53, 127], residues := [(2, 6731), (53, 9892), (127, 2431)] },
    { n := 13469, F := 13468, R := 1, a := 2, factors := [2, 2, 7, 13, 37], residues := [(2, 6734), (7, 11139), (13, 1940), (37, 11931)] },
    { n := 13477, F := 13476, R := 1, a := 2, factors := [2, 2, 3, 1123], residues := [(2, 6738), (3, 3715), (1123, 11114)] },
    { n := 13487, F := 13486, R := 1, a := 5, factors := [2, 11, 613], residues := [(2, 6743), (11, 2090), (613, 5074)] },
    { n := 13499, F := 13498, R := 1, a := 6, factors := [2, 17, 397], residues := [(2, 6749), (17, 9088), (397, 10134)] },
    { n := 13513, F := 13512, R := 1, a := 5, factors := [2, 2, 2, 3, 563], residues := [(2, 6756), (3, 6369), (563, 3665)] },
    { n := 13523, F := 13522, R := 1, a := 2, factors := [2, 6761], residues := [(2, 6761), (6761, 4508)] },
    { n := 13537, F := 13536, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 3, 3, 47], residues := [(2, 6768), (3, 4372), (47, 10420)] },
    { n := 13553, F := 13552, R := 1, a := 3, factors := [2, 2, 2, 2, 7, 11, 11], residues := [(2, 6776), (7, 13202), (11, 7638)] },
    { n := 13567, F := 13566, R := 1, a := 3, factors := [2, 3, 7, 17, 19], residues := [(2, 6783), (3, 6108), (7, 11095), (17, 11924), (19, 1212)] },
    { n := 13577, F := 13576, R := 1, a := 3, factors := [2, 2, 2, 1697], residues := [(2, 6788), (1697, 7962)] },
    { n := 13591, F := 13590, R := 1, a := 3, factors := [2, 3, 3, 5, 151], residues := [(2, 6795), (3, 3616), (5, 5994), (151, 3859)] },
    { n := 13597, F := 13596, R := 1, a := 5, factors := [2, 2, 3, 11, 103], residues := [(2, 6798), (3, 12120), (11, 3813), (103, 5587)] },
    { n := 13613, F := 13612, R := 1, a := 2, factors := [2, 2, 41, 83], residues := [(2, 6806), (41, 983), (83, 10062)] },
    { n := 13619, F := 13618, R := 1, a := 2, factors := [2, 11, 619], residues := [(2, 6809), (11, 10229), (619, 5112)] },
    { n := 13627, F := 13626, R := 1, a := 2, factors := [2, 3, 3, 757], residues := [(2, 6813), (3, 3467), (757, 12644)] },
    { n := 13633, F := 13632, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 3, 71], residues := [(2, 6816), (3, 5558), (71, 6864)] },
    { n := 13649, F := 13648, R := 1, a := 3, factors := [2, 2, 2, 2, 853], residues := [(2, 6824), (853, 10295)] },
    { n := 13669, F := 13668, R := 1, a := 6, factors := [2, 2, 3, 17, 67], residues := [(2, 6834), (3, 13601), (17, 13158), (67, 8361)] },
    { n := 13679, F := 13678, R := 1, a := 7, factors := [2, 7, 977], residues := [(2, 6839), (7, 9533), (977, 13325)] },
    { n := 13681, F := 13680, R := 1, a := 22, factors := [2, 2, 2, 2, 3, 3, 5, 19], residues := [(2, 6840), (3, 3918), (5, 7899), (19, 9620)] },
    { n := 13687, F := 13686, R := 1, a := 3, factors := [2, 3, 2281], residues := [(2, 6843), (3, 3670), (2281, 4531)] },
    { n := 13691, F := 13690, R := 1, a := 2, factors := [2, 5, 37, 37], residues := [(2, 6845), (5, 12768), (37, 1626)] },
    { n := 13693, F := 13692, R := 1, a := 6, factors := [2, 2, 3, 7, 163], residues := [(2, 6846), (3, 3561), (7, 12349), (163, 5523)] },
    { n := 13697, F := 13696, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 107], residues := [(2, 6848), (107, 1923)] },
    { n := 13709, F := 13708, R := 1, a := 2, factors := [2, 2, 23, 149], residues := [(2, 6854), (23, 11514), (149, 9931)] },
    { n := 13711, F := 13710, R := 1, a := 6, factors := [2, 3, 5, 457], residues := [(2, 6855), (3, 1049), (5, 2811), (457, 597)] },
    { n := 13721, F := 13720, R := 1, a := 3, factors := [2, 2, 2, 5, 7, 7, 7], residues := [(2, 6860), (5, 10624), (7, 5353)] },
    { n := 13723, F := 13722, R := 1, a := 2, factors := [2, 3, 2287], residues := [(2, 6861), (3, 3857), (2287, 5010)] },
    { n := 13729, F := 13728, R := 1, a := 23, factors := [2, 2, 2, 2, 2, 3, 11, 13], residues := [(2, 6864), (3, 2236), (11, 12927), (13, 294)] },
    { n := 13751, F := 13750, R := 1, a := 11, factors := [2, 5, 5, 5, 5, 11], residues := [(2, 6875), (5, 1728), (11, 5381)] },
    { n := 13757, F := 13756, R := 1, a := 2, factors := [2, 2, 19, 181], residues := [(2, 6878), (19, 9457), (181, 10755)] },
    { n := 13759, F := 13758, R := 1, a := 6, factors := [2, 3, 2293], residues := [(2, 6879), (3, 4348), (2293, 1205)] },
    { n := 13763, F := 13762, R := 1, a := 2, factors := [2, 7, 983], residues := [(2, 6881), (7, 5661), (983, 3010)] },
    { n := 13781, F := 13780, R := 1, a := 7, factors := [2, 2, 5, 13, 53], residues := [(2, 6890), (5, 12442), (13, 5898), (53, 12205)] },
    { n := 13789, F := 13788, R := 1, a := 7, factors := [2, 2, 3, 3, 383], residues := [(2, 6894), (3, 10001), (383, 3274)] },
    { n := 13799, F := 13798, R := 1, a := 7, factors := [2, 6899], residues := [(2, 6899), (6899, 7187)] },
    { n := 13807, F := 13806, R := 1, a := 5, factors := [2, 3, 3, 13, 59], residues := [(2, 6903), (3, 9165), (13, 717), (59, 519)] },
    { n := 13829, F := 13828, R := 1, a := 2, factors := [2, 2, 3457], residues := [(2, 6914), (3457, 922)] },
    { n := 13831, F := 13830, R := 1, a := 6, factors := [2, 3, 5, 461], residues := [(2, 6915), (3, 3865), (5, 6077), (461, 6886)] },
    { n := 13841, F := 13840, R := 1, a := 6, factors := [2, 2, 2, 2, 5, 173], residues := [(2, 6920), (5, 9806), (173, 11066)] },
    { n := 13859, F := 13858, R := 1, a := 2, factors := [2, 13, 13, 41], residues := [(2, 6929), (13, 5554), (41, 4087)] },
    { n := 13873, F := 13872, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 17, 17], residues := [(2, 6936), (3, 6970), (17, 4982)] },
    { n := 13877, F := 13876, R := 1, a := 2, factors := [2, 2, 3469], residues := [(2, 6938), (3469, 6476)] },
    { n := 13879, F := 13878, R := 1, a := 6, factors := [2, 3, 3, 3, 257], residues := [(2, 6939), (3, 12919), (257, 8004)] },
    { n := 13883, F := 13882, R := 1, a := 2, factors := [2, 11, 631], residues := [(2, 6941), (11, 12425), (631, 441)] },
    { n := 13901, F := 13900, R := 1, a := 2, factors := [2, 2, 5, 5, 139], residues := [(2, 6950), (5, 7565), (139, 436)] },
    { n := 13903, F := 13902, R := 1, a := 3, factors := [2, 3, 7, 331], residues := [(2, 6951), (3, 4415), (7, 8438), (331, 3786)] },
    { n := 13907, F := 13906, R := 1, a := 2, factors := [2, 17, 409], residues := [(2, 6953), (17, 563), (409, 13516)] },
    { n := 13913, F := 13912, R := 1, a := 3, factors := [2, 2, 2, 37, 47], residues := [(2, 6956), (37, 13008), (47, 9566)] },
    { n := 13921, F := 13920, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 3, 5, 29], residues := [(2, 6960), (3, 12931), (5, 6717), (29, 648)] },
    { n := 13931, F := 13930, R := 1, a := 2, factors := [2, 5, 7, 199], residues := [(2, 6965), (5, 6123), (7, 4477), (199, 8941)] },
    { n := 13933, F := 13932, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 3, 43], residues := [(2, 6966), (3, 711), (43, 5120)] },
    { n := 13963, F := 13962, R := 1, a := 3, factors := [2, 3, 13, 179], residues := [(2, 6981), (3, 180), (13, 1535), (179, 10323)] },
    { n := 13967, F := 13966, R := 1, a := 5, factors := [2, 6983], residues := [(2, 6983), (6983, 582)] },
    { n := 13997, F := 13996, R := 1, a := 2, factors := [2, 2, 3499], residues := [(2, 6998), (3499, 6532)] },
    { n := 13999, F := 13998, R := 1, a := 3, factors := [2, 3, 2333], residues := [(2, 6999), (3, 10736), (2333, 8634)] },
    { n := 14009, F := 14008, R := 1, a := 3, factors := [2, 2, 2, 17, 103], residues := [(2, 7004), (17, 10252), (103, 8325)] },
    { n := 14011, F := 14010, R := 1, a := 2, factors := [2, 3, 5, 467], residues := [(2, 7005), (3, 13630), (5, 7782), (467, 13277)] },
    { n := 14029, F := 14028, R := 1, a := 6, factors := [2, 2, 3, 7, 167], residues := [(2, 7014), (3, 11088), (7, 12344), (167, 3017)] },
    { n := 14033, F := 14032, R := 1, a := 3, factors := [2, 2, 2, 2, 877], residues := [(2, 7016), (877, 7565)] },
    { n := 14051, F := 14050, R := 1, a := 2, factors := [2, 5, 5, 281], residues := [(2, 7025), (5, 10400), (281, 2225)] },
    { n := 14057, F := 14056, R := 1, a := 3, factors := [2, 2, 2, 7, 251], residues := [(2, 7028), (7, 7520), (251, 12163)] },
    { n := 14071, F := 14070, R := 1, a := 7, factors := [2, 3, 5, 7, 67], residues := [(2, 7035), (3, 9718), (5, 1196), (7, 10307), (67, 8635)] },
    { n := 14081, F := 14080, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 2, 5, 11], residues := [(2, 7040), (5, 9826), (11, 5154)] },
    { n := 14083, F := 14082, R := 1, a := 3, factors := [2, 3, 2347], residues := [(2, 7041), (3, 8463), (2347, 561)] },
    { n := 14087, F := 14086, R := 1, a := 5, factors := [2, 7043], residues := [(2, 7043), (7043, 587)] },
    { n := 14107, F := 14106, R := 1, a := 2, factors := [2, 3, 2351], residues := [(2, 7053), (3, 6418), (2351, 8509)] },
    { n := 14143, F := 14142, R := 1, a := 3, factors := [2, 3, 2357], residues := [(2, 7071), (3, 2990), (2357, 12142)] },
    { n := 14149, F := 14148, R := 1, a := 6, factors := [2, 2, 3, 3, 3, 131], residues := [(2, 7074), (3, 9983), (131, 1348)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData13_valid : PocklingtonRow.Valid lowPocklingtonData13 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime13 (i : Fin lowPocklingtonData13.length) :
    Nat.Prime (lowPocklingtonData13.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData13_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13241) (q := 13249) (by
      have hp := lowPocklingtonPrime13 ⟨0, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13249) (q := 13259) (by
      have hp := lowPocklingtonPrime13 ⟨1, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13259) (q := 13267) (by
      have hp := lowPocklingtonPrime13 ⟨2, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13267) (q := 13291) (by
      have hp := lowPocklingtonPrime13 ⟨3, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13291) (q := 13297) (by
      have hp := lowPocklingtonPrime13 ⟨4, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13297) (q := 13309) (by
      have hp := lowPocklingtonPrime13 ⟨5, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13309) (q := 13313) (by
      have hp := lowPocklingtonPrime13 ⟨6, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13313) (q := 13327) (by
      have hp := lowPocklingtonPrime13 ⟨7, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part08_chain :
    DusartPrimeRowsChain 13241 13326 dusartPrimeRows_12713_13366_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_13359, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13327) (q := 13331) (by
      have hp := lowPocklingtonPrime13 ⟨8, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13331) (q := 13337) (by
      have hp := lowPocklingtonPrime13 ⟨9, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13337) (q := 13339) (by
      have hp := lowPocklingtonPrime13 ⟨10, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13339) (q := 13367) (by
      have hp := lowPocklingtonPrime13 ⟨11, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part09_chain :
    DusartPrimeRowsChain 13327 13366 dusartPrimeRows_12713_13366_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · apply DusartPrimeRowsChain.empty
          norm_num [dusartPrimeRow_of_explicit_13359, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13367) (q := 13381) (by
      have hp := lowPocklingtonPrime13 ⟨12, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13381) (q := 13397) (by
      have hp := lowPocklingtonPrime13 ⟨13, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13397) (q := 13399) (by
      have hp := lowPocklingtonPrime13 ⟨14, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13399) (q := 13411) (by
      have hp := lowPocklingtonPrime13 ⟨15, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13411) (q := 13417) (by
      have hp := lowPocklingtonPrime13 ⟨16, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13417) (q := 13421) (by
      have hp := lowPocklingtonPrime13 ⟨17, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13421) (q := 13441) (by
      have hp := lowPocklingtonPrime13 ⟨18, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13441) (q := 13451) (by
      have hp := lowPocklingtonPrime13 ⟨19, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part01_chain :
    DusartPrimeRowsChain 13367 13450 dusartPrimeRows_13367_14050_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13451) (q := 13457) (by
      have hp := lowPocklingtonPrime13 ⟨20, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13457) (q := 13463) (by
      have hp := lowPocklingtonPrime13 ⟨21, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13463) (q := 13469) (by
      have hp := lowPocklingtonPrime13 ⟨22, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13469) (q := 13477) (by
      have hp := lowPocklingtonPrime13 ⟨23, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13477) (q := 13487) (by
      have hp := lowPocklingtonPrime13 ⟨24, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13487) (q := 13499) (by
      have hp := lowPocklingtonPrime13 ⟨25, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13499) (q := 13513) (by
      have hp := lowPocklingtonPrime13 ⟨26, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13513) (q := 13523) (by
      have hp := lowPocklingtonPrime13 ⟨27, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part02_chain :
    DusartPrimeRowsChain 13451 13522 dusartPrimeRows_13367_14050_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13523) (q := 13537) (by
      have hp := lowPocklingtonPrime13 ⟨28, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13537) (q := 13553) (by
      have hp := lowPocklingtonPrime13 ⟨29, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13553) (q := 13567) (by
      have hp := lowPocklingtonPrime13 ⟨30, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13567) (q := 13577) (by
      have hp := lowPocklingtonPrime13 ⟨31, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13577) (q := 13591) (by
      have hp := lowPocklingtonPrime13 ⟨32, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13591) (q := 13597) (by
      have hp := lowPocklingtonPrime13 ⟨33, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13597) (q := 13613) (by
      have hp := lowPocklingtonPrime13 ⟨34, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13613) (q := 13619) (by
      have hp := lowPocklingtonPrime13 ⟨35, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part03_chain :
    DusartPrimeRowsChain 13523 13618 dusartPrimeRows_13367_14050_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13619) (q := 13627) (by
      have hp := lowPocklingtonPrime13 ⟨36, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13627) (q := 13633) (by
      have hp := lowPocklingtonPrime13 ⟨37, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13633) (q := 13649) (by
      have hp := lowPocklingtonPrime13 ⟨38, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13649) (q := 13669) (by
      have hp := lowPocklingtonPrime13 ⟨39, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13669) (q := 13679) (by
      have hp := lowPocklingtonPrime13 ⟨40, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13679) (q := 13681) (by
      have hp := lowPocklingtonPrime13 ⟨41, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13681) (q := 13687) (by
      have hp := lowPocklingtonPrime13 ⟨42, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13687) (q := 13691) (by
      have hp := lowPocklingtonPrime13 ⟨43, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part04_chain :
    DusartPrimeRowsChain 13619 13690 dusartPrimeRows_13367_14050_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13691) (q := 13693) (by
      have hp := lowPocklingtonPrime13 ⟨44, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13693) (q := 13697) (by
      have hp := lowPocklingtonPrime13 ⟨45, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13697) (q := 13709) (by
      have hp := lowPocklingtonPrime13 ⟨46, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13709) (q := 13711) (by
      have hp := lowPocklingtonPrime13 ⟨47, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13711) (q := 13721) (by
      have hp := lowPocklingtonPrime13 ⟨48, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13721) (q := 13723) (by
      have hp := lowPocklingtonPrime13 ⟨49, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13723) (q := 13729) (by
      have hp := lowPocklingtonPrime13 ⟨50, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13729) (q := 13751) (by
      have hp := lowPocklingtonPrime13 ⟨51, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part05_chain :
    DusartPrimeRowsChain 13691 13750 dusartPrimeRows_13367_14050_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13751) (q := 13757) (by
      have hp := lowPocklingtonPrime13 ⟨52, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13757) (q := 13759) (by
      have hp := lowPocklingtonPrime13 ⟨53, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13759) (q := 13763) (by
      have hp := lowPocklingtonPrime13 ⟨54, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13763) (q := 13781) (by
      have hp := lowPocklingtonPrime13 ⟨55, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13781) (q := 13789) (by
      have hp := lowPocklingtonPrime13 ⟨56, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13789) (q := 13799) (by
      have hp := lowPocklingtonPrime13 ⟨57, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13799) (q := 13807) (by
      have hp := lowPocklingtonPrime13 ⟨58, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13807) (q := 13829) (by
      have hp := lowPocklingtonPrime13 ⟨59, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part06_chain :
    DusartPrimeRowsChain 13751 13828 dusartPrimeRows_13367_14050_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13829) (q := 13831) (by
      have hp := lowPocklingtonPrime13 ⟨60, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13831) (q := 13841) (by
      have hp := lowPocklingtonPrime13 ⟨61, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13841) (q := 13859) (by
      have hp := lowPocklingtonPrime13 ⟨62, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13859) (q := 13873) (by
      have hp := lowPocklingtonPrime13 ⟨63, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13873) (q := 13877) (by
      have hp := lowPocklingtonPrime13 ⟨64, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13877) (q := 13879) (by
      have hp := lowPocklingtonPrime13 ⟨65, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13879) (q := 13883) (by
      have hp := lowPocklingtonPrime13 ⟨66, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13883) (q := 13901) (by
      have hp := lowPocklingtonPrime13 ⟨67, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part07_chain :
    DusartPrimeRowsChain 13829 13900 dusartPrimeRows_13367_14050_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13901) (q := 13903) (by
      have hp := lowPocklingtonPrime13 ⟨68, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13903) (q := 13907) (by
      have hp := lowPocklingtonPrime13 ⟨69, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13907) (q := 13913) (by
      have hp := lowPocklingtonPrime13 ⟨70, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13913) (q := 13921) (by
      have hp := lowPocklingtonPrime13 ⟨71, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13921) (q := 13931) (by
      have hp := lowPocklingtonPrime13 ⟨72, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13931) (q := 13933) (by
      have hp := lowPocklingtonPrime13 ⟨73, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13933) (q := 13963) (by
      have hp := lowPocklingtonPrime13 ⟨74, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13963) (q := 13967) (by
      have hp := lowPocklingtonPrime13 ⟨75, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part08_chain :
    DusartPrimeRowsChain 13901 13966 dusartPrimeRows_13367_14050_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13967) (q := 13997) (by
      have hp := lowPocklingtonPrime13 ⟨76, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13997) (q := 13999) (by
      have hp := lowPocklingtonPrime13 ⟨77, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13999) (q := 14009) (by
      have hp := lowPocklingtonPrime13 ⟨78, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14009) (q := 14011) (by
      have hp := lowPocklingtonPrime13 ⟨79, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14011) (q := 14029) (by
      have hp := lowPocklingtonPrime13 ⟨80, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14029) (q := 14033) (by
      have hp := lowPocklingtonPrime13 ⟨81, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 14033) (q := 14051) (by
      have hp := lowPocklingtonPrime13 ⟨82, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part09_chain :
    DusartPrimeRowsChain 13967 14050 dusartPrimeRows_13367_14050_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14051) (q := 14057) (by
      have hp := lowPocklingtonPrime13 ⟨83, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14057) (q := 14071) (by
      have hp := lowPocklingtonPrime13 ⟨84, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14071) (q := 14081) (by
      have hp := lowPocklingtonPrime13 ⟨85, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14081) (q := 14083) (by
      have hp := lowPocklingtonPrime13 ⟨86, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14083) (q := 14087) (by
      have hp := lowPocklingtonPrime13 ⟨87, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14087) (q := 14107) (by
      have hp := lowPocklingtonPrime13 ⟨88, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14107) (q := 14143) (by
      have hp := lowPocklingtonPrime13 ⟨89, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14143) (q := 14149) (by
      have hp := lowPocklingtonPrime13 ⟨90, by simp [lowPocklingtonData13]⟩
      simpa [lowPocklingtonData13] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part01_chain :
    DusartPrimeRowsChain 14051 14148 dusartPrimeRows_14051_14766_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]
