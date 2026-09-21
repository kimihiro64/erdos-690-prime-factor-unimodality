import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart21


set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 22 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData22 : List PocklingtonData := [
    { n := 18043, F := 18042, R := 1, a := 2, factors := [2, 3, 31, 97], residues := [(2, 9021), (3, 14098), (31, 8385), (97, 860)] },
    { n := 18047, F := 18046, R := 1, a := 5, factors := [2, 7, 1289], residues := [(2, 9023), (7, 17111), (1289, 572)] },
    { n := 18049, F := 18048, R := 1, a := 13, factors := [2, 2, 2, 2, 2, 2, 2, 3, 47], residues := [(2, 9024), (3, 13119), (47, 3873)] },
    { n := 18059, F := 18058, R := 1, a := 2, factors := [2, 9029], residues := [(2, 9029), (9029, 6020)] },
    { n := 18061, F := 18060, R := 1, a := 6, factors := [2, 2, 3, 5, 7, 43], residues := [(2, 9030), (3, 11108), (5, 939), (7, 14576), (43, 17703)] },
    { n := 18077, F := 18076, R := 1, a := 2, factors := [2, 2, 4519], residues := [(2, 9038), (4519, 8436)] },
    { n := 18089, F := 18088, R := 1, a := 3, factors := [2, 2, 2, 7, 17, 19], residues := [(2, 9044), (7, 1018), (17, 9477), (19, 7795)] },
    { n := 18097, F := 18096, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 13, 29], residues := [(2, 9048), (3, 14060), (13, 16363), (29, 10916)] },
    { n := 18119, F := 18118, R := 1, a := 17, factors := [2, 9059], residues := [(2, 9059), (9059, 16672)] },
    { n := 18121, F := 18120, R := 1, a := 23, factors := [2, 2, 2, 3, 5, 151], residues := [(2, 9060), (3, 12330), (5, 15075), (151, 11791)] },
    { n := 18127, F := 18126, R := 1, a := 3, factors := [2, 3, 3, 19, 53], residues := [(2, 9063), (3, 8625), (19, 9151), (53, 7244)] },
    { n := 18131, F := 18130, R := 1, a := 7, factors := [2, 5, 7, 7, 37], residues := [(2, 9065), (5, 4996), (7, 10679), (37, 11177)] },
    { n := 18133, F := 18132, R := 1, a := 5, factors := [2, 2, 3, 1511], residues := [(2, 9066), (3, 1176), (1511, 2614)] },
    { n := 18143, F := 18142, R := 1, a := 5, factors := [2, 47, 193], residues := [(2, 9071), (47, 5780), (193, 1879)] },
    { n := 18149, F := 18148, R := 1, a := 2, factors := [2, 2, 13, 349], residues := [(2, 9074), (13, 13400), (349, 4583)] },
    { n := 18169, F := 18168, R := 1, a := 11, factors := [2, 2, 2, 3, 757], residues := [(2, 9084), (3, 2191), (757, 3494)] },
    { n := 18181, F := 18180, R := 1, a := 2, factors := [2, 2, 3, 3, 5, 101], residues := [(2, 9090), (3, 3852), (5, 1019), (101, 13973)] },
    { n := 18191, F := 18190, R := 1, a := 29, factors := [2, 5, 17, 107], residues := [(2, 9095), (5, 166), (17, 960), (107, 4925)] },
    { n := 18199, F := 18198, R := 1, a := 11, factors := [2, 3, 3, 3, 337], residues := [(2, 9099), (3, 339), (337, 7826)] },
    { n := 18211, F := 18210, R := 1, a := 7, factors := [2, 3, 5, 607], residues := [(2, 9105), (3, 17518), (5, 7603), (607, 3102)] },
    { n := 18217, F := 18216, R := 1, a := 7, factors := [2, 2, 2, 3, 3, 11, 23], residues := [(2, 9108), (3, 9345), (11, 9454), (23, 8815)] },
    { n := 18223, F := 18222, R := 1, a := 3, factors := [2, 3, 3037], residues := [(2, 9111), (3, 11424), (3037, 15845)] },
    { n := 18229, F := 18228, R := 1, a := 2, factors := [2, 2, 3, 7, 7, 31], residues := [(2, 9114), (3, 16974), (7, 17385), (31, 3809)] },
    { n := 18233, F := 18232, R := 1, a := 3, factors := [2, 2, 2, 43, 53], residues := [(2, 9116), (43, 13150), (53, 438)] },
    { n := 18251, F := 18250, R := 1, a := 2, factors := [2, 5, 5, 5, 73], residues := [(2, 9125), (5, 4597), (73, 2194)] },
    { n := 18253, F := 18252, R := 1, a := 5, factors := [2, 2, 3, 3, 3, 13, 13], residues := [(2, 9126), (3, 9087), (13, 2928)] },
    { n := 18257, F := 18256, R := 1, a := 5, factors := [2, 2, 2, 2, 7, 163], residues := [(2, 9128), (7, 4491), (163, 4217)] },
    { n := 18269, F := 18268, R := 1, a := 2, factors := [2, 2, 4567], residues := [(2, 9134), (4567, 1218)] },
    { n := 18287, F := 18286, R := 1, a := 5, factors := [2, 41, 223], residues := [(2, 9143), (41, 10760), (223, 5113)] },
    { n := 18289, F := 18288, R := 1, a := 13, factors := [2, 2, 2, 2, 3, 3, 127], residues := [(2, 9144), (3, 13275), (127, 8872)] },
    { n := 18301, F := 18300, R := 1, a := 6, factors := [2, 2, 3, 5, 5, 61], residues := [(2, 9150), (3, 6530), (5, 11614), (61, 4247)] },
    { n := 18307, F := 18306, R := 1, a := 11, factors := [2, 3, 3, 3, 3, 113], residues := [(2, 9153), (3, 7894), (113, 8525)] },
    { n := 18311, F := 18310, R := 1, a := 13, factors := [2, 5, 1831], residues := [(2, 9155), (5, 2654), (1831, 3709)] },
    { n := 18313, F := 18312, R := 1, a := 10, factors := [2, 2, 2, 3, 7, 109], residues := [(2, 9156), (3, 997), (7, 9675), (109, 2521)] },
    { n := 18329, F := 18328, R := 1, a := 3, factors := [2, 2, 2, 29, 79], residues := [(2, 9164), (29, 11378), (79, 9344)] },
    { n := 18341, F := 18340, R := 1, a := 3, factors := [2, 2, 5, 7, 131], residues := [(2, 9170), (5, 10579), (7, 12998), (131, 4363)] },
    { n := 18353, F := 18352, R := 1, a := 3, factors := [2, 2, 2, 2, 31, 37], residues := [(2, 9176), (31, 8481), (37, 5670)] },
    { n := 18367, F := 18366, R := 1, a := 3, factors := [2, 3, 3061], residues := [(2, 9183), (3, 4066), (3061, 11328)] },
    { n := 18371, F := 18370, R := 1, a := 11, factors := [2, 5, 11, 167], residues := [(2, 9185), (5, 8990), (11, 17496), (167, 11524)] },
    { n := 18379, F := 18378, R := 1, a := 3, factors := [2, 3, 3, 1021], residues := [(2, 9189), (3, 15937), (1021, 3136)] },
    { n := 18397, F := 18396, R := 1, a := 6, factors := [2, 2, 3, 3, 7, 73], residues := [(2, 9198), (3, 882), (7, 2579), (73, 125)] },
    { n := 18401, F := 18400, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 5, 5, 23], residues := [(2, 9200), (5, 818), (23, 6221)] },
    { n := 18413, F := 18412, R := 1, a := 2, factors := [2, 2, 4603], residues := [(2, 9206), (4603, 15958)] },
    { n := 18427, F := 18426, R := 1, a := 2, factors := [2, 3, 37, 83], residues := [(2, 9213), (3, 5620), (37, 17644), (83, 6299)] },
    { n := 18433, F := 18432, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], residues := [(2, 9216), (3, 1261)] },
    { n := 18439, F := 18438, R := 1, a := 3, factors := [2, 3, 7, 439], residues := [(2, 9219), (3, 15742), (7, 10852), (439, 11356)] },
    { n := 18443, F := 18442, R := 1, a := 2, factors := [2, 9221], residues := [(2, 9221), (9221, 6148)] },
    { n := 18451, F := 18450, R := 1, a := 3, factors := [2, 3, 3, 5, 5, 41], residues := [(2, 9225), (3, 2791), (5, 1554), (41, 10309)] },
    { n := 18457, F := 18456, R := 1, a := 5, factors := [2, 2, 2, 3, 769], residues := [(2, 9228), (3, 6730), (769, 3407)] },
    { n := 18461, F := 18460, R := 1, a := 2, factors := [2, 2, 5, 13, 71], residues := [(2, 9230), (5, 9097), (13, 14440), (71, 3619)] },
    { n := 18481, F := 18480, R := 1, a := 13, factors := [2, 2, 2, 2, 3, 5, 7, 11], residues := [(2, 9240), (3, 13751), (5, 3806), (7, 160), (11, 12344)] },
    { n := 18493, F := 18492, R := 1, a := 2, factors := [2, 2, 3, 23, 67], residues := [(2, 9246), (3, 7381), (23, 3325), (67, 164)] },
    { n := 18503, F := 18502, R := 1, a := 5, factors := [2, 11, 29, 29], residues := [(2, 9251), (11, 8656), (29, 18083)] },
    { n := 18517, F := 18516, R := 1, a := 6, factors := [2, 2, 3, 1543], residues := [(2, 9258), (3, 1690), (1543, 13715)] },
    { n := 18521, F := 18520, R := 1, a := 3, factors := [2, 2, 2, 5, 463], residues := [(2, 9260), (5, 4206), (463, 315)] },
    { n := 18523, F := 18522, R := 1, a := 3, factors := [2, 3, 3, 3, 7, 7, 7], residues := [(2, 9261), (3, 1021), (7, 17556)] },
    { n := 18539, F := 18538, R := 1, a := 6, factors := [2, 13, 23, 31], residues := [(2, 9269), (13, 923), (23, 8637), (31, 8127)] },
    { n := 18541, F := 18540, R := 1, a := 6, factors := [2, 2, 3, 3, 5, 103], residues := [(2, 9270), (3, 7091), (5, 6191), (103, 13871)] },
    { n := 18553, F := 18552, R := 1, a := 5, factors := [2, 2, 2, 3, 773], residues := [(2, 9276), (3, 9805), (773, 1722)] },
    { n := 18583, F := 18582, R := 1, a := 3, factors := [2, 3, 19, 163], residues := [(2, 9291), (3, 8204), (19, 15045), (163, 14429)] },
    { n := 18587, F := 18586, R := 1, a := 2, factors := [2, 9293], residues := [(2, 9293), (9293, 6196)] },
    { n := 18593, F := 18592, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 7, 83], residues := [(2, 9296), (7, 10267), (83, 2167)] },
    { n := 18617, F := 18616, R := 1, a := 3, factors := [2, 2, 2, 13, 179], residues := [(2, 9308), (13, 13446), (179, 2884)] },
    { n := 18637, F := 18636, R := 1, a := 2, factors := [2, 2, 3, 1553], residues := [(2, 9318), (3, 12886), (1553, 15301)] },
    { n := 18661, F := 18660, R := 1, a := 10, factors := [2, 2, 3, 5, 311], residues := [(2, 9330), (3, 7085), (5, 9560), (311, 10989)] },
    { n := 18671, F := 18670, R := 1, a := 7, factors := [2, 5, 1867], residues := [(2, 9335), (5, 4460), (1867, 10756)] },
    { n := 18679, F := 18678, R := 1, a := 6, factors := [2, 3, 11, 283], residues := [(2, 9339), (3, 11150), (11, 11491), (283, 14067)] },
    { n := 18691, F := 18690, R := 1, a := 3, factors := [2, 3, 5, 7, 89], residues := [(2, 9345), (3, 5931), (5, 2968), (7, 5439), (89, 14194)] },
    { n := 18701, F := 18700, R := 1, a := 2, factors := [2, 2, 5, 5, 11, 17], residues := [(2, 9350), (5, 11237), (11, 18381), (17, 16714)] },
    { n := 18713, F := 18712, R := 1, a := 3, factors := [2, 2, 2, 2339], residues := [(2, 9356), (2339, 5999)] },
    { n := 18719, F := 18718, R := 1, a := 7, factors := [2, 7, 7, 191], residues := [(2, 9359), (7, 6223), (191, 5581)] },
    { n := 18731, F := 18730, R := 1, a := 2, factors := [2, 5, 1873], residues := [(2, 9365), (5, 17677), (1873, 17431)] },
    { n := 18743, F := 18742, R := 1, a := 5, factors := [2, 9371], residues := [(2, 9371), (9371, 781)] },
    { n := 18749, F := 18748, R := 1, a := 2, factors := [2, 2, 43, 109], residues := [(2, 9374), (43, 3262), (109, 12720)] },
    { n := 18757, F := 18756, R := 1, a := 2, factors := [2, 2, 3, 3, 521], residues := [(2, 9378), (3, 7613), (521, 1858)] },
    { n := 18773, F := 18772, R := 1, a := 2, factors := [2, 2, 13, 19, 19], residues := [(2, 9386), (13, 8038), (19, 9050)] },
    { n := 18787, F := 18786, R := 1, a := 2, factors := [2, 3, 31, 101], residues := [(2, 9393), (3, 3527), (31, 9175), (101, 18714)] },
    { n := 18793, F := 18792, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 3, 3, 29], residues := [(2, 9396), (3, 11810), (29, 4890)] },
    { n := 18797, F := 18796, R := 1, a := 3, factors := [2, 2, 37, 127], residues := [(2, 9398), (37, 17289), (127, 17111)] },
    { n := 18803, F := 18802, R := 1, a := 5, factors := [2, 7, 17, 79], residues := [(2, 9401), (7, 13310), (17, 12984), (79, 12069)] },
    { n := 19843, F := 19842, R := 1, a := 19, factors := [2, 3, 3307], residues := [(2, 9921), (3, 15803), (3307, 15065)] },
    { n := 19853, F := 19852, R := 1, a := 2, factors := [2, 2, 7, 709], residues := [(2, 9926), (7, 9158), (709, 124)] },
    { n := 19861, F := 19860, R := 1, a := 11, factors := [2, 2, 3, 5, 331], residues := [(2, 9930), (3, 11143), (5, 6913), (331, 2000)] },
    { n := 19867, F := 19866, R := 1, a := 2, factors := [2, 3, 7, 11, 43], residues := [(2, 9933), (3, 14776), (7, 5342), (11, 19534), (43, 12416)] },
    { n := 19889, F := 19888, R := 1, a := 3, factors := [2, 2, 2, 2, 11, 113], residues := [(2, 9944), (11, 1630), (113, 13974)] },
    { n := 19891, F := 19890, R := 1, a := 2, factors := [2, 3, 3, 5, 13, 17], residues := [(2, 9945), (3, 7172), (5, 19139), (13, 11976), (17, 2694)] },
    { n := 19913, F := 19912, R := 1, a := 3, factors := [2, 2, 2, 19, 131], residues := [(2, 9956), (19, 15115), (131, 8511)] },
    { n := 19919, F := 19918, R := 1, a := 7, factors := [2, 23, 433], residues := [(2, 9959), (23, 16088), (433, 14882)] },
    { n := 19927, F := 19926, R := 1, a := 6, factors := [2, 3, 3, 3, 3, 3, 41], residues := [(2, 9963), (3, 81), (41, 3982)] },
    { n := 19937, F := 19936, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 7, 89], residues := [(2, 9968), (7, 11232), (89, 12798)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData22_valid : PocklingtonRow.Valid lowPocklingtonData22 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime22 (i : Fin lowPocklingtonData22.length) :
    Nat.Prime (lowPocklingtonData22.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData22_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19841) (q := 19843) (by
      have hp := lowPocklingtonPrime22 ⟨80, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19843) (q := 19853) (by
      have hp := lowPocklingtonPrime22 ⟨81, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19853) (q := 19861) (by
      have hp := lowPocklingtonPrime22 ⟨82, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19861) (q := 19867) (by
      have hp := lowPocklingtonPrime22 ⟨83, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19867) (q := 19889) (by
      have hp := lowPocklingtonPrime22 ⟨84, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19889) (q := 19891) (by
      have hp := lowPocklingtonPrime22 ⟨85, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19891) (q := 19913) (by
      have hp := lowPocklingtonPrime22 ⟨86, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19913) (q := 19919) (by
      have hp := lowPocklingtonPrime22 ⟨87, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part12_chain :
    DusartPrimeRowsChain 19841 19918 dusartPrimeRows_18959_19936_part12 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19919) (q := 19927) (by
      have hp := lowPocklingtonPrime22 ⟨88, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19927) (q := 19937) (by
      have hp := lowPocklingtonPrime22 ⟨89, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part13_chain :
    DusartPrimeRowsChain 19919 19936 dusartPrimeRows_18959_19936_part13 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18041) (q := 18043) (by
      have hp := lowPocklingtonPrime22 ⟨0, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18043) (q := 18047) (by
      have hp := lowPocklingtonPrime22 ⟨1, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18047) (q := 18049) (by
      have hp := lowPocklingtonPrime22 ⟨2, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18049) (q := 18059) (by
      have hp := lowPocklingtonPrime22 ⟨3, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18059) (q := 18061) (by
      have hp := lowPocklingtonPrime22 ⟨4, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18061) (q := 18077) (by
      have hp := lowPocklingtonPrime22 ⟨5, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18077) (q := 18089) (by
      have hp := lowPocklingtonPrime22 ⟨6, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18089) (q := 18097) (by
      have hp := lowPocklingtonPrime22 ⟨7, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part01_chain :
    DusartPrimeRowsChain 18041 18096 dusartPrimeRows_18041_18958_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18097) (q := 18119) (by
      have hp := lowPocklingtonPrime22 ⟨8, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18119) (q := 18121) (by
      have hp := lowPocklingtonPrime22 ⟨9, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18121) (q := 18127) (by
      have hp := lowPocklingtonPrime22 ⟨10, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18127) (q := 18131) (by
      have hp := lowPocklingtonPrime22 ⟨11, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18131) (q := 18133) (by
      have hp := lowPocklingtonPrime22 ⟨12, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18133) (q := 18143) (by
      have hp := lowPocklingtonPrime22 ⟨13, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18143) (q := 18149) (by
      have hp := lowPocklingtonPrime22 ⟨14, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18149) (q := 18169) (by
      have hp := lowPocklingtonPrime22 ⟨15, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part02_chain :
    DusartPrimeRowsChain 18097 18168 dusartPrimeRows_18041_18958_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18169) (q := 18181) (by
      have hp := lowPocklingtonPrime22 ⟨16, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18181) (q := 18191) (by
      have hp := lowPocklingtonPrime22 ⟨17, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18191) (q := 18199) (by
      have hp := lowPocklingtonPrime22 ⟨18, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18199) (q := 18211) (by
      have hp := lowPocklingtonPrime22 ⟨19, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18211) (q := 18217) (by
      have hp := lowPocklingtonPrime22 ⟨20, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18217) (q := 18223) (by
      have hp := lowPocklingtonPrime22 ⟨21, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18223) (q := 18229) (by
      have hp := lowPocklingtonPrime22 ⟨22, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18229) (q := 18233) (by
      have hp := lowPocklingtonPrime22 ⟨23, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part03_chain :
    DusartPrimeRowsChain 18169 18232 dusartPrimeRows_18041_18958_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18233) (q := 18251) (by
      have hp := lowPocklingtonPrime22 ⟨24, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18251) (q := 18253) (by
      have hp := lowPocklingtonPrime22 ⟨25, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18253) (q := 18257) (by
      have hp := lowPocklingtonPrime22 ⟨26, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18257) (q := 18269) (by
      have hp := lowPocklingtonPrime22 ⟨27, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18269) (q := 18287) (by
      have hp := lowPocklingtonPrime22 ⟨28, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18287) (q := 18289) (by
      have hp := lowPocklingtonPrime22 ⟨29, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18289) (q := 18301) (by
      have hp := lowPocklingtonPrime22 ⟨30, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18301) (q := 18307) (by
      have hp := lowPocklingtonPrime22 ⟨31, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part04_chain :
    DusartPrimeRowsChain 18233 18306 dusartPrimeRows_18041_18958_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18307) (q := 18311) (by
      have hp := lowPocklingtonPrime22 ⟨32, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18311) (q := 18313) (by
      have hp := lowPocklingtonPrime22 ⟨33, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18313) (q := 18329) (by
      have hp := lowPocklingtonPrime22 ⟨34, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18329) (q := 18341) (by
      have hp := lowPocklingtonPrime22 ⟨35, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18341) (q := 18353) (by
      have hp := lowPocklingtonPrime22 ⟨36, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18353) (q := 18367) (by
      have hp := lowPocklingtonPrime22 ⟨37, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18367) (q := 18371) (by
      have hp := lowPocklingtonPrime22 ⟨38, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18371) (q := 18379) (by
      have hp := lowPocklingtonPrime22 ⟨39, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part05_chain :
    DusartPrimeRowsChain 18307 18378 dusartPrimeRows_18041_18958_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18379) (q := 18397) (by
      have hp := lowPocklingtonPrime22 ⟨40, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18397) (q := 18401) (by
      have hp := lowPocklingtonPrime22 ⟨41, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18401) (q := 18413) (by
      have hp := lowPocklingtonPrime22 ⟨42, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18413) (q := 18427) (by
      have hp := lowPocklingtonPrime22 ⟨43, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18427) (q := 18433) (by
      have hp := lowPocklingtonPrime22 ⟨44, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18433) (q := 18439) (by
      have hp := lowPocklingtonPrime22 ⟨45, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18439) (q := 18443) (by
      have hp := lowPocklingtonPrime22 ⟨46, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18443) (q := 18451) (by
      have hp := lowPocklingtonPrime22 ⟨47, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part06_chain :
    DusartPrimeRowsChain 18379 18450 dusartPrimeRows_18041_18958_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18451) (q := 18457) (by
      have hp := lowPocklingtonPrime22 ⟨48, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18457) (q := 18461) (by
      have hp := lowPocklingtonPrime22 ⟨49, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18461) (q := 18481) (by
      have hp := lowPocklingtonPrime22 ⟨50, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18481) (q := 18493) (by
      have hp := lowPocklingtonPrime22 ⟨51, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18493) (q := 18503) (by
      have hp := lowPocklingtonPrime22 ⟨52, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18503) (q := 18517) (by
      have hp := lowPocklingtonPrime22 ⟨53, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18517) (q := 18521) (by
      have hp := lowPocklingtonPrime22 ⟨54, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18521) (q := 18523) (by
      have hp := lowPocklingtonPrime22 ⟨55, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part07_chain :
    DusartPrimeRowsChain 18451 18522 dusartPrimeRows_18041_18958_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18523) (q := 18539) (by
      have hp := lowPocklingtonPrime22 ⟨56, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18539) (q := 18541) (by
      have hp := lowPocklingtonPrime22 ⟨57, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18541) (q := 18553) (by
      have hp := lowPocklingtonPrime22 ⟨58, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18553) (q := 18583) (by
      have hp := lowPocklingtonPrime22 ⟨59, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18583) (q := 18587) (by
      have hp := lowPocklingtonPrime22 ⟨60, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18587) (q := 18593) (by
      have hp := lowPocklingtonPrime22 ⟨61, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18593) (q := 18617) (by
      have hp := lowPocklingtonPrime22 ⟨62, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18617) (q := 18637) (by
      have hp := lowPocklingtonPrime22 ⟨63, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part08_chain :
    DusartPrimeRowsChain 18523 18636 dusartPrimeRows_18041_18958_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18637) (q := 18661) (by
      have hp := lowPocklingtonPrime22 ⟨64, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18661) (q := 18671) (by
      have hp := lowPocklingtonPrime22 ⟨65, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18671) (q := 18679) (by
      have hp := lowPocklingtonPrime22 ⟨66, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18679) (q := 18691) (by
      have hp := lowPocklingtonPrime22 ⟨67, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18691) (q := 18701) (by
      have hp := lowPocklingtonPrime22 ⟨68, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18701) (q := 18713) (by
      have hp := lowPocklingtonPrime22 ⟨69, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18713) (q := 18719) (by
      have hp := lowPocklingtonPrime22 ⟨70, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18719) (q := 18731) (by
      have hp := lowPocklingtonPrime22 ⟨71, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part09_chain :
    DusartPrimeRowsChain 18637 18730 dusartPrimeRows_18041_18958_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18731) (q := 18743) (by
      have hp := lowPocklingtonPrime22 ⟨72, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18743) (q := 18749) (by
      have hp := lowPocklingtonPrime22 ⟨73, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18749) (q := 18757) (by
      have hp := lowPocklingtonPrime22 ⟨74, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18757) (q := 18773) (by
      have hp := lowPocklingtonPrime22 ⟨75, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18773) (q := 18787) (by
      have hp := lowPocklingtonPrime22 ⟨76, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18787) (q := 18793) (by
      have hp := lowPocklingtonPrime22 ⟨77, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18793) (q := 18797) (by
      have hp := lowPocklingtonPrime22 ⟨78, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18797) (q := 18803) (by
      have hp := lowPocklingtonPrime22 ⟨79, by simp [lowPocklingtonData22]⟩
      simpa [lowPocklingtonData22] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part10_chain :
    DusartPrimeRowsChain 18731 18802 dusartPrimeRows_18041_18958_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]
