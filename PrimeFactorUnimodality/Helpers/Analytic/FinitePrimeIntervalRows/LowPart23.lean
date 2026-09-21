import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart22


set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 23 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData23 : List PocklingtonData := [
    { n := 17167, F := 17166, R := 1, a := 3, factors := [2, 3, 2861], residues := [(2, 8583), (3, 1988), (2861, 9456)] },
    { n := 17183, F := 17182, R := 1, a := 5, factors := [2, 11, 11, 71], residues := [(2, 8591), (11, 8757), (71, 6133)] },
    { n := 17189, F := 17188, R := 1, a := 2, factors := [2, 2, 4297], residues := [(2, 8594), (4297, 1146)] },
    { n := 17191, F := 17190, R := 1, a := 3, factors := [2, 3, 3, 5, 191], residues := [(2, 8595), (3, 10853), (5, 14803), (191, 10121)] },
    { n := 17203, F := 17202, R := 1, a := 2, factors := [2, 3, 47, 61], residues := [(2, 8601), (3, 15740), (47, 191), (61, 6272)] },
    { n := 17207, F := 17206, R := 1, a := 5, factors := [2, 7, 1229], residues := [(2, 8603), (7, 4719), (1229, 5531)] },
    { n := 17209, F := 17208, R := 1, a := 14, factors := [2, 2, 2, 3, 3, 239], residues := [(2, 8604), (3, 16486), (239, 6719)] },
    { n := 17231, F := 17230, R := 1, a := 13, factors := [2, 5, 1723], residues := [(2, 8615), (5, 4035), (1723, 16704)] },
    { n := 17239, F := 17238, R := 1, a := 6, factors := [2, 3, 13, 13, 17], residues := [(2, 8619), (3, 12180), (13, 977), (17, 6885)] },
    { n := 17257, F := 17256, R := 1, a := 5, factors := [2, 2, 2, 3, 719], residues := [(2, 8628), (3, 11047), (719, 3177)] },
    { n := 17291, F := 17290, R := 1, a := 6, factors := [2, 5, 7, 13, 19], residues := [(2, 8645), (5, 13376), (7, 8543), (13, 2709), (19, 1176)] },
    { n := 17293, F := 17292, R := 1, a := 7, factors := [2, 2, 3, 11, 131], residues := [(2, 8646), (3, 11572), (11, 16257), (131, 10519)] },
    { n := 17299, F := 17298, R := 1, a := 2, factors := [2, 3, 3, 31, 31], residues := [(2, 8649), (3, 1907), (31, 5345)] },
    { n := 17317, F := 17316, R := 1, a := 2, factors := [2, 2, 3, 3, 13, 37], residues := [(2, 8658), (3, 15177), (13, 13628), (37, 10493)] },
    { n := 17321, F := 17320, R := 1, a := 3, factors := [2, 2, 2, 5, 433], residues := [(2, 8660), (5, 13962), (433, 16914)] },
    { n := 17327, F := 17326, R := 1, a := 5, factors := [2, 8663], residues := [(2, 8663), (8663, 722)] },
    { n := 17333, F := 17332, R := 1, a := 2, factors := [2, 2, 7, 619], residues := [(2, 8666), (7, 457), (619, 4188)] },
    { n := 17341, F := 17340, R := 1, a := 6, factors := [2, 2, 3, 5, 17, 17], residues := [(2, 8670), (3, 14546), (5, 11695), (17, 7077)] },
    { n := 17351, F := 17350, R := 1, a := 11, factors := [2, 5, 5, 347], residues := [(2, 8675), (5, 6361), (347, 14773)] },
    { n := 17359, F := 17358, R := 1, a := 3, factors := [2, 3, 11, 263], residues := [(2, 8679), (3, 5130), (11, 14631), (263, 12255)] },
    { n := 17377, F := 17376, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 3, 181], residues := [(2, 8688), (3, 11165), (181, 4457)] },
    { n := 17383, F := 17382, R := 1, a := 5, factors := [2, 3, 2897], residues := [(2, 8691), (3, 1057), (2897, 17215)] },
    { n := 17387, F := 17386, R := 1, a := 2, factors := [2, 8693], residues := [(2, 8693), (8693, 5796)] },
    { n := 17389, F := 17388, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 7, 23], residues := [(2, 8694), (3, 10378), (7, 1874), (23, 17385)] },
    { n := 17393, F := 17392, R := 1, a := 3, factors := [2, 2, 2, 2, 1087], residues := [(2, 8696), (1087, 3770)] },
    { n := 17401, F := 17400, R := 1, a := 11, factors := [2, 2, 2, 3, 5, 5, 29], residues := [(2, 8700), (3, 201), (5, 11290), (29, 4786)] },
    { n := 17417, F := 17416, R := 1, a := 3, factors := [2, 2, 2, 7, 311], residues := [(2, 8708), (7, 14203), (311, 4925)] },
    { n := 17419, F := 17418, R := 1, a := 3, factors := [2, 3, 2903], residues := [(2, 8709), (3, 13842), (2903, 6245)] },
    { n := 17431, F := 17430, R := 1, a := 3, factors := [2, 3, 5, 7, 83], residues := [(2, 8715), (3, 4815), (5, 15936), (7, 6648), (83, 1033)] },
    { n := 17443, F := 17442, R := 1, a := 2, factors := [2, 3, 3, 3, 17, 19], residues := [(2, 8721), (3, 3773), (17, 15897), (19, 5659)] },
    { n := 17449, F := 17448, R := 1, a := 14, factors := [2, 2, 2, 3, 727], residues := [(2, 8724), (3, 11900), (727, 10142)] },
    { n := 17467, F := 17466, R := 1, a := 3, factors := [2, 3, 41, 71], residues := [(2, 8733), (3, 9347), (41, 1064), (71, 1228)] },
    { n := 17471, F := 17470, R := 1, a := 11, factors := [2, 5, 1747], residues := [(2, 8735), (5, 7310), (1747, 16225)] },
    { n := 17477, F := 17476, R := 1, a := 2, factors := [2, 2, 17, 257], residues := [(2, 8738), (17, 8004), (257, 8236)] },
    { n := 17483, F := 17482, R := 1, a := 2, factors := [2, 8741], residues := [(2, 8741), (8741, 5828)] },
    { n := 17489, F := 17488, R := 1, a := 3, factors := [2, 2, 2, 2, 1093], residues := [(2, 8744), (1093, 17350)] },
    { n := 17491, F := 17490, R := 1, a := 3, factors := [2, 3, 5, 11, 53], residues := [(2, 8745), (3, 5267), (5, 10184), (11, 10644), (53, 10972)] },
    { n := 17497, F := 17496, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 3, 3, 3, 3, 3], residues := [(2, 8748), (3, 10091)] },
    { n := 17509, F := 17508, R := 1, a := 2, factors := [2, 2, 3, 1459], residues := [(2, 8754), (3, 4460), (1459, 16594)] },
    { n := 17519, F := 17518, R := 1, a := 13, factors := [2, 19, 461], residues := [(2, 8759), (19, 16464), (461, 13983)] },
    { n := 17539, F := 17538, R := 1, a := 3, factors := [2, 3, 37, 79], residues := [(2, 8769), (3, 11533), (37, 9401), (79, 12534)] },
    { n := 17551, F := 17550, R := 1, a := 3, factors := [2, 3, 3, 3, 5, 5, 13], residues := [(2, 8775), (3, 7761), (5, 15663), (13, 14823)] },
    { n := 17569, F := 17568, R := 1, a := 11, factors := [2, 2, 2, 2, 2, 3, 3, 61], residues := [(2, 8784), (3, 7540), (61, 6249)] },
    { n := 17573, F := 17572, R := 1, a := 2, factors := [2, 2, 23, 191], residues := [(2, 8786), (23, 4240), (191, 16533)] },
    { n := 17579, F := 17578, R := 1, a := 2, factors := [2, 11, 17, 47], residues := [(2, 8789), (11, 1505), (17, 3061), (47, 1504)] },
    { n := 17581, F := 17580, R := 1, a := 10, factors := [2, 2, 3, 5, 293], residues := [(2, 8790), (3, 15850), (5, 4467), (293, 3624)] },
    { n := 17597, F := 17596, R := 1, a := 2, factors := [2, 2, 53, 83], residues := [(2, 8798), (53, 14545), (83, 7039)] },
    { n := 17599, F := 17598, R := 1, a := 6, factors := [2, 3, 7, 419], residues := [(2, 8799), (3, 8128), (7, 9114), (419, 7240)] },
    { n := 17609, F := 17608, R := 1, a := 3, factors := [2, 2, 2, 31, 71], residues := [(2, 8804), (31, 11613), (71, 10622)] },
    { n := 17623, F := 17622, R := 1, a := 3, factors := [2, 3, 3, 11, 89], residues := [(2, 8811), (3, 4757), (11, 17293), (89, 12378)] },
    { n := 17627, F := 17626, R := 1, a := 2, factors := [2, 7, 1259], residues := [(2, 8813), (7, 14848), (1259, 4010)] },
    { n := 17657, F := 17656, R := 1, a := 3, factors := [2, 2, 2, 2207], residues := [(2, 8828), (2207, 9278)] },
    { n := 17659, F := 17658, R := 1, a := 3, factors := [2, 3, 3, 3, 3, 109], residues := [(2, 8829), (3, 8515), (109, 15537)] },
    { n := 17669, F := 17668, R := 1, a := 2, factors := [2, 2, 7, 631], residues := [(2, 8834), (7, 2582), (631, 13911)] },
    { n := 17681, F := 17680, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 13, 17], residues := [(2, 8840), (5, 2155), (13, 15632), (17, 6294)] },
    { n := 17683, F := 17682, R := 1, a := 5, factors := [2, 3, 7, 421], residues := [(2, 8841), (3, 13145), (7, 6362), (421, 10940)] },
    { n := 17707, F := 17706, R := 1, a := 3, factors := [2, 3, 13, 227], residues := [(2, 8853), (3, 4357), (13, 1576), (227, 10028)] },
    { n := 17713, F := 17712, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 3, 3, 41], residues := [(2, 8856), (3, 2122), (41, 4578)] },
    { n := 17729, F := 17728, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 277], residues := [(2, 8864), (277, 3694)] },
    { n := 17737, F := 17736, R := 1, a := 7, factors := [2, 2, 2, 3, 739], residues := [(2, 8868), (3, 17003), (739, 4746)] },
    { n := 17747, F := 17746, R := 1, a := 2, factors := [2, 19, 467], residues := [(2, 8873), (19, 16497), (467, 2170)] },
    { n := 17749, F := 17748, R := 1, a := 2, factors := [2, 2, 3, 3, 17, 29], residues := [(2, 8874), (3, 14158), (17, 5880), (29, 9713)] },
    { n := 17761, F := 17760, R := 1, a := 19, factors := [2, 2, 2, 2, 2, 3, 5, 37], residues := [(2, 8880), (3, 945), (5, 10963), (37, 3018)] },
    { n := 17783, F := 17782, R := 1, a := 5, factors := [2, 17, 523], residues := [(2, 8891), (17, 13953), (523, 7995)] },
    { n := 17789, F := 17788, R := 1, a := 2, factors := [2, 2, 4447], residues := [(2, 8894), (4447, 1186)] },
    { n := 17791, F := 17790, R := 1, a := 3, factors := [2, 3, 5, 593], residues := [(2, 8895), (3, 4428), (5, 5012), (593, 3884)] },
    { n := 17807, F := 17806, R := 1, a := 5, factors := [2, 29, 307], residues := [(2, 8903), (29, 11073), (307, 12899)] },
    { n := 17827, F := 17826, R := 1, a := 2, factors := [2, 3, 2971], residues := [(2, 8913), (3, 5314), (2971, 9055)] },
    { n := 17837, F := 17836, R := 1, a := 2, factors := [2, 2, 7, 7, 7, 13], residues := [(2, 8918), (7, 7885), (13, 2230)] },
    { n := 17839, F := 17838, R := 1, a := 6, factors := [2, 3, 3, 991], residues := [(2, 8919), (3, 16075), (991, 17129)] },
    { n := 17851, F := 17850, R := 1, a := 2, factors := [2, 3, 5, 5, 7, 17], residues := [(2, 8925), (3, 16730), (5, 2339), (7, 6976), (17, 5078)] },
    { n := 17863, F := 17862, R := 1, a := 6, factors := [2, 3, 13, 229], residues := [(2, 8931), (3, 9184), (13, 11702), (229, 837)] },
    { n := 17881, F := 17880, R := 1, a := 7, factors := [2, 2, 2, 3, 5, 149], residues := [(2, 8940), (3, 13780), (5, 6375), (149, 15183)] },
    { n := 17891, F := 17890, R := 1, a := 2, factors := [2, 5, 1789], residues := [(2, 8945), (5, 13914), (1789, 3113)] },
    { n := 17903, F := 17902, R := 1, a := 5, factors := [2, 8951], residues := [(2, 8951), (8951, 746)] },
    { n := 17909, F := 17908, R := 1, a := 2, factors := [2, 2, 11, 11, 37], residues := [(2, 8954), (11, 9684), (37, 10438)] },
    { n := 17911, F := 17910, R := 1, a := 3, factors := [2, 3, 3, 5, 199], residues := [(2, 8955), (3, 13623), (5, 7261), (199, 4038)] },
    { n := 17921, F := 17920, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 7], residues := [(2, 8960), (5, 10503), (7, 12499)] },
    { n := 17923, F := 17922, R := 1, a := 2, factors := [2, 3, 29, 103], residues := [(2, 8961), (3, 204), (29, 3102), (103, 1634)] },
    { n := 17929, F := 17928, R := 1, a := 11, factors := [2, 2, 2, 3, 3, 3, 83], residues := [(2, 8964), (3, 6911), (83, 841)] },
    { n := 18839, F := 18838, R := 1, a := 7, factors := [2, 9419], residues := [(2, 9419), (9419, 9812)] },
    { n := 18859, F := 18858, R := 1, a := 2, factors := [2, 3, 7, 449], residues := [(2, 9429), (3, 7141), (7, 14750), (449, 4694)] },
    { n := 18869, F := 18868, R := 1, a := 2, factors := [2, 2, 53, 89], residues := [(2, 9434), (53, 12409), (89, 17623)] },
    { n := 18899, F := 18898, R := 1, a := 2, factors := [2, 11, 859], residues := [(2, 9449), (11, 16746), (859, 4432)] },
    { n := 18911, F := 18910, R := 1, a := 14, factors := [2, 5, 31, 61], residues := [(2, 9455), (5, 4322), (31, 14786), (61, 17232)] },
    { n := 18913, F := 18912, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 3, 197], residues := [(2, 9456), (3, 10522), (197, 5798)] },
    { n := 18917, F := 18916, R := 1, a := 2, factors := [2, 2, 4729], residues := [(2, 9458), (4729, 8828)] },
    { n := 18919, F := 18918, R := 1, a := 3, factors := [2, 3, 3, 1051], residues := [(2, 9459), (3, 18240), (1051, 5803)] },
    { n := 18947, F := 18946, R := 1, a := 2, factors := [2, 9473], residues := [(2, 9473), (9473, 6316)] },
    { n := 18959, F := 18958, R := 1, a := 13, factors := [2, 9479], residues := [(2, 9479), (9479, 13655)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData23_valid : PocklingtonRow.Valid lowPocklingtonData23 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime23 (i : Fin lowPocklingtonData23.length) :
    Nat.Prime (lowPocklingtonData23.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData23_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18803) (q := 18839) (by
      have hp := lowPocklingtonPrime23 ⟨80, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18839) (q := 18859) (by
      have hp := lowPocklingtonPrime23 ⟨81, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18859) (q := 18869) (by
      have hp := lowPocklingtonPrime23 ⟨82, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18869) (q := 18899) (by
      have hp := lowPocklingtonPrime23 ⟨83, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18899) (q := 18911) (by
      have hp := lowPocklingtonPrime23 ⟨84, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18911) (q := 18913) (by
      have hp := lowPocklingtonPrime23 ⟨85, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18913) (q := 18917) (by
      have hp := lowPocklingtonPrime23 ⟨86, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18917) (q := 18919) (by
      have hp := lowPocklingtonPrime23 ⟨87, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part11_chain :
    DusartPrimeRowsChain 18803 18918 dusartPrimeRows_18041_18958_part11 := by
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
def dusartPrimeRows_18041_18958_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18919) (q := 18947) (by
      have hp := lowPocklingtonPrime23 ⟨88, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18947) (q := 18959) (by
      have hp := lowPocklingtonPrime23 ⟨89, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part12_chain :
    DusartPrimeRowsChain 18919 18958 dusartPrimeRows_18041_18958_part12 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17159) (q := 17167) (by
      have hp := lowPocklingtonPrime23 ⟨0, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17167) (q := 17183) (by
      have hp := lowPocklingtonPrime23 ⟨1, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17183) (q := 17189) (by
      have hp := lowPocklingtonPrime23 ⟨2, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17189) (q := 17191) (by
      have hp := lowPocklingtonPrime23 ⟨3, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17191) (q := 17203) (by
      have hp := lowPocklingtonPrime23 ⟨4, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17203) (q := 17207) (by
      have hp := lowPocklingtonPrime23 ⟨5, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17207) (q := 17209) (by
      have hp := lowPocklingtonPrime23 ⟨6, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17209) (q := 17231) (by
      have hp := lowPocklingtonPrime23 ⟨7, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part01_chain :
    DusartPrimeRowsChain 17159 17230 dusartPrimeRows_17159_18040_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17231) (q := 17239) (by
      have hp := lowPocklingtonPrime23 ⟨8, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17239) (q := 17257) (by
      have hp := lowPocklingtonPrime23 ⟨9, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17257) (q := 17291) (by
      have hp := lowPocklingtonPrime23 ⟨10, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17291) (q := 17293) (by
      have hp := lowPocklingtonPrime23 ⟨11, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17293) (q := 17299) (by
      have hp := lowPocklingtonPrime23 ⟨12, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17299) (q := 17317) (by
      have hp := lowPocklingtonPrime23 ⟨13, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17317) (q := 17321) (by
      have hp := lowPocklingtonPrime23 ⟨14, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17321) (q := 17327) (by
      have hp := lowPocklingtonPrime23 ⟨15, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part02_chain :
    DusartPrimeRowsChain 17231 17326 dusartPrimeRows_17159_18040_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17327) (q := 17333) (by
      have hp := lowPocklingtonPrime23 ⟨16, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17333) (q := 17341) (by
      have hp := lowPocklingtonPrime23 ⟨17, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17341) (q := 17351) (by
      have hp := lowPocklingtonPrime23 ⟨18, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17351) (q := 17359) (by
      have hp := lowPocklingtonPrime23 ⟨19, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17359) (q := 17377) (by
      have hp := lowPocklingtonPrime23 ⟨20, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17377) (q := 17383) (by
      have hp := lowPocklingtonPrime23 ⟨21, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17383) (q := 17387) (by
      have hp := lowPocklingtonPrime23 ⟨22, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17387) (q := 17389) (by
      have hp := lowPocklingtonPrime23 ⟨23, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part03_chain :
    DusartPrimeRowsChain 17327 17388 dusartPrimeRows_17159_18040_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17389) (q := 17393) (by
      have hp := lowPocklingtonPrime23 ⟨24, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17393) (q := 17401) (by
      have hp := lowPocklingtonPrime23 ⟨25, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17401) (q := 17417) (by
      have hp := lowPocklingtonPrime23 ⟨26, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17417) (q := 17419) (by
      have hp := lowPocklingtonPrime23 ⟨27, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17419) (q := 17431) (by
      have hp := lowPocklingtonPrime23 ⟨28, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17431) (q := 17443) (by
      have hp := lowPocklingtonPrime23 ⟨29, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17443) (q := 17449) (by
      have hp := lowPocklingtonPrime23 ⟨30, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17449) (q := 17467) (by
      have hp := lowPocklingtonPrime23 ⟨31, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part04_chain :
    DusartPrimeRowsChain 17389 17466 dusartPrimeRows_17159_18040_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17467) (q := 17471) (by
      have hp := lowPocklingtonPrime23 ⟨32, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17471) (q := 17477) (by
      have hp := lowPocklingtonPrime23 ⟨33, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17477) (q := 17483) (by
      have hp := lowPocklingtonPrime23 ⟨34, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17483) (q := 17489) (by
      have hp := lowPocklingtonPrime23 ⟨35, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17489) (q := 17491) (by
      have hp := lowPocklingtonPrime23 ⟨36, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17491) (q := 17497) (by
      have hp := lowPocklingtonPrime23 ⟨37, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17497) (q := 17509) (by
      have hp := lowPocklingtonPrime23 ⟨38, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17509) (q := 17519) (by
      have hp := lowPocklingtonPrime23 ⟨39, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part05_chain :
    DusartPrimeRowsChain 17467 17518 dusartPrimeRows_17159_18040_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17519) (q := 17539) (by
      have hp := lowPocklingtonPrime23 ⟨40, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17539) (q := 17551) (by
      have hp := lowPocklingtonPrime23 ⟨41, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17551) (q := 17569) (by
      have hp := lowPocklingtonPrime23 ⟨42, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17569) (q := 17573) (by
      have hp := lowPocklingtonPrime23 ⟨43, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17573) (q := 17579) (by
      have hp := lowPocklingtonPrime23 ⟨44, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17579) (q := 17581) (by
      have hp := lowPocklingtonPrime23 ⟨45, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17581) (q := 17597) (by
      have hp := lowPocklingtonPrime23 ⟨46, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17597) (q := 17599) (by
      have hp := lowPocklingtonPrime23 ⟨47, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part06_chain :
    DusartPrimeRowsChain 17519 17598 dusartPrimeRows_17159_18040_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17599) (q := 17609) (by
      have hp := lowPocklingtonPrime23 ⟨48, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17609) (q := 17623) (by
      have hp := lowPocklingtonPrime23 ⟨49, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17623) (q := 17627) (by
      have hp := lowPocklingtonPrime23 ⟨50, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17627) (q := 17657) (by
      have hp := lowPocklingtonPrime23 ⟨51, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17657) (q := 17659) (by
      have hp := lowPocklingtonPrime23 ⟨52, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17659) (q := 17669) (by
      have hp := lowPocklingtonPrime23 ⟨53, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17669) (q := 17681) (by
      have hp := lowPocklingtonPrime23 ⟨54, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17681) (q := 17683) (by
      have hp := lowPocklingtonPrime23 ⟨55, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part07_chain :
    DusartPrimeRowsChain 17599 17682 dusartPrimeRows_17159_18040_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17683) (q := 17707) (by
      have hp := lowPocklingtonPrime23 ⟨56, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17707) (q := 17713) (by
      have hp := lowPocklingtonPrime23 ⟨57, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17713) (q := 17729) (by
      have hp := lowPocklingtonPrime23 ⟨58, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17729) (q := 17737) (by
      have hp := lowPocklingtonPrime23 ⟨59, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17737) (q := 17747) (by
      have hp := lowPocklingtonPrime23 ⟨60, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17747) (q := 17749) (by
      have hp := lowPocklingtonPrime23 ⟨61, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17749) (q := 17761) (by
      have hp := lowPocklingtonPrime23 ⟨62, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17761) (q := 17783) (by
      have hp := lowPocklingtonPrime23 ⟨63, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part08_chain :
    DusartPrimeRowsChain 17683 17782 dusartPrimeRows_17159_18040_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17783) (q := 17789) (by
      have hp := lowPocklingtonPrime23 ⟨64, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17789) (q := 17791) (by
      have hp := lowPocklingtonPrime23 ⟨65, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17791) (q := 17807) (by
      have hp := lowPocklingtonPrime23 ⟨66, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17807) (q := 17827) (by
      have hp := lowPocklingtonPrime23 ⟨67, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17827) (q := 17837) (by
      have hp := lowPocklingtonPrime23 ⟨68, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17837) (q := 17839) (by
      have hp := lowPocklingtonPrime23 ⟨69, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17839) (q := 17851) (by
      have hp := lowPocklingtonPrime23 ⟨70, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17851) (q := 17863) (by
      have hp := lowPocklingtonPrime23 ⟨71, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part09_chain :
    DusartPrimeRowsChain 17783 17862 dusartPrimeRows_17159_18040_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17863) (q := 17881) (by
      have hp := lowPocklingtonPrime23 ⟨72, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17881) (q := 17891) (by
      have hp := lowPocklingtonPrime23 ⟨73, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17891) (q := 17903) (by
      have hp := lowPocklingtonPrime23 ⟨74, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17903) (q := 17909) (by
      have hp := lowPocklingtonPrime23 ⟨75, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17909) (q := 17911) (by
      have hp := lowPocklingtonPrime23 ⟨76, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17911) (q := 17921) (by
      have hp := lowPocklingtonPrime23 ⟨77, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17921) (q := 17923) (by
      have hp := lowPocklingtonPrime23 ⟨78, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17923) (q := 17929) (by
      have hp := lowPocklingtonPrime23 ⟨79, by simp [lowPocklingtonData23]⟩
      simpa [lowPocklingtonData23] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part10_chain :
    DusartPrimeRowsChain 17863 17928 dusartPrimeRows_17159_18040_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]
