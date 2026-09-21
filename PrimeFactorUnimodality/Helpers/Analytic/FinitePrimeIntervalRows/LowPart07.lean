import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 07 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData07 : List PocklingtonData := [
    { n := 8117, F := 8116, R := 1, a := 2, factors := [2, 2, 2029], residues := [(2, 4058), (2029, 3788)] },
    { n := 8123, F := 8122, R := 1, a := 2, factors := [2, 31, 131], residues := [(2, 4061), (31, 3866), (131, 7709)] },
    { n := 8147, F := 8146, R := 1, a := 2, factors := [2, 4073], residues := [(2, 4073), (4073, 2716)] },
    { n := 8161, F := 8160, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 3, 5, 17], residues := [(2, 4080), (3, 6408), (5, 2231), (17, 2310)] },
    { n := 8167, F := 8166, R := 1, a := 3, factors := [2, 3, 1361], residues := [(2, 4083), (3, 1691), (1361, 7191)] },
    { n := 8171, F := 8170, R := 1, a := 2, factors := [2, 5, 19, 43], residues := [(2, 4085), (5, 5060), (19, 383), (43, 7581)] },
    { n := 8179, F := 8178, R := 1, a := 2, factors := [2, 3, 29, 47], residues := [(2, 4089), (3, 7813), (29, 6725), (47, 3326)] },
    { n := 8191, F := 8190, R := 1, a := 17, factors := [2, 3, 3, 5, 7, 13], residues := [(2, 4095), (3, 2760), (5, 2653), (7, 3806), (13, 7021)] },
    { n := 8209, F := 8208, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 3, 3, 19], residues := [(2, 4104), (3, 7120), (19, 3087)] },
    { n := 8219, F := 8218, R := 1, a := 2, factors := [2, 7, 587], residues := [(2, 4109), (7, 261), (587, 5828)] },
    { n := 8221, F := 8220, R := 1, a := 2, factors := [2, 2, 3, 5, 137], residues := [(2, 4110), (3, 8082), (5, 1189), (137, 7376)] },
    { n := 8231, F := 8230, R := 1, a := 11, factors := [2, 5, 823], residues := [(2, 4115), (5, 2645), (823, 1546)] },
    { n := 8233, F := 8232, R := 1, a := 10, factors := [2, 2, 2, 3, 7, 7, 7], residues := [(2, 4116), (3, 1873), (7, 7943)] },
    { n := 8237, F := 8236, R := 1, a := 2, factors := [2, 2, 29, 71], residues := [(2, 4118), (29, 6337), (71, 5515)] },
    { n := 8243, F := 8242, R := 1, a := 2, factors := [2, 13, 317], residues := [(2, 4121), (13, 4637), (317, 1563)] },
    { n := 8263, F := 8262, R := 1, a := 3, factors := [2, 3, 3, 3, 3, 3, 17], residues := [(2, 4131), (3, 5428), (17, 7741)] },
    { n := 8269, F := 8268, R := 1, a := 2, factors := [2, 2, 3, 13, 53], residues := [(2, 4134), (3, 52), (13, 5435), (53, 1260)] },
    { n := 8273, F := 8272, R := 1, a := 3, factors := [2, 2, 2, 2, 11, 47], residues := [(2, 4136), (11, 3762), (47, 6509)] },
    { n := 8287, F := 8286, R := 1, a := 3, factors := [2, 3, 1381], residues := [(2, 4143), (3, 8097), (1381, 6386)] },
    { n := 8291, F := 8290, R := 1, a := 2, factors := [2, 5, 829], residues := [(2, 4145), (5, 7547), (829, 5114)] },
    { n := 8293, F := 8292, R := 1, a := 2, factors := [2, 2, 3, 691], residues := [(2, 4146), (3, 683), (691, 5636)] },
    { n := 8297, F := 8296, R := 1, a := 3, factors := [2, 2, 2, 17, 61], residues := [(2, 4148), (17, 87), (61, 1311)] },
    { n := 8311, F := 8310, R := 1, a := 3, factors := [2, 3, 5, 277], residues := [(2, 4155), (3, 3192), (5, 5690), (277, 4836)] },
    { n := 8317, F := 8316, R := 1, a := 6, factors := [2, 2, 3, 3, 3, 7, 11], residues := [(2, 4158), (3, 2343), (7, 2224), (11, 5547)] },
    { n := 8329, F := 8328, R := 1, a := 7, factors := [2, 2, 2, 3, 347], residues := [(2, 4164), (3, 5903), (347, 4312)] },
    { n := 8353, F := 8352, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 3, 3, 29], residues := [(2, 4176), (3, 2205), (29, 8320)] },
    { n := 8363, F := 8362, R := 1, a := 2, factors := [2, 37, 113], residues := [(2, 4181), (37, 6983), (113, 7763)] },
    { n := 8369, F := 8368, R := 1, a := 3, factors := [2, 2, 2, 2, 523], residues := [(2, 4184), (523, 2080)] },
    { n := 8377, F := 8376, R := 1, a := 5, factors := [2, 2, 2, 3, 349], residues := [(2, 4188), (3, 5313), (349, 2759)] },
    { n := 8387, F := 8386, R := 1, a := 2, factors := [2, 7, 599], residues := [(2, 4193), (7, 6456), (599, 429)] },
    { n := 8389, F := 8388, R := 1, a := 6, factors := [2, 2, 3, 3, 233], residues := [(2, 4194), (3, 8158), (233, 1599)] },
    { n := 8419, F := 8418, R := 1, a := 3, factors := [2, 3, 23, 61], residues := [(2, 4209), (3, 2152), (23, 5744), (61, 8029)] },
    { n := 8423, F := 8422, R := 1, a := 5, factors := [2, 4211], residues := [(2, 4211), (4211, 351)] },
    { n := 8429, F := 8428, R := 1, a := 2, factors := [2, 2, 7, 7, 43], residues := [(2, 4214), (7, 5886), (43, 6920)] },
    { n := 8431, F := 8430, R := 1, a := 3, factors := [2, 3, 5, 281], residues := [(2, 4215), (3, 6336), (5, 876), (281, 1436)] },
    { n := 8443, F := 8442, R := 1, a := 2, factors := [2, 3, 3, 7, 67], residues := [(2, 4221), (3, 5283), (7, 1903), (67, 6328)] },
    { n := 8447, F := 8446, R := 1, a := 5, factors := [2, 41, 103], residues := [(2, 4223), (41, 2321), (103, 8260)] },
    { n := 8461, F := 8460, R := 1, a := 6, factors := [2, 2, 3, 3, 5, 47], residues := [(2, 4230), (3, 3412), (5, 5189), (47, 7446)] },
    { n := 8467, F := 8466, R := 1, a := 2, factors := [2, 3, 17, 83], residues := [(2, 4233), (3, 7040), (17, 4751), (83, 5649)] },
    { n := 8501, F := 8500, R := 1, a := 7, factors := [2, 2, 5, 5, 5, 17], residues := [(2, 4250), (5, 1505), (17, 789)] },
    { n := 8513, F := 8512, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 7, 19], residues := [(2, 4256), (7, 7144), (19, 2070)] },
    { n := 8521, F := 8520, R := 1, a := 13, factors := [2, 2, 2, 3, 5, 71], residues := [(2, 4260), (3, 2165), (5, 3129), (71, 1336)] },
    { n := 8527, F := 8526, R := 1, a := 5, factors := [2, 3, 7, 7, 29], residues := [(2, 4263), (3, 3834), (7, 394), (29, 744)] },
    { n := 8537, F := 8536, R := 1, a := 3, factors := [2, 2, 2, 11, 97], residues := [(2, 4268), (11, 544), (97, 7731)] },
    { n := 8539, F := 8538, R := 1, a := 2, factors := [2, 3, 1423], residues := [(2, 4269), (3, 1995), (1423, 6777)] },
    { n := 8543, F := 8542, R := 1, a := 5, factors := [2, 4271], residues := [(2, 4271), (4271, 356)] },
    { n := 8563, F := 8562, R := 1, a := 2, factors := [2, 3, 1427], residues := [(2, 4281), (3, 4767), (1427, 5165)] },
    { n := 8573, F := 8572, R := 1, a := 2, factors := [2, 2, 2143], residues := [(2, 4286), (2143, 7430)] },
    { n := 8581, F := 8580, R := 1, a := 6, factors := [2, 2, 3, 5, 11, 13], residues := [(2, 4290), (3, 8439), (5, 8084), (11, 4069), (13, 2714)] },
    { n := 8597, F := 8596, R := 1, a := 2, factors := [2, 2, 7, 307], residues := [(2, 4298), (7, 7660), (307, 8411)] },
    { n := 8599, F := 8598, R := 1, a := 3, factors := [2, 3, 1433], residues := [(2, 4299), (3, 6134), (1433, 5398)] },
    { n := 8609, F := 8608, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 269], residues := [(2, 4304), (269, 4780)] },
    { n := 8623, F := 8622, R := 1, a := 3, factors := [2, 3, 3, 479], residues := [(2, 4311), (3, 5233), (479, 4775)] },
    { n := 8627, F := 8626, R := 1, a := 2, factors := [2, 19, 227], residues := [(2, 4313), (19, 482), (227, 3929)] },
    { n := 8629, F := 8628, R := 1, a := 6, factors := [2, 2, 3, 719], residues := [(2, 4314), (3, 4650), (719, 2319)] },
    { n := 8641, F := 8640, R := 1, a := 17, factors := [2, 2, 2, 2, 2, 2, 3, 3, 3, 5], residues := [(2, 4320), (3, 6951), (5, 3801)] },
    { n := 8647, F := 8646, R := 1, a := 3, factors := [2, 3, 11, 131], residues := [(2, 4323), (3, 2617), (11, 6748), (131, 2137)] },
    { n := 8663, F := 8662, R := 1, a := 5, factors := [2, 61, 71], residues := [(2, 4331), (61, 4990), (71, 6368)] },
    { n := 8669, F := 8668, R := 1, a := 2, factors := [2, 2, 11, 197], residues := [(2, 4334), (11, 4722), (197, 5512)] },
    { n := 8677, F := 8676, R := 1, a := 2, factors := [2, 2, 3, 3, 241], residues := [(2, 4338), (3, 8217), (241, 1404)] },
    { n := 8681, F := 8680, R := 1, a := 15, factors := [2, 2, 2, 5, 7, 31], residues := [(2, 4340), (5, 3404), (7, 8175), (31, 6082)] },
    { n := 8689, F := 8688, R := 1, a := 13, factors := [2, 2, 2, 2, 3, 181], residues := [(2, 4344), (3, 8054), (181, 4782)] },
    { n := 8693, F := 8692, R := 1, a := 2, factors := [2, 2, 41, 53], residues := [(2, 4346), (41, 4368), (53, 3635)] },
    { n := 8699, F := 8698, R := 1, a := 2, factors := [2, 4349], residues := [(2, 4349), (4349, 2900)] },
    { n := 8707, F := 8706, R := 1, a := 5, factors := [2, 3, 1451], residues := [(2, 4353), (3, 804), (1451, 2544)] },
    { n := 8713, F := 8712, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 11, 11], residues := [(2, 4356), (3, 6654), (11, 7898)] },
    { n := 8719, F := 8718, R := 1, a := 3, factors := [2, 3, 1453], residues := [(2, 4359), (3, 7958), (1453, 3078)] },
    { n := 8731, F := 8730, R := 1, a := 2, factors := [2, 3, 3, 5, 97], residues := [(2, 4365), (3, 7511), (5, 4101), (97, 7838)] },
    { n := 8737, F := 8736, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 3, 7, 13], residues := [(2, 4368), (3, 5068), (7, 6289), (13, 1583)] },
    { n := 8741, F := 8740, R := 1, a := 2, factors := [2, 2, 5, 19, 23], residues := [(2, 4370), (5, 7350), (19, 538), (23, 8561)] },
    { n := 8747, F := 8746, R := 1, a := 2, factors := [2, 4373], residues := [(2, 4373), (4373, 2916)] },
    { n := 8753, F := 8752, R := 1, a := 3, factors := [2, 2, 2, 2, 547], residues := [(2, 4376), (547, 377)] },
    { n := 8761, F := 8760, R := 1, a := 23, factors := [2, 2, 2, 3, 5, 73], residues := [(2, 4380), (3, 2342), (5, 2202), (73, 1258)] },
    { n := 8779, F := 8778, R := 1, a := 11, factors := [2, 3, 7, 11, 19], residues := [(2, 4389), (3, 422), (7, 5532), (11, 6068), (19, 5351)] },
    { n := 8783, F := 8782, R := 1, a := 5, factors := [2, 4391], residues := [(2, 4391), (4391, 366)] },
    { n := 8803, F := 8802, R := 1, a := 2, factors := [2, 3, 3, 3, 163], residues := [(2, 4401), (3, 329), (163, 4013)] },
    { n := 8807, F := 8806, R := 1, a := 5, factors := [2, 7, 17, 37], residues := [(2, 4403), (7, 2565), (17, 1137), (37, 8605)] },
    { n := 8819, F := 8818, R := 1, a := 2, factors := [2, 4409], residues := [(2, 4409), (4409, 2940)] },
    { n := 8821, F := 8820, R := 1, a := 2, factors := [2, 2, 3, 3, 5, 7, 7], residues := [(2, 4410), (3, 3752), (5, 5349), (7, 8403)] },
    { n := 8831, F := 8830, R := 1, a := 7, factors := [2, 5, 883], residues := [(2, 4415), (5, 615), (883, 4744)] },
    { n := 8837, F := 8836, R := 1, a := 2, factors := [2, 2, 47, 47], residues := [(2, 4418), (47, 8274)] },
    { n := 8839, F := 8838, R := 1, a := 3, factors := [2, 3, 3, 491], residues := [(2, 4419), (3, 7381), (491, 1171)] },
    { n := 8849, F := 8848, R := 1, a := 3, factors := [2, 2, 2, 2, 7, 79], residues := [(2, 4424), (7, 8684), (79, 6705)] },
    { n := 8861, F := 8860, R := 1, a := 2, factors := [2, 2, 5, 443], residues := [(2, 4430), (5, 2126), (443, 2152)] },
    { n := 8863, F := 8862, R := 1, a := 3, factors := [2, 3, 7, 211], residues := [(2, 4431), (3, 3441), (7, 7602), (211, 2442)] },
    { n := 8867, F := 8866, R := 1, a := 2, factors := [2, 11, 13, 31], residues := [(2, 4433), (11, 3248), (13, 7391), (31, 3741)] },
    { n := 8887, F := 8886, R := 1, a := 3, factors := [2, 3, 1481], residues := [(2, 4443), (3, 4515), (1481, 7239)] },
    { n := 8893, F := 8892, R := 1, a := 5, factors := [2, 2, 3, 3, 13, 19], residues := [(2, 4446), (3, 5845), (13, 5146), (19, 5017)] },
    { n := 8923, F := 8922, R := 1, a := 2, factors := [2, 3, 1487], residues := [(2, 4461), (3, 1282), (1487, 1558)] },
    { n := 8929, F := 8928, R := 1, a := 11, factors := [2, 2, 2, 2, 2, 3, 3, 31], residues := [(2, 4464), (3, 7482), (31, 732)] },
    { n := 8933, F := 8932, R := 1, a := 2, factors := [2, 2, 7, 11, 29], residues := [(2, 4466), (7, 6981), (11, 7685), (29, 5851)] },
    { n := 8941, F := 8940, R := 1, a := 6, factors := [2, 2, 3, 5, 149], residues := [(2, 4470), (3, 2433), (5, 5138), (149, 3114)] },
    { n := 8951, F := 8950, R := 1, a := 13, factors := [2, 5, 5, 179], residues := [(2, 4475), (5, 2628), (179, 5499)] },
    { n := 8963, F := 8962, R := 1, a := 2, factors := [2, 4481], residues := [(2, 4481), (4481, 2988)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData07_valid : PocklingtonRow.Valid lowPocklingtonData07 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime07 (i : Fin lowPocklingtonData07.length) :
    Nat.Prime (lowPocklingtonData07.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData07_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8111) (q := 8117) (by
      have hp := lowPocklingtonPrime07 ⟨0, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8117) (q := 8123) (by
      have hp := lowPocklingtonPrime07 ⟨1, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8123) (q := 8147) (by
      have hp := lowPocklingtonPrime07 ⟨2, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8147) (q := 8161) (by
      have hp := lowPocklingtonPrime07 ⟨3, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8161) (q := 8167) (by
      have hp := lowPocklingtonPrime07 ⟨4, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8167) (q := 8171) (by
      have hp := lowPocklingtonPrime07 ⟨5, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8171) (q := 8179) (by
      have hp := lowPocklingtonPrime07 ⟨6, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8179) (q := 8191) (by
      have hp := lowPocklingtonPrime07 ⟨7, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part01_chain :
    DusartPrimeRowsChain 8111 8190 dusartPrimeRows_8111_8520_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8191) (q := 8209) (by
      have hp := lowPocklingtonPrime07 ⟨8, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8209) (q := 8219) (by
      have hp := lowPocklingtonPrime07 ⟨9, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8219) (q := 8221) (by
      have hp := lowPocklingtonPrime07 ⟨10, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8221) (q := 8231) (by
      have hp := lowPocklingtonPrime07 ⟨11, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8231) (q := 8233) (by
      have hp := lowPocklingtonPrime07 ⟨12, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8233) (q := 8237) (by
      have hp := lowPocklingtonPrime07 ⟨13, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8237) (q := 8243) (by
      have hp := lowPocklingtonPrime07 ⟨14, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8243) (q := 8263) (by
      have hp := lowPocklingtonPrime07 ⟨15, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part02_chain :
    DusartPrimeRowsChain 8191 8262 dusartPrimeRows_8111_8520_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8263) (q := 8269) (by
      have hp := lowPocklingtonPrime07 ⟨16, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8269) (q := 8273) (by
      have hp := lowPocklingtonPrime07 ⟨17, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8273) (q := 8287) (by
      have hp := lowPocklingtonPrime07 ⟨18, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8287) (q := 8291) (by
      have hp := lowPocklingtonPrime07 ⟨19, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8291) (q := 8293) (by
      have hp := lowPocklingtonPrime07 ⟨20, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8293) (q := 8297) (by
      have hp := lowPocklingtonPrime07 ⟨21, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8297) (q := 8311) (by
      have hp := lowPocklingtonPrime07 ⟨22, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8311) (q := 8317) (by
      have hp := lowPocklingtonPrime07 ⟨23, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part03_chain :
    DusartPrimeRowsChain 8263 8316 dusartPrimeRows_8111_8520_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8317) (q := 8329) (by
      have hp := lowPocklingtonPrime07 ⟨24, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8329) (q := 8353) (by
      have hp := lowPocklingtonPrime07 ⟨25, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8353) (q := 8363) (by
      have hp := lowPocklingtonPrime07 ⟨26, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8363) (q := 8369) (by
      have hp := lowPocklingtonPrime07 ⟨27, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8369) (q := 8377) (by
      have hp := lowPocklingtonPrime07 ⟨28, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8377) (q := 8387) (by
      have hp := lowPocklingtonPrime07 ⟨29, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8387) (q := 8389) (by
      have hp := lowPocklingtonPrime07 ⟨30, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8389) (q := 8419) (by
      have hp := lowPocklingtonPrime07 ⟨31, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part04_chain :
    DusartPrimeRowsChain 8317 8418 dusartPrimeRows_8111_8520_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8419) (q := 8423) (by
      have hp := lowPocklingtonPrime07 ⟨32, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8423) (q := 8429) (by
      have hp := lowPocklingtonPrime07 ⟨33, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8429) (q := 8431) (by
      have hp := lowPocklingtonPrime07 ⟨34, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8431) (q := 8443) (by
      have hp := lowPocklingtonPrime07 ⟨35, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8443) (q := 8447) (by
      have hp := lowPocklingtonPrime07 ⟨36, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8447) (q := 8461) (by
      have hp := lowPocklingtonPrime07 ⟨37, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8461) (q := 8467) (by
      have hp := lowPocklingtonPrime07 ⟨38, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8467) (q := 8501) (by
      have hp := lowPocklingtonPrime07 ⟨39, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part05_chain :
    DusartPrimeRowsChain 8419 8500 dusartPrimeRows_8111_8520_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8501) (q := 8513) (by
      have hp := lowPocklingtonPrime07 ⟨40, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8513) (q := 8521) (by
      have hp := lowPocklingtonPrime07 ⟨41, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part06_chain :
    DusartPrimeRowsChain 8501 8520 dusartPrimeRows_8111_8520_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_8518, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8521) (q := 8527) (by
      have hp := lowPocklingtonPrime07 ⟨42, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8527) (q := 8537) (by
      have hp := lowPocklingtonPrime07 ⟨43, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8537) (q := 8539) (by
      have hp := lowPocklingtonPrime07 ⟨44, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8539) (q := 8543) (by
      have hp := lowPocklingtonPrime07 ⟨45, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8543) (q := 8563) (by
      have hp := lowPocklingtonPrime07 ⟨46, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8563) (q := 8573) (by
      have hp := lowPocklingtonPrime07 ⟨47, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8573) (q := 8581) (by
      have hp := lowPocklingtonPrime07 ⟨48, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8581) (q := 8597) (by
      have hp := lowPocklingtonPrime07 ⟨49, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part01_chain :
    DusartPrimeRowsChain 8521 8596 dusartPrimeRows_8521_8962_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8597) (q := 8599) (by
      have hp := lowPocklingtonPrime07 ⟨50, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8599) (q := 8609) (by
      have hp := lowPocklingtonPrime07 ⟨51, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8609) (q := 8623) (by
      have hp := lowPocklingtonPrime07 ⟨52, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8623) (q := 8627) (by
      have hp := lowPocklingtonPrime07 ⟨53, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8627) (q := 8629) (by
      have hp := lowPocklingtonPrime07 ⟨54, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8629) (q := 8641) (by
      have hp := lowPocklingtonPrime07 ⟨55, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8641) (q := 8647) (by
      have hp := lowPocklingtonPrime07 ⟨56, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8647) (q := 8663) (by
      have hp := lowPocklingtonPrime07 ⟨57, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part02_chain :
    DusartPrimeRowsChain 8597 8662 dusartPrimeRows_8521_8962_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8663) (q := 8669) (by
      have hp := lowPocklingtonPrime07 ⟨58, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8669) (q := 8677) (by
      have hp := lowPocklingtonPrime07 ⟨59, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8677) (q := 8681) (by
      have hp := lowPocklingtonPrime07 ⟨60, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8681) (q := 8689) (by
      have hp := lowPocklingtonPrime07 ⟨61, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8689) (q := 8693) (by
      have hp := lowPocklingtonPrime07 ⟨62, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8693) (q := 8699) (by
      have hp := lowPocklingtonPrime07 ⟨63, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8699) (q := 8707) (by
      have hp := lowPocklingtonPrime07 ⟨64, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8707) (q := 8713) (by
      have hp := lowPocklingtonPrime07 ⟨65, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part03_chain :
    DusartPrimeRowsChain 8663 8712 dusartPrimeRows_8521_8962_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8713) (q := 8719) (by
      have hp := lowPocklingtonPrime07 ⟨66, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8719) (q := 8731) (by
      have hp := lowPocklingtonPrime07 ⟨67, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8731) (q := 8737) (by
      have hp := lowPocklingtonPrime07 ⟨68, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8737) (q := 8741) (by
      have hp := lowPocklingtonPrime07 ⟨69, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8741) (q := 8747) (by
      have hp := lowPocklingtonPrime07 ⟨70, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8747) (q := 8753) (by
      have hp := lowPocklingtonPrime07 ⟨71, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8753) (q := 8761) (by
      have hp := lowPocklingtonPrime07 ⟨72, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8761) (q := 8779) (by
      have hp := lowPocklingtonPrime07 ⟨73, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part04_chain :
    DusartPrimeRowsChain 8713 8778 dusartPrimeRows_8521_8962_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8779) (q := 8783) (by
      have hp := lowPocklingtonPrime07 ⟨74, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8783) (q := 8803) (by
      have hp := lowPocklingtonPrime07 ⟨75, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8803) (q := 8807) (by
      have hp := lowPocklingtonPrime07 ⟨76, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8807) (q := 8819) (by
      have hp := lowPocklingtonPrime07 ⟨77, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8819) (q := 8821) (by
      have hp := lowPocklingtonPrime07 ⟨78, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8821) (q := 8831) (by
      have hp := lowPocklingtonPrime07 ⟨79, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8831) (q := 8837) (by
      have hp := lowPocklingtonPrime07 ⟨80, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8837) (q := 8839) (by
      have hp := lowPocklingtonPrime07 ⟨81, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part05_chain :
    DusartPrimeRowsChain 8779 8838 dusartPrimeRows_8521_8962_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8839) (q := 8849) (by
      have hp := lowPocklingtonPrime07 ⟨82, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8849) (q := 8861) (by
      have hp := lowPocklingtonPrime07 ⟨83, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8861) (q := 8863) (by
      have hp := lowPocklingtonPrime07 ⟨84, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8863) (q := 8867) (by
      have hp := lowPocklingtonPrime07 ⟨85, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8867) (q := 8887) (by
      have hp := lowPocklingtonPrime07 ⟨86, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8887) (q := 8893) (by
      have hp := lowPocklingtonPrime07 ⟨87, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8893) (q := 8923) (by
      have hp := lowPocklingtonPrime07 ⟨88, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8923) (q := 8929) (by
      have hp := lowPocklingtonPrime07 ⟨89, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part06_chain :
    DusartPrimeRowsChain 8839 8928 dusartPrimeRows_8521_8962_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8929) (q := 8933) (by
      have hp := lowPocklingtonPrime07 ⟨90, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8933) (q := 8941) (by
      have hp := lowPocklingtonPrime07 ⟨91, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8941) (q := 8951) (by
      have hp := lowPocklingtonPrime07 ⟨92, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8951) (q := 8963) (by
      have hp := lowPocklingtonPrime07 ⟨93, by simp [lowPocklingtonData07]⟩
      simpa [lowPocklingtonData07] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part07_chain :
    DusartPrimeRowsChain 8929 8962 dusartPrimeRows_8521_8962_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.empty
          norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]
