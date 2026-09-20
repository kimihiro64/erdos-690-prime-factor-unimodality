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

theorem lowPrime_8117 : Nat.Prime 8117 := by
  let d := lowPocklingtonData07.get ⟨0, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8123 : Nat.Prime 8123 := by
  let d := lowPocklingtonData07.get ⟨1, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8147 : Nat.Prime 8147 := by
  let d := lowPocklingtonData07.get ⟨2, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8161 : Nat.Prime 8161 := by
  let d := lowPocklingtonData07.get ⟨3, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8167 : Nat.Prime 8167 := by
  let d := lowPocklingtonData07.get ⟨4, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8171 : Nat.Prime 8171 := by
  let d := lowPocklingtonData07.get ⟨5, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8179 : Nat.Prime 8179 := by
  let d := lowPocklingtonData07.get ⟨6, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8191 : Nat.Prime 8191 := by
  let d := lowPocklingtonData07.get ⟨7, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8209 : Nat.Prime 8209 := by
  let d := lowPocklingtonData07.get ⟨8, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8219 : Nat.Prime 8219 := by
  let d := lowPocklingtonData07.get ⟨9, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8221 : Nat.Prime 8221 := by
  let d := lowPocklingtonData07.get ⟨10, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8231 : Nat.Prime 8231 := by
  let d := lowPocklingtonData07.get ⟨11, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8233 : Nat.Prime 8233 := by
  let d := lowPocklingtonData07.get ⟨12, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8237 : Nat.Prime 8237 := by
  let d := lowPocklingtonData07.get ⟨13, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8243 : Nat.Prime 8243 := by
  let d := lowPocklingtonData07.get ⟨14, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8263 : Nat.Prime 8263 := by
  let d := lowPocklingtonData07.get ⟨15, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8269 : Nat.Prime 8269 := by
  let d := lowPocklingtonData07.get ⟨16, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8273 : Nat.Prime 8273 := by
  let d := lowPocklingtonData07.get ⟨17, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8287 : Nat.Prime 8287 := by
  let d := lowPocklingtonData07.get ⟨18, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8291 : Nat.Prime 8291 := by
  let d := lowPocklingtonData07.get ⟨19, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8293 : Nat.Prime 8293 := by
  let d := lowPocklingtonData07.get ⟨20, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8297 : Nat.Prime 8297 := by
  let d := lowPocklingtonData07.get ⟨21, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8311 : Nat.Prime 8311 := by
  let d := lowPocklingtonData07.get ⟨22, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8317 : Nat.Prime 8317 := by
  let d := lowPocklingtonData07.get ⟨23, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8329 : Nat.Prime 8329 := by
  let d := lowPocklingtonData07.get ⟨24, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8353 : Nat.Prime 8353 := by
  let d := lowPocklingtonData07.get ⟨25, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8363 : Nat.Prime 8363 := by
  let d := lowPocklingtonData07.get ⟨26, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8369 : Nat.Prime 8369 := by
  let d := lowPocklingtonData07.get ⟨27, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8377 : Nat.Prime 8377 := by
  let d := lowPocklingtonData07.get ⟨28, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8387 : Nat.Prime 8387 := by
  let d := lowPocklingtonData07.get ⟨29, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8389 : Nat.Prime 8389 := by
  let d := lowPocklingtonData07.get ⟨30, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8419 : Nat.Prime 8419 := by
  let d := lowPocklingtonData07.get ⟨31, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8423 : Nat.Prime 8423 := by
  let d := lowPocklingtonData07.get ⟨32, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8429 : Nat.Prime 8429 := by
  let d := lowPocklingtonData07.get ⟨33, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8431 : Nat.Prime 8431 := by
  let d := lowPocklingtonData07.get ⟨34, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8443 : Nat.Prime 8443 := by
  let d := lowPocklingtonData07.get ⟨35, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8447 : Nat.Prime 8447 := by
  let d := lowPocklingtonData07.get ⟨36, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8461 : Nat.Prime 8461 := by
  let d := lowPocklingtonData07.get ⟨37, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8467 : Nat.Prime 8467 := by
  let d := lowPocklingtonData07.get ⟨38, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8501 : Nat.Prime 8501 := by
  let d := lowPocklingtonData07.get ⟨39, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8513 : Nat.Prime 8513 := by
  let d := lowPocklingtonData07.get ⟨40, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8521 : Nat.Prime 8521 := by
  let d := lowPocklingtonData07.get ⟨41, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8527 : Nat.Prime 8527 := by
  let d := lowPocklingtonData07.get ⟨42, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8537 : Nat.Prime 8537 := by
  let d := lowPocklingtonData07.get ⟨43, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8539 : Nat.Prime 8539 := by
  let d := lowPocklingtonData07.get ⟨44, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8543 : Nat.Prime 8543 := by
  let d := lowPocklingtonData07.get ⟨45, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8563 : Nat.Prime 8563 := by
  let d := lowPocklingtonData07.get ⟨46, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8573 : Nat.Prime 8573 := by
  let d := lowPocklingtonData07.get ⟨47, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8581 : Nat.Prime 8581 := by
  let d := lowPocklingtonData07.get ⟨48, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8597 : Nat.Prime 8597 := by
  let d := lowPocklingtonData07.get ⟨49, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8599 : Nat.Prime 8599 := by
  let d := lowPocklingtonData07.get ⟨50, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8609 : Nat.Prime 8609 := by
  let d := lowPocklingtonData07.get ⟨51, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8623 : Nat.Prime 8623 := by
  let d := lowPocklingtonData07.get ⟨52, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8627 : Nat.Prime 8627 := by
  let d := lowPocklingtonData07.get ⟨53, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8629 : Nat.Prime 8629 := by
  let d := lowPocklingtonData07.get ⟨54, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8641 : Nat.Prime 8641 := by
  let d := lowPocklingtonData07.get ⟨55, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8647 : Nat.Prime 8647 := by
  let d := lowPocklingtonData07.get ⟨56, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8663 : Nat.Prime 8663 := by
  let d := lowPocklingtonData07.get ⟨57, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8669 : Nat.Prime 8669 := by
  let d := lowPocklingtonData07.get ⟨58, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8677 : Nat.Prime 8677 := by
  let d := lowPocklingtonData07.get ⟨59, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8681 : Nat.Prime 8681 := by
  let d := lowPocklingtonData07.get ⟨60, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8689 : Nat.Prime 8689 := by
  let d := lowPocklingtonData07.get ⟨61, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8693 : Nat.Prime 8693 := by
  let d := lowPocklingtonData07.get ⟨62, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8699 : Nat.Prime 8699 := by
  let d := lowPocklingtonData07.get ⟨63, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8707 : Nat.Prime 8707 := by
  let d := lowPocklingtonData07.get ⟨64, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8713 : Nat.Prime 8713 := by
  let d := lowPocklingtonData07.get ⟨65, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8719 : Nat.Prime 8719 := by
  let d := lowPocklingtonData07.get ⟨66, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8731 : Nat.Prime 8731 := by
  let d := lowPocklingtonData07.get ⟨67, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8737 : Nat.Prime 8737 := by
  let d := lowPocklingtonData07.get ⟨68, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8741 : Nat.Prime 8741 := by
  let d := lowPocklingtonData07.get ⟨69, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8747 : Nat.Prime 8747 := by
  let d := lowPocklingtonData07.get ⟨70, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8753 : Nat.Prime 8753 := by
  let d := lowPocklingtonData07.get ⟨71, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8761 : Nat.Prime 8761 := by
  let d := lowPocklingtonData07.get ⟨72, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8779 : Nat.Prime 8779 := by
  let d := lowPocklingtonData07.get ⟨73, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8783 : Nat.Prime 8783 := by
  let d := lowPocklingtonData07.get ⟨74, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8803 : Nat.Prime 8803 := by
  let d := lowPocklingtonData07.get ⟨75, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8807 : Nat.Prime 8807 := by
  let d := lowPocklingtonData07.get ⟨76, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8819 : Nat.Prime 8819 := by
  let d := lowPocklingtonData07.get ⟨77, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8821 : Nat.Prime 8821 := by
  let d := lowPocklingtonData07.get ⟨78, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8831 : Nat.Prime 8831 := by
  let d := lowPocklingtonData07.get ⟨79, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8837 : Nat.Prime 8837 := by
  let d := lowPocklingtonData07.get ⟨80, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8839 : Nat.Prime 8839 := by
  let d := lowPocklingtonData07.get ⟨81, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8849 : Nat.Prime 8849 := by
  let d := lowPocklingtonData07.get ⟨82, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8861 : Nat.Prime 8861 := by
  let d := lowPocklingtonData07.get ⟨83, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8863 : Nat.Prime 8863 := by
  let d := lowPocklingtonData07.get ⟨84, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8867 : Nat.Prime 8867 := by
  let d := lowPocklingtonData07.get ⟨85, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8887 : Nat.Prime 8887 := by
  let d := lowPocklingtonData07.get ⟨86, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8893 : Nat.Prime 8893 := by
  let d := lowPocklingtonData07.get ⟨87, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8923 : Nat.Prime 8923 := by
  let d := lowPocklingtonData07.get ⟨88, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8929 : Nat.Prime 8929 := by
  let d := lowPocklingtonData07.get ⟨89, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8933 : Nat.Prime 8933 := by
  let d := lowPocklingtonData07.get ⟨90, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8941 : Nat.Prime 8941 := by
  let d := lowPocklingtonData07.get ⟨91, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8951 : Nat.Prime 8951 := by
  let d := lowPocklingtonData07.get ⟨92, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp

theorem lowPrime_8963 : Nat.Prime 8963 := by
  let d := lowPocklingtonData07.get ⟨93, by simp [lowPocklingtonData07]⟩
  have hd : d ∈ lowPocklingtonData07 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData07_valid hd
  simpa [d, lowPocklingtonData07] using hp
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8111) (q := 8117) (by exact lowPrime_8117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8117) (q := 8123) (by exact lowPrime_8123) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8123) (q := 8147) (by exact lowPrime_8147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8147) (q := 8161) (by exact lowPrime_8161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8161) (q := 8167) (by exact lowPrime_8167) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8167) (q := 8171) (by exact lowPrime_8171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8171) (q := 8179) (by exact lowPrime_8179) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8179) (q := 8191) (by exact lowPrime_8191) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8518 (p := 8191) (q := 8209) (by exact lowPrime_8209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8209) (q := 8219) (by exact lowPrime_8219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8219) (q := 8221) (by exact lowPrime_8221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8221) (q := 8231) (by exact lowPrime_8231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8231) (q := 8233) (by exact lowPrime_8233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8233) (q := 8237) (by exact lowPrime_8237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8237) (q := 8243) (by exact lowPrime_8243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8243) (q := 8263) (by exact lowPrime_8263) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8518 (p := 8263) (q := 8269) (by exact lowPrime_8269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8269) (q := 8273) (by exact lowPrime_8273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8273) (q := 8287) (by exact lowPrime_8287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8287) (q := 8291) (by exact lowPrime_8291) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8291) (q := 8293) (by exact lowPrime_8293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8293) (q := 8297) (by exact lowPrime_8297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8297) (q := 8311) (by exact lowPrime_8311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8311) (q := 8317) (by exact lowPrime_8317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8518 (p := 8317) (q := 8329) (by exact lowPrime_8329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8329) (q := 8353) (by exact lowPrime_8353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8353) (q := 8363) (by exact lowPrime_8363) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8363) (q := 8369) (by exact lowPrime_8369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8369) (q := 8377) (by exact lowPrime_8377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8377) (q := 8387) (by exact lowPrime_8387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8387) (q := 8389) (by exact lowPrime_8389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8389) (q := 8419) (by exact lowPrime_8419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8518 (p := 8419) (q := 8423) (by exact lowPrime_8423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8423) (q := 8429) (by exact lowPrime_8429) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8429) (q := 8431) (by exact lowPrime_8431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8431) (q := 8443) (by exact lowPrime_8443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8443) (q := 8447) (by exact lowPrime_8447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8447) (q := 8461) (by exact lowPrime_8461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8461) (q := 8467) (by exact lowPrime_8467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8467) (q := 8501) (by exact lowPrime_8501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8518 (p := 8501) (q := 8513) (by exact lowPrime_8513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8513) (q := 8521) (by exact lowPrime_8521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8955 (p := 8521) (q := 8527) (by exact lowPrime_8527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8527) (q := 8537) (by exact lowPrime_8537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8537) (q := 8539) (by exact lowPrime_8539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8539) (q := 8543) (by exact lowPrime_8543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8543) (q := 8563) (by exact lowPrime_8563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8563) (q := 8573) (by exact lowPrime_8573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8573) (q := 8581) (by exact lowPrime_8581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8581) (q := 8597) (by exact lowPrime_8597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8955 (p := 8597) (q := 8599) (by exact lowPrime_8599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8599) (q := 8609) (by exact lowPrime_8609) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8609) (q := 8623) (by exact lowPrime_8623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8623) (q := 8627) (by exact lowPrime_8627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8627) (q := 8629) (by exact lowPrime_8629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8629) (q := 8641) (by exact lowPrime_8641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8641) (q := 8647) (by exact lowPrime_8647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8647) (q := 8663) (by exact lowPrime_8663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8955 (p := 8663) (q := 8669) (by exact lowPrime_8669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8669) (q := 8677) (by exact lowPrime_8677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8677) (q := 8681) (by exact lowPrime_8681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8681) (q := 8689) (by exact lowPrime_8689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8689) (q := 8693) (by exact lowPrime_8693) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8693) (q := 8699) (by exact lowPrime_8699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8699) (q := 8707) (by exact lowPrime_8707) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8707) (q := 8713) (by exact lowPrime_8713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8955 (p := 8713) (q := 8719) (by exact lowPrime_8719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8719) (q := 8731) (by exact lowPrime_8731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8731) (q := 8737) (by exact lowPrime_8737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8737) (q := 8741) (by exact lowPrime_8741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8741) (q := 8747) (by exact lowPrime_8747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8747) (q := 8753) (by exact lowPrime_8753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8753) (q := 8761) (by exact lowPrime_8761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8761) (q := 8779) (by exact lowPrime_8779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8955 (p := 8779) (q := 8783) (by exact lowPrime_8783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8783) (q := 8803) (by exact lowPrime_8803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8803) (q := 8807) (by exact lowPrime_8807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8807) (q := 8819) (by exact lowPrime_8819) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8819) (q := 8821) (by exact lowPrime_8821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8821) (q := 8831) (by exact lowPrime_8831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8831) (q := 8837) (by exact lowPrime_8837) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8837) (q := 8839) (by exact lowPrime_8839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8955 (p := 8839) (q := 8849) (by exact lowPrime_8849) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8849) (q := 8861) (by exact lowPrime_8861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8861) (q := 8863) (by exact lowPrime_8863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8863) (q := 8867) (by exact lowPrime_8867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8867) (q := 8887) (by exact lowPrime_8887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8887) (q := 8893) (by exact lowPrime_8893) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8893) (q := 8923) (by exact lowPrime_8923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8923) (q := 8929) (by exact lowPrime_8929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8955 (p := 8929) (q := 8933) (by exact lowPrime_8933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8933) (q := 8941) (by exact lowPrime_8941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8941) (q := 8951) (by exact lowPrime_8951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8951) (q := 8963) (by exact lowPrime_8963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
