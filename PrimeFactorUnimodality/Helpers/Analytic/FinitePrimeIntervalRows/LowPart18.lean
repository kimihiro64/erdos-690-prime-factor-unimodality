import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 18 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData18 : List PocklingtonData := [
    { n := 20963, F := 20962, R := 1, a := 2, factors := [2, 47, 223], residues := [(2, 10481), (47, 2605), (223, 13538)] },
    { n := 20981, F := 20980, R := 1, a := 2, factors := [2, 2, 5, 1049], residues := [(2, 10490), (5, 13824), (1049, 15283)] },
    { n := 20983, F := 20982, R := 1, a := 3, factors := [2, 3, 13, 269], residues := [(2, 10491), (3, 7423), (13, 9829), (269, 16158)] },
    { n := 21001, F := 21000, R := 1, a := 11, factors := [2, 2, 2, 3, 5, 5, 5, 7], residues := [(2, 10500), (3, 18609), (5, 14647), (7, 16569)] },
    { n := 21011, F := 21010, R := 1, a := 2, factors := [2, 5, 11, 191], residues := [(2, 10505), (5, 19680), (11, 11131), (191, 6142)] },
    { n := 21013, F := 21012, R := 1, a := 2, factors := [2, 2, 3, 17, 103], residues := [(2, 10506), (3, 11232), (17, 17301), (103, 14723)] },
    { n := 21017, F := 21016, R := 1, a := 3, factors := [2, 2, 2, 37, 71], residues := [(2, 10508), (37, 3230), (71, 20654)] },
    { n := 21019, F := 21018, R := 1, a := 2, factors := [2, 3, 31, 113], residues := [(2, 10509), (3, 12441), (31, 11386), (113, 612)] },
    { n := 21023, F := 21022, R := 1, a := 5, factors := [2, 23, 457], residues := [(2, 10511), (23, 18711), (457, 5355)] },
    { n := 21031, F := 21030, R := 1, a := 12, factors := [2, 3, 5, 701], residues := [(2, 10515), (3, 7627), (5, 15934), (701, 16696)] },
    { n := 21059, F := 21058, R := 1, a := 2, factors := [2, 10529], residues := [(2, 10529), (10529, 7020)] },
    { n := 21061, F := 21060, R := 1, a := 7, factors := [2, 2, 3, 3, 3, 3, 5, 13], residues := [(2, 10530), (3, 12915), (5, 529), (13, 13446)] },
    { n := 21067, F := 21066, R := 1, a := 2, factors := [2, 3, 3511], residues := [(2, 10533), (3, 15271), (3511, 1672)] },
    { n := 21089, F := 21088, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 659], residues := [(2, 10544), (659, 8655)] },
    { n := 21101, F := 21100, R := 1, a := 2, factors := [2, 2, 5, 5, 211], residues := [(2, 10550), (5, 2119), (211, 15408)] },
    { n := 21107, F := 21106, R := 1, a := 2, factors := [2, 61, 173], residues := [(2, 10553), (61, 17377), (173, 13322)] },
    { n := 21121, F := 21120, R := 1, a := 19, factors := [2, 2, 2, 2, 2, 2, 2, 3, 5, 11], residues := [(2, 10560), (3, 2389), (5, 9902), (11, 11164)] },
    { n := 21139, F := 21138, R := 1, a := 2, factors := [2, 3, 13, 271], residues := [(2, 10569), (3, 18266), (13, 12453), (271, 10898)] },
    { n := 21143, F := 21142, R := 1, a := 10, factors := [2, 11, 31, 31], residues := [(2, 10571), (11, 18834), (31, 17618)] },
    { n := 21149, F := 21148, R := 1, a := 3, factors := [2, 2, 17, 311], residues := [(2, 10574), (17, 10869), (311, 17833)] },
    { n := 21157, F := 21156, R := 1, a := 2, factors := [2, 2, 3, 41, 43], residues := [(2, 10578), (3, 12964), (41, 14634), (43, 9862)] },
    { n := 21163, F := 21162, R := 1, a := 2, factors := [2, 3, 3527], residues := [(2, 10581), (3, 15554), (3527, 12765)] },
    { n := 21169, F := 21168, R := 1, a := 13, factors := [2, 2, 2, 2, 3, 3, 3, 7, 7], residues := [(2, 10584), (3, 10542), (7, 17432)] },
    { n := 21179, F := 21178, R := 1, a := 2, factors := [2, 10589], residues := [(2, 10589), (10589, 7060)] },
    { n := 22501, F := 22500, R := 1, a := 2, factors := [2, 2, 3, 3, 5, 5, 5, 5], residues := [(2, 11250), (3, 22123), (5, 12352)] },
    { n := 22511, F := 22510, R := 1, a := 11, factors := [2, 5, 2251], residues := [(2, 11255), (5, 18241), (2251, 6132)] },
    { n := 22531, F := 22530, R := 1, a := 2, factors := [2, 3, 5, 751], residues := [(2, 11265), (3, 6895), (5, 1411), (751, 5398)] },
    { n := 22541, F := 22540, R := 1, a := 3, factors := [2, 2, 5, 7, 7, 23], residues := [(2, 11270), (5, 8480), (7, 14204), (23, 5277)] },
    { n := 22543, F := 22542, R := 1, a := 3, factors := [2, 3, 13, 17, 17], residues := [(2, 11271), (3, 2356), (13, 19884), (17, 3819)] },
    { n := 22549, F := 22548, R := 1, a := 2, factors := [2, 2, 3, 1879], residues := [(2, 11274), (3, 18397), (1879, 16167)] },
    { n := 22567, F := 22566, R := 1, a := 3, factors := [2, 3, 3761], residues := [(2, 11283), (3, 3094), (3761, 31)] },
    { n := 22571, F := 22570, R := 1, a := 6, factors := [2, 5, 37, 61], residues := [(2, 11285), (5, 684), (37, 7865), (61, 5635)] },
    { n := 22573, F := 22572, R := 1, a := 6, factors := [2, 2, 3, 3, 3, 11, 19], residues := [(2, 11286), (3, 22343), (11, 3116), (19, 11415)] },
    { n := 22613, F := 22612, R := 1, a := 2, factors := [2, 2, 5653], residues := [(2, 11306), (5653, 19598)] },
    { n := 22619, F := 22618, R := 1, a := 2, factors := [2, 43, 263], residues := [(2, 11309), (43, 9202), (263, 18294)] },
    { n := 22621, F := 22620, R := 1, a := 2, factors := [2, 2, 3, 5, 13, 29], residues := [(2, 11310), (3, 3177), (5, 4113), (13, 8522), (29, 19055)] },
    { n := 22637, F := 22636, R := 1, a := 2, factors := [2, 2, 5659], residues := [(2, 11318), (5659, 10564)] },
    { n := 22639, F := 22638, R := 1, a := 6, factors := [2, 3, 7, 7, 7, 11], residues := [(2, 11319), (3, 15273), (7, 17224), (11, 21493)] },
    { n := 22643, F := 22642, R := 1, a := 2, factors := [2, 11321], residues := [(2, 11321), (11321, 7548)] },
    { n := 22651, F := 22650, R := 1, a := 3, factors := [2, 3, 5, 5, 151], residues := [(2, 11325), (3, 7600), (5, 17127), (151, 15613)] },
    { n := 22669, F := 22668, R := 1, a := 2, factors := [2, 2, 3, 1889], residues := [(2, 11334), (3, 19656), (1889, 16170)] },
    { n := 22679, F := 22678, R := 1, a := 13, factors := [2, 17, 23, 29], residues := [(2, 11339), (17, 13971), (23, 11157), (29, 20717)] },
    { n := 22691, F := 22690, R := 1, a := 2, factors := [2, 5, 2269], residues := [(2, 11345), (5, 4024), (2269, 2085)] },
    { n := 22697, F := 22696, R := 1, a := 3, factors := [2, 2, 2, 2837], residues := [(2, 11348), (2837, 8328)] },
    { n := 22699, F := 22698, R := 1, a := 12, factors := [2, 3, 3, 13, 97], residues := [(2, 11349), (3, 10993), (13, 1796), (97, 10634)] },
    { n := 22709, F := 22708, R := 1, a := 2, factors := [2, 2, 7, 811], residues := [(2, 11354), (7, 20398), (811, 10825)] },
    { n := 22717, F := 22716, R := 1, a := 2, factors := [2, 2, 3, 3, 631], residues := [(2, 11358), (3, 18270), (631, 9265)] },
    { n := 22721, F := 22720, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 5, 71], residues := [(2, 11360), (5, 3097), (71, 12059)] },
    { n := 22727, F := 22726, R := 1, a := 5, factors := [2, 11, 1033], residues := [(2, 11363), (11, 204), (1033, 3198)] },
    { n := 22739, F := 22738, R := 1, a := 2, factors := [2, 11369], residues := [(2, 11369), (11369, 7580)] },
    { n := 22741, F := 22740, R := 1, a := 7, factors := [2, 2, 3, 5, 379], residues := [(2, 11370), (3, 11710), (5, 21469), (379, 5849)] },
    { n := 22751, F := 22750, R := 1, a := 21, factors := [2, 5, 5, 5, 7, 13], residues := [(2, 11375), (5, 9314), (7, 18789), (13, 393)] },
    { n := 22769, F := 22768, R := 1, a := 3, factors := [2, 2, 2, 2, 1423], residues := [(2, 11384), (1423, 7905)] },
    { n := 22777, F := 22776, R := 1, a := 7, factors := [2, 2, 2, 3, 13, 73], residues := [(2, 11388), (3, 14604), (13, 18627), (73, 4555)] },
    { n := 22783, F := 22782, R := 1, a := 3, factors := [2, 3, 3797], residues := [(2, 11391), (3, 7182), (3797, 6040)] },
    { n := 22787, F := 22786, R := 1, a := 2, factors := [2, 11393], residues := [(2, 11393), (11393, 7596)] },
    { n := 22807, F := 22806, R := 1, a := 3, factors := [2, 3, 3, 7, 181], residues := [(2, 11403), (3, 12539), (7, 16923), (181, 14424)] },
    { n := 22811, F := 22810, R := 1, a := 6, factors := [2, 5, 2281], residues := [(2, 11405), (5, 12253), (2281, 548)] },
    { n := 22817, F := 22816, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 23, 31], residues := [(2, 11408), (23, 7296), (31, 13965)] },
    { n := 22853, F := 22852, R := 1, a := 2, factors := [2, 2, 29, 197], residues := [(2, 11426), (29, 5735), (197, 14094)] },
    { n := 22859, F := 22858, R := 1, a := 2, factors := [2, 11, 1039], residues := [(2, 11429), (11, 10199), (1039, 13673)] },
    { n := 22861, F := 22860, R := 1, a := 2, factors := [2, 2, 3, 3, 5, 127], residues := [(2, 11430), (3, 16488), (5, 13064), (127, 9978)] },
    { n := 22871, F := 22870, R := 1, a := 7, factors := [2, 5, 2287], residues := [(2, 11435), (5, 1417), (2287, 1130)] },
    { n := 22877, F := 22876, R := 1, a := 2, factors := [2, 2, 7, 19, 43], residues := [(2, 11438), (7, 483), (19, 20321), (43, 9915)] },
    { n := 22901, F := 22900, R := 1, a := 2, factors := [2, 2, 5, 5, 229], residues := [(2, 11450), (5, 15056), (229, 15651)] },
    { n := 22907, F := 22906, R := 1, a := 5, factors := [2, 13, 881], residues := [(2, 11453), (13, 19813), (881, 14995)] },
    { n := 22921, F := 22920, R := 1, a := 7, factors := [2, 2, 2, 3, 5, 191], residues := [(2, 11460), (3, 2817), (5, 350), (191, 12084)] },
    { n := 22937, F := 22936, R := 1, a := 3, factors := [2, 2, 2, 47, 61], residues := [(2, 11468), (47, 20600), (61, 1295)] },
    { n := 22943, F := 22942, R := 1, a := 5, factors := [2, 11471], residues := [(2, 11471), (11471, 956)] },
    { n := 22961, F := 22960, R := 1, a := 6, factors := [2, 2, 2, 2, 5, 7, 41], residues := [(2, 11480), (5, 16506), (7, 11552), (41, 16694)] },
    { n := 22963, F := 22962, R := 1, a := 3, factors := [2, 3, 43, 89], residues := [(2, 11481), (3, 20807), (43, 4131), (89, 5759)] },
    { n := 22973, F := 22972, R := 1, a := 2, factors := [2, 2, 5743], residues := [(2, 11486), (5743, 19910)] },
    { n := 22993, F := 22992, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 479], residues := [(2, 11496), (3, 14846), (479, 14343)] },
    { n := 23003, F := 23002, R := 1, a := 2, factors := [2, 7, 31, 53], residues := [(2, 11501), (7, 8451), (31, 3168), (53, 7355)] },
    { n := 23011, F := 23010, R := 1, a := 7, factors := [2, 3, 5, 13, 59], residues := [(2, 11505), (3, 5303), (5, 11398), (13, 6664), (59, 4153)] },
    { n := 23017, F := 23016, R := 1, a := 5, factors := [2, 2, 2, 3, 7, 137], residues := [(2, 11508), (3, 1872), (7, 4639), (137, 8314)] },
    { n := 23021, F := 23020, R := 1, a := 2, factors := [2, 2, 5, 1151], residues := [(2, 11510), (5, 10529), (1151, 20759)] },
    { n := 23027, F := 23026, R := 1, a := 2, factors := [2, 29, 397], residues := [(2, 11513), (29, 5365), (397, 6703)] },
    { n := 23029, F := 23028, R := 1, a := 2, factors := [2, 2, 3, 19, 101], residues := [(2, 11514), (3, 7542), (19, 6698), (101, 1123)] },
    { n := 23039, F := 23038, R := 1, a := 7, factors := [2, 11519], residues := [(2, 11519), (11519, 480)] },
    { n := 23041, F := 23040, R := 1, a := 11, factors := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5], residues := [(2, 11520), (3, 1360), (5, 15797)] },
    { n := 23053, F := 23052, R := 1, a := 2, factors := [2, 2, 3, 17, 113], residues := [(2, 11526), (3, 1033), (17, 11285), (113, 7904)] },
    { n := 23057, F := 23056, R := 1, a := 5, factors := [2, 2, 2, 2, 11, 131], residues := [(2, 11528), (11, 4427), (131, 14769)] },
    { n := 23059, F := 23058, R := 1, a := 3, factors := [2, 3, 3, 3, 7, 61], residues := [(2, 11529), (3, 3645), (7, 16323), (61, 11565)] },
    { n := 23063, F := 23062, R := 1, a := 5, factors := [2, 13, 887], residues := [(2, 11531), (13, 6926), (887, 18685)] },
    { n := 23071, F := 23070, R := 1, a := 3, factors := [2, 3, 5, 769], residues := [(2, 11535), (3, 6944), (5, 7634), (769, 11219)] },
    { n := 23081, F := 23080, R := 1, a := 3, factors := [2, 2, 2, 5, 577], residues := [(2, 11540), (5, 9804), (577, 16919)] },
    { n := 23087, F := 23086, R := 1, a := 5, factors := [2, 7, 17, 97], residues := [(2, 11543), (7, 12677), (17, 16477), (97, 10451)] },
    { n := 23099, F := 23098, R := 1, a := 2, factors := [2, 11549], residues := [(2, 11549), (11549, 7700)] },
    { n := 23117, F := 23116, R := 1, a := 2, factors := [2, 2, 5779], residues := [(2, 11558), (5779, 10788)] },
    { n := 23131, F := 23130, R := 1, a := 3, factors := [2, 3, 3, 5, 257], residues := [(2, 11565), (3, 1293), (5, 19702), (257, 5462)] },
    { n := 23143, F := 23142, R := 1, a := 5, factors := [2, 3, 7, 19, 29], residues := [(2, 11571), (3, 2510), (7, 4097), (19, 6881), (29, 11025)] },
    { n := 23159, F := 23158, R := 1, a := 11, factors := [2, 11579], residues := [(2, 11579), (11579, 193)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData18_valid : PocklingtonRow.Valid lowPocklingtonData18 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPrime_20963 : Nat.Prime 20963 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_20981 : Nat.Prime 20981 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_20983 : Nat.Prime 20983 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21001 : Nat.Prime 21001 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21011 : Nat.Prime 21011 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21013 : Nat.Prime 21013 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21017 : Nat.Prime 21017 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21019 : Nat.Prime 21019 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21023 : Nat.Prime 21023 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21031 : Nat.Prime 21031 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21059 : Nat.Prime 21059 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21061 : Nat.Prime 21061 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21067 : Nat.Prime 21067 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21089 : Nat.Prime 21089 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21101 : Nat.Prime 21101 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21107 : Nat.Prime 21107 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21121 : Nat.Prime 21121 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21139 : Nat.Prime 21139 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21143 : Nat.Prime 21143 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21149 : Nat.Prime 21149 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21157 : Nat.Prime 21157 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21163 : Nat.Prime 21163 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21169 : Nat.Prime 21169 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_21179 : Nat.Prime 21179 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22501 : Nat.Prime 22501 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22511 : Nat.Prime 22511 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22531 : Nat.Prime 22531 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22541 : Nat.Prime 22541 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22543 : Nat.Prime 22543 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22549 : Nat.Prime 22549 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22567 : Nat.Prime 22567 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22571 : Nat.Prime 22571 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22573 : Nat.Prime 22573 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22613 : Nat.Prime 22613 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22619 : Nat.Prime 22619 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22621 : Nat.Prime 22621 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22637 : Nat.Prime 22637 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22639 : Nat.Prime 22639 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22643 : Nat.Prime 22643 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22651 : Nat.Prime 22651 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22669 : Nat.Prime 22669 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22679 : Nat.Prime 22679 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22691 : Nat.Prime 22691 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22697 : Nat.Prime 22697 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22699 : Nat.Prime 22699 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22709 : Nat.Prime 22709 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22717 : Nat.Prime 22717 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22721 : Nat.Prime 22721 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22727 : Nat.Prime 22727 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22739 : Nat.Prime 22739 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22741 : Nat.Prime 22741 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22751 : Nat.Prime 22751 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22769 : Nat.Prime 22769 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22777 : Nat.Prime 22777 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22783 : Nat.Prime 22783 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22787 : Nat.Prime 22787 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22807 : Nat.Prime 22807 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22811 : Nat.Prime 22811 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22817 : Nat.Prime 22817 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22853 : Nat.Prime 22853 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22859 : Nat.Prime 22859 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22861 : Nat.Prime 22861 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22871 : Nat.Prime 22871 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22877 : Nat.Prime 22877 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22901 : Nat.Prime 22901 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22907 : Nat.Prime 22907 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22921 : Nat.Prime 22921 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22937 : Nat.Prime 22937 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22943 : Nat.Prime 22943 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22961 : Nat.Prime 22961 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22963 : Nat.Prime 22963 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22973 : Nat.Prime 22973 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_22993 : Nat.Prime 22993 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23003 : Nat.Prime 23003 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23011 : Nat.Prime 23011 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23017 : Nat.Prime 23017 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23021 : Nat.Prime 23021 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23027 : Nat.Prime 23027 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23029 : Nat.Prime 23029 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23039 : Nat.Prime 23039 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23041 : Nat.Prime 23041 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23053 : Nat.Prime 23053 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23057 : Nat.Prime 23057 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23059 : Nat.Prime 23059 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23063 : Nat.Prime 23063 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23071 : Nat.Prime 23071 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23081 : Nat.Prime 23081 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23087 : Nat.Prime 23087 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23099 : Nat.Prime 23099 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23117 : Nat.Prime 23117 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23131 : Nat.Prime 23131 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23143 : Nat.Prime 23143 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]

theorem lowPrime_23159 : Nat.Prime 23159 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData18_valid
  simp [lowPocklingtonData18]
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22483) (q := 22501) (by exact lowPrime_22501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22501) (q := 22511) (by exact lowPrime_22511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22511) (q := 22531) (by exact lowPrime_22531) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22531) (q := 22541) (by exact lowPrime_22541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22541) (q := 22543) (by exact lowPrime_22543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22543) (q := 22549) (by exact lowPrime_22549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22549) (q := 22567) (by exact lowPrime_22567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22567) (q := 22571) (by exact lowPrime_22571) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part07_chain :
    DusartPrimeRowsChain 22483 22570 dusartPrimeRows_22027_23158_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22571) (q := 22573) (by exact lowPrime_22573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22573) (q := 22613) (by exact lowPrime_22613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22613) (q := 22619) (by exact lowPrime_22619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22619) (q := 22621) (by exact lowPrime_22621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22621) (q := 22637) (by exact lowPrime_22637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22637) (q := 22639) (by exact lowPrime_22639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22639) (q := 22643) (by exact lowPrime_22643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22643) (q := 22651) (by exact lowPrime_22651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part08_chain :
    DusartPrimeRowsChain 22571 22650 dusartPrimeRows_22027_23158_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22651) (q := 22669) (by exact lowPrime_22669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22669) (q := 22679) (by exact lowPrime_22679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22679) (q := 22691) (by exact lowPrime_22691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22691) (q := 22697) (by exact lowPrime_22697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22697) (q := 22699) (by exact lowPrime_22699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22699) (q := 22709) (by exact lowPrime_22709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22709) (q := 22717) (by exact lowPrime_22717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22717) (q := 22721) (by exact lowPrime_22721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part09_chain :
    DusartPrimeRowsChain 22651 22720 dusartPrimeRows_22027_23158_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22721) (q := 22727) (by exact lowPrime_22727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22727) (q := 22739) (by exact lowPrime_22739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22739) (q := 22741) (by exact lowPrime_22741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22741) (q := 22751) (by exact lowPrime_22751) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22751) (q := 22769) (by exact lowPrime_22769) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22769) (q := 22777) (by exact lowPrime_22777) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22777) (q := 22783) (by exact lowPrime_22783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22783) (q := 22787) (by exact lowPrime_22787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part10_chain :
    DusartPrimeRowsChain 22721 22786 dusartPrimeRows_22027_23158_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22787) (q := 22807) (by exact lowPrime_22807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22807) (q := 22811) (by exact lowPrime_22811) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22811) (q := 22817) (by exact lowPrime_22817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22817) (q := 22853) (by exact lowPrime_22853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22853) (q := 22859) (by exact lowPrime_22859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22859) (q := 22861) (by exact lowPrime_22861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22861) (q := 22871) (by exact lowPrime_22871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22871) (q := 22877) (by exact lowPrime_22877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part11_chain :
    DusartPrimeRowsChain 22787 22876 dusartPrimeRows_22027_23158_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22877) (q := 22901) (by exact lowPrime_22901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22901) (q := 22907) (by exact lowPrime_22907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22907) (q := 22921) (by exact lowPrime_22921) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22921) (q := 22937) (by exact lowPrime_22937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22937) (q := 22943) (by exact lowPrime_22943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22943) (q := 22961) (by exact lowPrime_22961) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22961) (q := 22963) (by exact lowPrime_22963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22963) (q := 22973) (by exact lowPrime_22973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part12_chain :
    DusartPrimeRowsChain 22877 22972 dusartPrimeRows_22027_23158_part12 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22973) (q := 22993) (by exact lowPrime_22993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22993) (q := 23003) (by exact lowPrime_23003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23003) (q := 23011) (by exact lowPrime_23011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23011) (q := 23017) (by exact lowPrime_23017) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23017) (q := 23021) (by exact lowPrime_23021) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23021) (q := 23027) (by exact lowPrime_23027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23027) (q := 23029) (by exact lowPrime_23029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23029) (q := 23039) (by exact lowPrime_23039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part13_chain :
    DusartPrimeRowsChain 22973 23038 dusartPrimeRows_22027_23158_part13 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part14 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 23039) (q := 23041) (by exact lowPrime_23041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23041) (q := 23053) (by exact lowPrime_23053) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23053) (q := 23057) (by exact lowPrime_23057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23057) (q := 23059) (by exact lowPrime_23059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23059) (q := 23063) (by exact lowPrime_23063) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23063) (q := 23071) (by exact lowPrime_23071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23071) (q := 23081) (by exact lowPrime_23081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23081) (q := 23087) (by exact lowPrime_23087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part14_chain :
    DusartPrimeRowsChain 23039 23086 dusartPrimeRows_22027_23158_part14 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part15 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 23087) (q := 23099) (by exact lowPrime_23099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23099) (q := 23117) (by exact lowPrime_23117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23117) (q := 23131) (by exact lowPrime_23131) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23131) (q := 23143) (by exact lowPrime_23143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23143) (q := 23159) (by exact lowPrime_23159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part15_chain :
    DusartPrimeRowsChain 23087 23158 dusartPrimeRows_22027_23158_part15 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.empty
            norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 20959) (q := 20963) (by exact lowPrime_20963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20963) (q := 20981) (by exact lowPrime_20981) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20981) (q := 20983) (by exact lowPrime_20983) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20983) (q := 21001) (by exact lowPrime_21001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21001) (q := 21011) (by exact lowPrime_21011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21011) (q := 21013) (by exact lowPrime_21013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21013) (q := 21017) (by exact lowPrime_21017) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21017) (q := 21019) (by exact lowPrime_21019) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part01_chain :
    DusartPrimeRowsChain 20959 21018 dusartPrimeRows_20959_22026_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21019) (q := 21023) (by exact lowPrime_21023) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21023) (q := 21031) (by exact lowPrime_21031) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21031) (q := 21059) (by exact lowPrime_21059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21059) (q := 21061) (by exact lowPrime_21061) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21061) (q := 21067) (by exact lowPrime_21067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21067) (q := 21089) (by exact lowPrime_21089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21089) (q := 21101) (by exact lowPrime_21101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21101) (q := 21107) (by exact lowPrime_21107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part02_chain :
    DusartPrimeRowsChain 21019 21106 dusartPrimeRows_20959_22026_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21107) (q := 21121) (by exact lowPrime_21121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21121) (q := 21139) (by exact lowPrime_21139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21139) (q := 21143) (by exact lowPrime_21143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21143) (q := 21149) (by exact lowPrime_21149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21149) (q := 21157) (by exact lowPrime_21157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21157) (q := 21163) (by exact lowPrime_21163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21163) (q := 21169) (by exact lowPrime_21169) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21169) (q := 21179) (by exact lowPrime_21179) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part03_chain :
    DusartPrimeRowsChain 21107 21178 dusartPrimeRows_20959_22026_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]
