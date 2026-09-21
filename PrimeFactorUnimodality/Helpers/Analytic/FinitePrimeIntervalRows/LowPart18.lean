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

theorem lowPocklingtonPrime18 (i : Fin lowPocklingtonData18.length) :
    Nat.Prime (lowPocklingtonData18.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData18_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22483) (q := 22501) (by
      have hp := lowPocklingtonPrime18 ⟨24, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22501) (q := 22511) (by
      have hp := lowPocklingtonPrime18 ⟨25, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22511) (q := 22531) (by
      have hp := lowPocklingtonPrime18 ⟨26, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22531) (q := 22541) (by
      have hp := lowPocklingtonPrime18 ⟨27, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22541) (q := 22543) (by
      have hp := lowPocklingtonPrime18 ⟨28, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22543) (q := 22549) (by
      have hp := lowPocklingtonPrime18 ⟨29, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22549) (q := 22567) (by
      have hp := lowPocklingtonPrime18 ⟨30, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22567) (q := 22571) (by
      have hp := lowPocklingtonPrime18 ⟨31, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_23155 (p := 22571) (q := 22573) (by
      have hp := lowPocklingtonPrime18 ⟨32, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22573) (q := 22613) (by
      have hp := lowPocklingtonPrime18 ⟨33, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22613) (q := 22619) (by
      have hp := lowPocklingtonPrime18 ⟨34, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22619) (q := 22621) (by
      have hp := lowPocklingtonPrime18 ⟨35, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22621) (q := 22637) (by
      have hp := lowPocklingtonPrime18 ⟨36, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22637) (q := 22639) (by
      have hp := lowPocklingtonPrime18 ⟨37, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22639) (q := 22643) (by
      have hp := lowPocklingtonPrime18 ⟨38, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22643) (q := 22651) (by
      have hp := lowPocklingtonPrime18 ⟨39, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_23155 (p := 22651) (q := 22669) (by
      have hp := lowPocklingtonPrime18 ⟨40, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22669) (q := 22679) (by
      have hp := lowPocklingtonPrime18 ⟨41, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22679) (q := 22691) (by
      have hp := lowPocklingtonPrime18 ⟨42, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22691) (q := 22697) (by
      have hp := lowPocklingtonPrime18 ⟨43, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22697) (q := 22699) (by
      have hp := lowPocklingtonPrime18 ⟨44, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22699) (q := 22709) (by
      have hp := lowPocklingtonPrime18 ⟨45, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22709) (q := 22717) (by
      have hp := lowPocklingtonPrime18 ⟨46, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22717) (q := 22721) (by
      have hp := lowPocklingtonPrime18 ⟨47, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_23155 (p := 22721) (q := 22727) (by
      have hp := lowPocklingtonPrime18 ⟨48, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22727) (q := 22739) (by
      have hp := lowPocklingtonPrime18 ⟨49, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22739) (q := 22741) (by
      have hp := lowPocklingtonPrime18 ⟨50, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22741) (q := 22751) (by
      have hp := lowPocklingtonPrime18 ⟨51, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22751) (q := 22769) (by
      have hp := lowPocklingtonPrime18 ⟨52, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22769) (q := 22777) (by
      have hp := lowPocklingtonPrime18 ⟨53, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22777) (q := 22783) (by
      have hp := lowPocklingtonPrime18 ⟨54, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22783) (q := 22787) (by
      have hp := lowPocklingtonPrime18 ⟨55, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_23155 (p := 22787) (q := 22807) (by
      have hp := lowPocklingtonPrime18 ⟨56, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22807) (q := 22811) (by
      have hp := lowPocklingtonPrime18 ⟨57, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22811) (q := 22817) (by
      have hp := lowPocklingtonPrime18 ⟨58, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22817) (q := 22853) (by
      have hp := lowPocklingtonPrime18 ⟨59, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22853) (q := 22859) (by
      have hp := lowPocklingtonPrime18 ⟨60, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22859) (q := 22861) (by
      have hp := lowPocklingtonPrime18 ⟨61, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22861) (q := 22871) (by
      have hp := lowPocklingtonPrime18 ⟨62, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22871) (q := 22877) (by
      have hp := lowPocklingtonPrime18 ⟨63, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_23155 (p := 22877) (q := 22901) (by
      have hp := lowPocklingtonPrime18 ⟨64, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22901) (q := 22907) (by
      have hp := lowPocklingtonPrime18 ⟨65, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22907) (q := 22921) (by
      have hp := lowPocklingtonPrime18 ⟨66, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22921) (q := 22937) (by
      have hp := lowPocklingtonPrime18 ⟨67, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22937) (q := 22943) (by
      have hp := lowPocklingtonPrime18 ⟨68, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22943) (q := 22961) (by
      have hp := lowPocklingtonPrime18 ⟨69, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22961) (q := 22963) (by
      have hp := lowPocklingtonPrime18 ⟨70, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22963) (q := 22973) (by
      have hp := lowPocklingtonPrime18 ⟨71, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_23155 (p := 22973) (q := 22993) (by
      have hp := lowPocklingtonPrime18 ⟨72, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22993) (q := 23003) (by
      have hp := lowPocklingtonPrime18 ⟨73, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23003) (q := 23011) (by
      have hp := lowPocklingtonPrime18 ⟨74, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23011) (q := 23017) (by
      have hp := lowPocklingtonPrime18 ⟨75, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23017) (q := 23021) (by
      have hp := lowPocklingtonPrime18 ⟨76, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23021) (q := 23027) (by
      have hp := lowPocklingtonPrime18 ⟨77, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23027) (q := 23029) (by
      have hp := lowPocklingtonPrime18 ⟨78, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23029) (q := 23039) (by
      have hp := lowPocklingtonPrime18 ⟨79, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_23155 (p := 23039) (q := 23041) (by
      have hp := lowPocklingtonPrime18 ⟨80, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23041) (q := 23053) (by
      have hp := lowPocklingtonPrime18 ⟨81, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23053) (q := 23057) (by
      have hp := lowPocklingtonPrime18 ⟨82, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23057) (q := 23059) (by
      have hp := lowPocklingtonPrime18 ⟨83, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23059) (q := 23063) (by
      have hp := lowPocklingtonPrime18 ⟨84, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23063) (q := 23071) (by
      have hp := lowPocklingtonPrime18 ⟨85, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23071) (q := 23081) (by
      have hp := lowPocklingtonPrime18 ⟨86, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23081) (q := 23087) (by
      have hp := lowPocklingtonPrime18 ⟨87, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_23155 (p := 23087) (q := 23099) (by
      have hp := lowPocklingtonPrime18 ⟨88, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23099) (q := 23117) (by
      have hp := lowPocklingtonPrime18 ⟨89, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23117) (q := 23131) (by
      have hp := lowPocklingtonPrime18 ⟨90, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23131) (q := 23143) (by
      have hp := lowPocklingtonPrime18 ⟨91, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23143) (q := 23159) (by
      have hp := lowPocklingtonPrime18 ⟨92, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_22026 (p := 20959) (q := 20963) (by
      have hp := lowPocklingtonPrime18 ⟨0, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20963) (q := 20981) (by
      have hp := lowPocklingtonPrime18 ⟨1, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20981) (q := 20983) (by
      have hp := lowPocklingtonPrime18 ⟨2, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20983) (q := 21001) (by
      have hp := lowPocklingtonPrime18 ⟨3, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21001) (q := 21011) (by
      have hp := lowPocklingtonPrime18 ⟨4, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21011) (q := 21013) (by
      have hp := lowPocklingtonPrime18 ⟨5, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21013) (q := 21017) (by
      have hp := lowPocklingtonPrime18 ⟨6, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21017) (q := 21019) (by
      have hp := lowPocklingtonPrime18 ⟨7, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_22026 (p := 21019) (q := 21023) (by
      have hp := lowPocklingtonPrime18 ⟨8, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21023) (q := 21031) (by
      have hp := lowPocklingtonPrime18 ⟨9, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21031) (q := 21059) (by
      have hp := lowPocklingtonPrime18 ⟨10, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21059) (q := 21061) (by
      have hp := lowPocklingtonPrime18 ⟨11, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21061) (q := 21067) (by
      have hp := lowPocklingtonPrime18 ⟨12, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21067) (q := 21089) (by
      have hp := lowPocklingtonPrime18 ⟨13, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21089) (q := 21101) (by
      have hp := lowPocklingtonPrime18 ⟨14, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21101) (q := 21107) (by
      have hp := lowPocklingtonPrime18 ⟨15, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_22026 (p := 21107) (q := 21121) (by
      have hp := lowPocklingtonPrime18 ⟨16, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21121) (q := 21139) (by
      have hp := lowPocklingtonPrime18 ⟨17, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21139) (q := 21143) (by
      have hp := lowPocklingtonPrime18 ⟨18, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21143) (q := 21149) (by
      have hp := lowPocklingtonPrime18 ⟨19, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21149) (q := 21157) (by
      have hp := lowPocklingtonPrime18 ⟨20, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21157) (q := 21163) (by
      have hp := lowPocklingtonPrime18 ⟨21, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21163) (q := 21169) (by
      have hp := lowPocklingtonPrime18 ⟨22, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21169) (q := 21179) (by
      have hp := lowPocklingtonPrime18 ⟨23, by simp [lowPocklingtonData18]⟩
      simpa [lowPocklingtonData18] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
