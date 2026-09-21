import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 21 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData21 : List PocklingtonData := [
    { n := 18973, F := 18972, R := 1, a := 2, factors := [2, 2, 3, 3, 17, 31], residues := [(2, 9486), (3, 13563), (17, 4625), (31, 3084)] },
    { n := 18979, F := 18978, R := 1, a := 2, factors := [2, 3, 3163], residues := [(2, 9489), (3, 12452), (3163, 17774)] },
    { n := 19001, F := 19000, R := 1, a := 3, factors := [2, 2, 2, 5, 5, 5, 19], residues := [(2, 9500), (5, 5749), (19, 16612)] },
    { n := 19009, F := 19008, R := 1, a := 23, factors := [2, 2, 2, 2, 2, 2, 3, 3, 3, 11], residues := [(2, 9504), (3, 5794), (11, 17520)] },
    { n := 19013, F := 19012, R := 1, a := 2, factors := [2, 2, 7, 7, 97], residues := [(2, 9506), (7, 1724), (97, 1428)] },
    { n := 19031, F := 19030, R := 1, a := 11, factors := [2, 5, 11, 173], residues := [(2, 9515), (5, 9800), (11, 6465), (173, 14062)] },
    { n := 19037, F := 19036, R := 1, a := 2, factors := [2, 2, 4759], residues := [(2, 9518), (4759, 8884)] },
    { n := 19051, F := 19050, R := 1, a := 2, factors := [2, 3, 5, 5, 127], residues := [(2, 9525), (3, 18052), (5, 7686), (127, 5299)] },
    { n := 19069, F := 19068, R := 1, a := 2, factors := [2, 2, 3, 7, 227], residues := [(2, 9534), (3, 7307), (7, 16617), (227, 12176)] },
    { n := 19073, F := 19072, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 149], residues := [(2, 9536), (149, 1510)] },
    { n := 19079, F := 19078, R := 1, a := 7, factors := [2, 9539], residues := [(2, 9539), (9539, 9937)] },
    { n := 19081, F := 19080, R := 1, a := 17, factors := [2, 2, 2, 3, 3, 5, 53], residues := [(2, 9540), (3, 4717), (5, 3487), (53, 1196)] },
    { n := 19087, F := 19086, R := 1, a := 19, factors := [2, 3, 3181], residues := [(2, 9543), (3, 5065), (3181, 7197)] },
    { n := 19121, F := 19120, R := 1, a := 6, factors := [2, 2, 2, 2, 5, 239], residues := [(2, 9560), (5, 8245), (239, 133)] },
    { n := 19139, F := 19138, R := 1, a := 2, factors := [2, 7, 1367], residues := [(2, 9569), (7, 9771), (1367, 9632)] },
    { n := 19141, F := 19140, R := 1, a := 2, factors := [2, 2, 3, 5, 11, 29], residues := [(2, 9570), (3, 9426), (5, 14590), (11, 5765), (29, 14172)] },
    { n := 19157, F := 19156, R := 1, a := 2, factors := [2, 2, 4789], residues := [(2, 9578), (4789, 8940)] },
    { n := 19163, F := 19162, R := 1, a := 2, factors := [2, 11, 13, 67], residues := [(2, 9581), (11, 7900), (13, 18356), (67, 16250)] },
    { n := 19181, F := 19180, R := 1, a := 2, factors := [2, 2, 5, 7, 137], residues := [(2, 9590), (5, 7499), (7, 5024), (137, 1837)] },
    { n := 19183, F := 19182, R := 1, a := 3, factors := [2, 3, 23, 139], residues := [(2, 9591), (3, 12742), (23, 12216), (139, 7845)] },
    { n := 19207, F := 19206, R := 1, a := 5, factors := [2, 3, 3, 11, 97], residues := [(2, 9603), (3, 15276), (11, 10698), (97, 13005)] },
    { n := 19211, F := 19210, R := 1, a := 6, factors := [2, 5, 17, 113], residues := [(2, 9605), (5, 11344), (17, 7973), (113, 14290)] },
    { n := 19213, F := 19212, R := 1, a := 5, factors := [2, 2, 3, 1601], residues := [(2, 9606), (3, 3407), (1601, 14433)] },
    { n := 19219, F := 19218, R := 1, a := 2, factors := [2, 3, 3203], residues := [(2, 9609), (3, 10060), (3203, 14338)] },
    { n := 19231, F := 19230, R := 1, a := 6, factors := [2, 3, 5, 641], residues := [(2, 9615), (3, 15942), (5, 12003), (641, 16463)] },
    { n := 19237, F := 19236, R := 1, a := 2, factors := [2, 2, 3, 7, 229], residues := [(2, 9618), (3, 12521), (7, 12332), (229, 12275)] },
    { n := 19249, F := 19248, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 401], residues := [(2, 9624), (3, 4130), (401, 15997)] },
    { n := 19259, F := 19258, R := 1, a := 2, factors := [2, 9629], residues := [(2, 9629), (9629, 6420)] },
    { n := 19267, F := 19266, R := 1, a := 3, factors := [2, 3, 13, 13, 19], residues := [(2, 9633), (3, 10461), (13, 17731), (19, 2619)] },
    { n := 19273, F := 19272, R := 1, a := 5, factors := [2, 2, 2, 3, 11, 73], residues := [(2, 9636), (3, 13428), (11, 17576), (73, 4256)] },
    { n := 19289, F := 19288, R := 1, a := 3, factors := [2, 2, 2, 2411], residues := [(2, 9644), (2411, 444)] },
    { n := 19301, F := 19300, R := 1, a := 2, factors := [2, 2, 5, 5, 193], residues := [(2, 9650), (5, 3175), (193, 17220)] },
    { n := 19309, F := 19308, R := 1, a := 6, factors := [2, 2, 3, 1609], residues := [(2, 9654), (3, 9410), (1609, 13020)] },
    { n := 19319, F := 19318, R := 1, a := 11, factors := [2, 13, 743], residues := [(2, 9659), (13, 10676), (743, 13989)] },
    { n := 19333, F := 19332, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 179], residues := [(2, 9666), (3, 1599), (179, 2472)] },
    { n := 19373, F := 19372, R := 1, a := 2, factors := [2, 2, 29, 167], residues := [(2, 9686), (29, 7830), (167, 6058)] },
    { n := 19379, F := 19378, R := 1, a := 2, factors := [2, 9689], residues := [(2, 9689), (9689, 6460)] },
    { n := 19381, F := 19380, R := 1, a := 7, factors := [2, 2, 3, 5, 17, 19], residues := [(2, 9690), (3, 10401), (5, 4122), (17, 12635), (19, 241)] },
    { n := 19387, F := 19386, R := 1, a := 2, factors := [2, 3, 3, 3, 359], residues := [(2, 9693), (3, 11875), (359, 16619)] },
    { n := 19391, F := 19390, R := 1, a := 11, factors := [2, 5, 7, 277], residues := [(2, 9695), (5, 9063), (7, 7024), (277, 4910)] },
    { n := 19403, F := 19402, R := 1, a := 2, factors := [2, 89, 109], residues := [(2, 9701), (89, 15694), (109, 17511)] },
    { n := 19417, F := 19416, R := 1, a := 5, factors := [2, 2, 2, 3, 809], residues := [(2, 9708), (3, 7956), (809, 11767)] },
    { n := 19421, F := 19420, R := 1, a := 3, factors := [2, 2, 5, 971], residues := [(2, 9710), (5, 1289), (971, 15803)] },
    { n := 19423, F := 19422, R := 1, a := 3, factors := [2, 3, 3, 13, 83], residues := [(2, 9711), (3, 9935), (13, 14481), (83, 4825)] },
    { n := 19427, F := 19426, R := 1, a := 2, factors := [2, 11, 883], residues := [(2, 9713), (11, 17632), (883, 15882)] },
    { n := 19429, F := 19428, R := 1, a := 6, factors := [2, 2, 3, 1619], residues := [(2, 9714), (3, 5940), (1619, 10863)] },
    { n := 19433, F := 19432, R := 1, a := 3, factors := [2, 2, 2, 7, 347], residues := [(2, 9716), (7, 7278), (347, 14224)] },
    { n := 19441, F := 19440, R := 1, a := 13, factors := [2, 2, 2, 2, 3, 3, 3, 3, 3, 5], residues := [(2, 9720), (3, 80), (5, 17601)] },
    { n := 19447, F := 19446, R := 1, a := 3, factors := [2, 3, 7, 463], residues := [(2, 9723), (3, 15541), (7, 17278), (463, 8375)] },
    { n := 19457, F := 19456, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 19], residues := [(2, 9728), (19, 13664)] },
    { n := 19463, F := 19462, R := 1, a := 5, factors := [2, 37, 263], residues := [(2, 9731), (37, 4166), (263, 17962)] },
    { n := 19469, F := 19468, R := 1, a := 2, factors := [2, 2, 31, 157], residues := [(2, 9734), (31, 2491), (157, 5531)] },
    { n := 19471, F := 19470, R := 1, a := 11, factors := [2, 3, 5, 11, 59], residues := [(2, 9735), (3, 15923), (5, 7971), (11, 18792), (59, 6675)] },
    { n := 19477, F := 19476, R := 1, a := 6, factors := [2, 2, 3, 3, 541], residues := [(2, 9738), (3, 14191), (541, 3042)] },
    { n := 19483, F := 19482, R := 1, a := 2, factors := [2, 3, 17, 191], residues := [(2, 9741), (3, 1492), (17, 2681), (191, 2865)] },
    { n := 19489, F := 19488, R := 1, a := 19, factors := [2, 2, 2, 2, 2, 3, 7, 29], residues := [(2, 9744), (3, 14332), (7, 4155), (29, 19205)] },
    { n := 19501, F := 19500, R := 1, a := 2, factors := [2, 2, 3, 5, 5, 5, 13], residues := [(2, 9750), (3, 6332), (5, 9316), (13, 380)] },
    { n := 19507, F := 19506, R := 1, a := 2, factors := [2, 3, 3251], residues := [(2, 9753), (3, 14280), (3251, 3406)] },
    { n := 19531, F := 19530, R := 1, a := 13, factors := [2, 3, 3, 5, 7, 31], residues := [(2, 9765), (3, 5135), (5, 6120), (7, 9922), (31, 95)] },
    { n := 19541, F := 19540, R := 1, a := 2, factors := [2, 2, 5, 977], residues := [(2, 9770), (5, 4114), (977, 12421)] },
    { n := 19543, F := 19542, R := 1, a := 3, factors := [2, 3, 3257], residues := [(2, 9771), (3, 2406), (3257, 10550)] },
    { n := 19553, F := 19552, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 13, 47], residues := [(2, 9776), (13, 17889), (47, 15229)] },
    { n := 19559, F := 19558, R := 1, a := 13, factors := [2, 7, 11, 127], residues := [(2, 9779), (7, 14646), (11, 3435), (127, 9643)] },
    { n := 19571, F := 19570, R := 1, a := 2, factors := [2, 5, 19, 103], residues := [(2, 9785), (5, 15059), (19, 7401), (103, 359)] },
    { n := 19577, F := 19576, R := 1, a := 3, factors := [2, 2, 2, 2447], residues := [(2, 9788), (2447, 5512)] },
    { n := 19583, F := 19582, R := 1, a := 5, factors := [2, 9791], residues := [(2, 9791), (9791, 816)] },
    { n := 19597, F := 19596, R := 1, a := 2, factors := [2, 2, 3, 23, 71], residues := [(2, 9798), (3, 14890), (23, 8114), (71, 16613)] },
    { n := 19603, F := 19602, R := 1, a := 2, factors := [2, 3, 3, 3, 3, 11, 11], residues := [(2, 9801), (3, 16312), (11, 5002)] },
    { n := 19609, F := 19608, R := 1, a := 13, factors := [2, 2, 2, 3, 19, 43], residues := [(2, 9804), (3, 291), (19, 3907), (43, 11242)] },
    { n := 19661, F := 19660, R := 1, a := 2, factors := [2, 2, 5, 983], residues := [(2, 9830), (5, 7394), (983, 12920)] },
    { n := 19681, F := 19680, R := 1, a := 11, factors := [2, 2, 2, 2, 2, 3, 5, 41], residues := [(2, 9840), (3, 15239), (5, 16439), (41, 10965)] },
    { n := 19687, F := 19686, R := 1, a := 5, factors := [2, 3, 17, 193], residues := [(2, 9843), (3, 4901), (17, 6914), (193, 11946)] },
    { n := 19697, F := 19696, R := 1, a := 3, factors := [2, 2, 2, 2, 1231], residues := [(2, 9848), (1231, 2844)] },
    { n := 19699, F := 19698, R := 1, a := 7, factors := [2, 3, 7, 7, 67], residues := [(2, 9849), (3, 2472), (7, 5376), (67, 15503)] },
    { n := 19709, F := 19708, R := 1, a := 2, factors := [2, 2, 13, 379], residues := [(2, 9854), (13, 15451), (379, 11285)] },
    { n := 19717, F := 19716, R := 1, a := 2, factors := [2, 2, 3, 31, 53], residues := [(2, 9858), (3, 17567), (31, 1846), (53, 4123)] },
    { n := 19727, F := 19726, R := 1, a := 5, factors := [2, 7, 1409], residues := [(2, 9863), (7, 1401), (1409, 2760)] },
    { n := 19739, F := 19738, R := 1, a := 2, factors := [2, 71, 139], residues := [(2, 9869), (71, 12852), (139, 15472)] },
    { n := 19751, F := 19750, R := 1, a := 7, factors := [2, 5, 5, 5, 79], residues := [(2, 9875), (5, 18719), (79, 14019)] },
    { n := 19753, F := 19752, R := 1, a := 5, factors := [2, 2, 2, 3, 823], residues := [(2, 9876), (3, 17834), (823, 11041)] },
    { n := 19759, F := 19758, R := 1, a := 3, factors := [2, 3, 37, 89], residues := [(2, 9879), (3, 10547), (37, 11806), (89, 14760)] },
    { n := 19763, F := 19762, R := 1, a := 2, factors := [2, 41, 241], residues := [(2, 9881), (41, 19445), (241, 8419)] },
    { n := 19777, F := 19776, R := 1, a := 11, factors := [2, 2, 2, 2, 2, 2, 3, 103], residues := [(2, 9888), (3, 4715), (103, 3596)] },
    { n := 19793, F := 19792, R := 1, a := 3, factors := [2, 2, 2, 2, 1237], residues := [(2, 9896), (1237, 6751)] },
    { n := 19801, F := 19800, R := 1, a := 13, factors := [2, 2, 2, 3, 3, 5, 5, 11], residues := [(2, 9900), (3, 12472), (5, 7024), (11, 648)] },
    { n := 19813, F := 19812, R := 1, a := 2, factors := [2, 2, 3, 13, 127], residues := [(2, 9906), (3, 17309), (13, 10292), (127, 6510)] },
    { n := 19819, F := 19818, R := 1, a := 3, factors := [2, 3, 3, 3, 367], residues := [(2, 9909), (3, 2987), (367, 16472)] },
    { n := 19841, F := 19840, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 5, 31], residues := [(2, 9920), (5, 7627), (31, 4029)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData21_valid : PocklingtonRow.Valid lowPocklingtonData21 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime21 (i : Fin lowPocklingtonData21.length) :
    Nat.Prime (lowPocklingtonData21.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData21_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 18959) (q := 18973) (by
      have hp := lowPocklingtonPrime21 ⟨0, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 18973) (q := 18979) (by
      have hp := lowPocklingtonPrime21 ⟨1, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 18979) (q := 19001) (by
      have hp := lowPocklingtonPrime21 ⟨2, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19001) (q := 19009) (by
      have hp := lowPocklingtonPrime21 ⟨3, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19009) (q := 19013) (by
      have hp := lowPocklingtonPrime21 ⟨4, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19013) (q := 19031) (by
      have hp := lowPocklingtonPrime21 ⟨5, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19031) (q := 19037) (by
      have hp := lowPocklingtonPrime21 ⟨6, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19037) (q := 19051) (by
      have hp := lowPocklingtonPrime21 ⟨7, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part01_chain :
    DusartPrimeRowsChain 18959 19050 dusartPrimeRows_18959_19936_part01 := by
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
def dusartPrimeRows_18959_19936_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19051) (q := 19069) (by
      have hp := lowPocklingtonPrime21 ⟨8, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19069) (q := 19073) (by
      have hp := lowPocklingtonPrime21 ⟨9, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19073) (q := 19079) (by
      have hp := lowPocklingtonPrime21 ⟨10, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19079) (q := 19081) (by
      have hp := lowPocklingtonPrime21 ⟨11, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19081) (q := 19087) (by
      have hp := lowPocklingtonPrime21 ⟨12, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19087) (q := 19121) (by
      have hp := lowPocklingtonPrime21 ⟨13, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19121) (q := 19139) (by
      have hp := lowPocklingtonPrime21 ⟨14, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19139) (q := 19141) (by
      have hp := lowPocklingtonPrime21 ⟨15, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part02_chain :
    DusartPrimeRowsChain 19051 19140 dusartPrimeRows_18959_19936_part02 := by
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
def dusartPrimeRows_18959_19936_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19141) (q := 19157) (by
      have hp := lowPocklingtonPrime21 ⟨16, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19157) (q := 19163) (by
      have hp := lowPocklingtonPrime21 ⟨17, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19163) (q := 19181) (by
      have hp := lowPocklingtonPrime21 ⟨18, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19181) (q := 19183) (by
      have hp := lowPocklingtonPrime21 ⟨19, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19183) (q := 19207) (by
      have hp := lowPocklingtonPrime21 ⟨20, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19207) (q := 19211) (by
      have hp := lowPocklingtonPrime21 ⟨21, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19211) (q := 19213) (by
      have hp := lowPocklingtonPrime21 ⟨22, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19213) (q := 19219) (by
      have hp := lowPocklingtonPrime21 ⟨23, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part03_chain :
    DusartPrimeRowsChain 19141 19218 dusartPrimeRows_18959_19936_part03 := by
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
def dusartPrimeRows_18959_19936_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19219) (q := 19231) (by
      have hp := lowPocklingtonPrime21 ⟨24, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19231) (q := 19237) (by
      have hp := lowPocklingtonPrime21 ⟨25, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19237) (q := 19249) (by
      have hp := lowPocklingtonPrime21 ⟨26, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19249) (q := 19259) (by
      have hp := lowPocklingtonPrime21 ⟨27, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19259) (q := 19267) (by
      have hp := lowPocklingtonPrime21 ⟨28, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19267) (q := 19273) (by
      have hp := lowPocklingtonPrime21 ⟨29, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19273) (q := 19289) (by
      have hp := lowPocklingtonPrime21 ⟨30, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19289) (q := 19301) (by
      have hp := lowPocklingtonPrime21 ⟨31, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part04_chain :
    DusartPrimeRowsChain 19219 19300 dusartPrimeRows_18959_19936_part04 := by
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
def dusartPrimeRows_18959_19936_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19301) (q := 19309) (by
      have hp := lowPocklingtonPrime21 ⟨32, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19309) (q := 19319) (by
      have hp := lowPocklingtonPrime21 ⟨33, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19319) (q := 19333) (by
      have hp := lowPocklingtonPrime21 ⟨34, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19333) (q := 19373) (by
      have hp := lowPocklingtonPrime21 ⟨35, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19373) (q := 19379) (by
      have hp := lowPocklingtonPrime21 ⟨36, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19379) (q := 19381) (by
      have hp := lowPocklingtonPrime21 ⟨37, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19381) (q := 19387) (by
      have hp := lowPocklingtonPrime21 ⟨38, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19387) (q := 19391) (by
      have hp := lowPocklingtonPrime21 ⟨39, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part05_chain :
    DusartPrimeRowsChain 19301 19390 dusartPrimeRows_18959_19936_part05 := by
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
def dusartPrimeRows_18959_19936_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19391) (q := 19403) (by
      have hp := lowPocklingtonPrime21 ⟨40, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19403) (q := 19417) (by
      have hp := lowPocklingtonPrime21 ⟨41, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19417) (q := 19421) (by
      have hp := lowPocklingtonPrime21 ⟨42, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19421) (q := 19423) (by
      have hp := lowPocklingtonPrime21 ⟨43, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19423) (q := 19427) (by
      have hp := lowPocklingtonPrime21 ⟨44, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19427) (q := 19429) (by
      have hp := lowPocklingtonPrime21 ⟨45, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19429) (q := 19433) (by
      have hp := lowPocklingtonPrime21 ⟨46, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19433) (q := 19441) (by
      have hp := lowPocklingtonPrime21 ⟨47, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part06_chain :
    DusartPrimeRowsChain 19391 19440 dusartPrimeRows_18959_19936_part06 := by
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
def dusartPrimeRows_18959_19936_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19441) (q := 19447) (by
      have hp := lowPocklingtonPrime21 ⟨48, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19447) (q := 19457) (by
      have hp := lowPocklingtonPrime21 ⟨49, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19457) (q := 19463) (by
      have hp := lowPocklingtonPrime21 ⟨50, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19463) (q := 19469) (by
      have hp := lowPocklingtonPrime21 ⟨51, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19469) (q := 19471) (by
      have hp := lowPocklingtonPrime21 ⟨52, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19471) (q := 19477) (by
      have hp := lowPocklingtonPrime21 ⟨53, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19477) (q := 19483) (by
      have hp := lowPocklingtonPrime21 ⟨54, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19483) (q := 19489) (by
      have hp := lowPocklingtonPrime21 ⟨55, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part07_chain :
    DusartPrimeRowsChain 19441 19488 dusartPrimeRows_18959_19936_part07 := by
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
def dusartPrimeRows_18959_19936_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19489) (q := 19501) (by
      have hp := lowPocklingtonPrime21 ⟨56, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19501) (q := 19507) (by
      have hp := lowPocklingtonPrime21 ⟨57, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19507) (q := 19531) (by
      have hp := lowPocklingtonPrime21 ⟨58, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19531) (q := 19541) (by
      have hp := lowPocklingtonPrime21 ⟨59, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19541) (q := 19543) (by
      have hp := lowPocklingtonPrime21 ⟨60, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19543) (q := 19553) (by
      have hp := lowPocklingtonPrime21 ⟨61, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19553) (q := 19559) (by
      have hp := lowPocklingtonPrime21 ⟨62, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19559) (q := 19571) (by
      have hp := lowPocklingtonPrime21 ⟨63, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part08_chain :
    DusartPrimeRowsChain 19489 19570 dusartPrimeRows_18959_19936_part08 := by
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
def dusartPrimeRows_18959_19936_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19571) (q := 19577) (by
      have hp := lowPocklingtonPrime21 ⟨64, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19577) (q := 19583) (by
      have hp := lowPocklingtonPrime21 ⟨65, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19583) (q := 19597) (by
      have hp := lowPocklingtonPrime21 ⟨66, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19597) (q := 19603) (by
      have hp := lowPocklingtonPrime21 ⟨67, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19603) (q := 19609) (by
      have hp := lowPocklingtonPrime21 ⟨68, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19609) (q := 19661) (by
      have hp := lowPocklingtonPrime21 ⟨69, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19661) (q := 19681) (by
      have hp := lowPocklingtonPrime21 ⟨70, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19681) (q := 19687) (by
      have hp := lowPocklingtonPrime21 ⟨71, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part09_chain :
    DusartPrimeRowsChain 19571 19686 dusartPrimeRows_18959_19936_part09 := by
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
def dusartPrimeRows_18959_19936_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19687) (q := 19697) (by
      have hp := lowPocklingtonPrime21 ⟨72, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19697) (q := 19699) (by
      have hp := lowPocklingtonPrime21 ⟨73, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19699) (q := 19709) (by
      have hp := lowPocklingtonPrime21 ⟨74, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19709) (q := 19717) (by
      have hp := lowPocklingtonPrime21 ⟨75, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19717) (q := 19727) (by
      have hp := lowPocklingtonPrime21 ⟨76, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19727) (q := 19739) (by
      have hp := lowPocklingtonPrime21 ⟨77, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19739) (q := 19751) (by
      have hp := lowPocklingtonPrime21 ⟨78, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19751) (q := 19753) (by
      have hp := lowPocklingtonPrime21 ⟨79, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part10_chain :
    DusartPrimeRowsChain 19687 19752 dusartPrimeRows_18959_19936_part10 := by
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
def dusartPrimeRows_18959_19936_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19753) (q := 19759) (by
      have hp := lowPocklingtonPrime21 ⟨80, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19759) (q := 19763) (by
      have hp := lowPocklingtonPrime21 ⟨81, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19763) (q := 19777) (by
      have hp := lowPocklingtonPrime21 ⟨82, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19777) (q := 19793) (by
      have hp := lowPocklingtonPrime21 ⟨83, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19793) (q := 19801) (by
      have hp := lowPocklingtonPrime21 ⟨84, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19801) (q := 19813) (by
      have hp := lowPocklingtonPrime21 ⟨85, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19813) (q := 19819) (by
      have hp := lowPocklingtonPrime21 ⟨86, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19819) (q := 19841) (by
      have hp := lowPocklingtonPrime21 ⟨87, by simp [lowPocklingtonData21]⟩
      simpa [lowPocklingtonData21] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part11_chain :
    DusartPrimeRowsChain 19753 19840 dusartPrimeRows_18959_19936_part11 := by
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
