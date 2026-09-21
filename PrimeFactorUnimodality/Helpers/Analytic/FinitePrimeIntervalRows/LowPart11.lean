import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 11 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData11 : List PocklingtonData := [
    { n := 11519, F := 11518, R := 1, a := 7, factors := [2, 13, 443], residues := [(2, 5759), (13, 258), (443, 3125)] },
    { n := 11527, F := 11526, R := 1, a := 5, factors := [2, 3, 17, 113], residues := [(2, 5763), (3, 5845), (17, 7186), (113, 10095)] },
    { n := 11549, F := 11548, R := 1, a := 2, factors := [2, 2, 2887], residues := [(2, 5774), (2887, 770)] },
    { n := 11551, F := 11550, R := 1, a := 7, factors := [2, 3, 5, 5, 7, 11], residues := [(2, 5775), (3, 1326), (5, 268), (7, 5175), (11, 8688)] },
    { n := 11579, F := 11578, R := 1, a := 2, factors := [2, 7, 827], residues := [(2, 5789), (7, 8101), (827, 2297)] },
    { n := 11587, F := 11586, R := 1, a := 2, factors := [2, 3, 1931], residues := [(2, 5793), (3, 4113), (1931, 6989)] },
    { n := 11593, F := 11592, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 7, 23], residues := [(2, 5796), (3, 4421), (7, 2865), (23, 2459)] },
    { n := 11597, F := 11596, R := 1, a := 3, factors := [2, 2, 13, 223], residues := [(2, 5798), (13, 7395), (223, 5676)] },
    { n := 11617, F := 11616, R := 1, a := 10, factors := [2, 2, 2, 2, 2, 3, 11, 11], residues := [(2, 5808), (3, 864), (11, 844)] },
    { n := 11621, F := 11620, R := 1, a := 2, factors := [2, 2, 5, 7, 83], residues := [(2, 5810), (5, 10691), (7, 8718), (83, 4674)] },
    { n := 11633, F := 11632, R := 1, a := 3, factors := [2, 2, 2, 2, 727], residues := [(2, 5816), (727, 5396)] },
    { n := 11657, F := 11656, R := 1, a := 3, factors := [2, 2, 2, 31, 47], residues := [(2, 5828), (31, 10317), (47, 581)] },
    { n := 11677, F := 11676, R := 1, a := 2, factors := [2, 2, 3, 7, 139], residues := [(2, 5838), (3, 719), (7, 1374), (139, 2345)] },
    { n := 11681, F := 11680, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 5, 73], residues := [(2, 5840), (5, 964), (73, 2303)] },
    { n := 11689, F := 11688, R := 1, a := 7, factors := [2, 2, 2, 3, 487], residues := [(2, 5844), (3, 633), (487, 4027)] },
    { n := 11699, F := 11698, R := 1, a := 2, factors := [2, 5849], residues := [(2, 5849), (5849, 3900)] },
    { n := 11701, F := 11700, R := 1, a := 6, factors := [2, 2, 3, 3, 5, 5, 13], residues := [(2, 5850), (3, 10348), (5, 3104), (13, 6040)] },
    { n := 11717, F := 11716, R := 1, a := 2, factors := [2, 2, 29, 101], residues := [(2, 5858), (29, 4268), (101, 1290)] },
    { n := 11719, F := 11718, R := 1, a := 6, factors := [2, 3, 3, 3, 7, 31], residues := [(2, 5859), (3, 11656), (7, 8211), (31, 3272)] },
    { n := 11731, F := 11730, R := 1, a := 3, factors := [2, 3, 5, 17, 23], residues := [(2, 5865), (3, 6694), (5, 997), (17, 2554), (23, 7388)] },
    { n := 11743, F := 11742, R := 1, a := 3, factors := [2, 3, 19, 103], residues := [(2, 5871), (3, 10690), (19, 2940), (103, 7133)] },
    { n := 11777, F := 11776, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 2, 2, 23], residues := [(2, 5888), (23, 6100)] },
    { n := 11779, F := 11778, R := 1, a := 2, factors := [2, 3, 13, 151], residues := [(2, 5889), (3, 9173), (13, 4971), (151, 10790)] },
    { n := 11783, F := 11782, R := 1, a := 5, factors := [2, 43, 137], residues := [(2, 5891), (43, 11540), (137, 10809)] },
    { n := 11789, F := 11788, R := 1, a := 2, factors := [2, 2, 7, 421], residues := [(2, 5894), (7, 1837), (421, 9274)] },
    { n := 11801, F := 11800, R := 1, a := 3, factors := [2, 2, 2, 5, 5, 59], residues := [(2, 5900), (5, 51), (59, 3077)] },
    { n := 11807, F := 11806, R := 1, a := 5, factors := [2, 5903], residues := [(2, 5903), (5903, 492)] },
    { n := 11813, F := 11812, R := 1, a := 2, factors := [2, 2, 2953], residues := [(2, 5906), (2953, 10238)] },
    { n := 11821, F := 11820, R := 1, a := 2, factors := [2, 2, 3, 5, 197], residues := [(2, 5910), (3, 11471), (5, 1566), (197, 2941)] },
    { n := 11827, F := 11826, R := 1, a := 2, factors := [2, 3, 3, 3, 3, 73], residues := [(2, 5913), (3, 9131), (73, 3225)] },
    { n := 11831, F := 11830, R := 1, a := 7, factors := [2, 5, 7, 13, 13], residues := [(2, 5915), (5, 3558), (7, 3933), (13, 3417)] },
    { n := 11833, F := 11832, R := 1, a := 5, factors := [2, 2, 2, 3, 17, 29], residues := [(2, 5916), (3, 872), (17, 11138), (29, 11064)] },
    { n := 11839, F := 11838, R := 1, a := 3, factors := [2, 3, 1973], residues := [(2, 5919), (3, 11612), (1973, 7562)] },
    { n := 11863, F := 11862, R := 1, a := 3, factors := [2, 3, 3, 659], residues := [(2, 5931), (3, 5029), (659, 3413)] },
    { n := 11867, F := 11866, R := 1, a := 2, factors := [2, 17, 349], residues := [(2, 5933), (17, 9315), (349, 10568)] },
    { n := 11887, F := 11886, R := 1, a := 3, factors := [2, 3, 7, 283], residues := [(2, 5943), (3, 5473), (7, 5365), (283, 8152)] },
    { n := 11897, F := 11896, R := 1, a := 3, factors := [2, 2, 2, 1487], residues := [(2, 5948), (1487, 3930)] },
    { n := 11903, F := 11902, R := 1, a := 5, factors := [2, 11, 541], residues := [(2, 5951), (11, 5835), (541, 9109)] },
    { n := 11909, F := 11908, R := 1, a := 2, factors := [2, 2, 13, 229], residues := [(2, 5954), (13, 7002), (229, 7695)] },
    { n := 11923, F := 11922, R := 1, a := 5, factors := [2, 3, 1987], residues := [(2, 5961), (3, 10440), (1987, 3795)] },
    { n := 11927, F := 11926, R := 1, a := 5, factors := [2, 67, 89], residues := [(2, 5963), (67, 5850), (89, 10316)] },
    { n := 11933, F := 11932, R := 1, a := 2, factors := [2, 2, 19, 157], residues := [(2, 5966), (19, 10542), (157, 3072)] },
    { n := 11939, F := 11938, R := 1, a := 2, factors := [2, 47, 127], residues := [(2, 5969), (47, 6685), (127, 440)] },
    { n := 11941, F := 11940, R := 1, a := 10, factors := [2, 2, 3, 5, 199], residues := [(2, 5970), (3, 9024), (5, 5174), (199, 9848)] },
    { n := 11953, F := 11952, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 3, 83], residues := [(2, 5976), (3, 9006), (83, 4077)] },
    { n := 11959, F := 11958, R := 1, a := 3, factors := [2, 3, 1993], residues := [(2, 5979), (3, 7717), (1993, 10267)] },
    { n := 11969, F := 11968, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 11, 17], residues := [(2, 5984), (11, 4751), (17, 8177)] },
    { n := 11971, F := 11970, R := 1, a := 10, factors := [2, 3, 3, 5, 7, 19], residues := [(2, 5985), (3, 9722), (5, 10508), (7, 3312), (19, 5504)] },
    { n := 11981, F := 11980, R := 1, a := 2, factors := [2, 2, 5, 599], residues := [(2, 5990), (5, 2157), (599, 5877)] },
    { n := 11987, F := 11986, R := 1, a := 2, factors := [2, 13, 461], residues := [(2, 5993), (13, 3607), (461, 9482)] },
    { n := 12007, F := 12006, R := 1, a := 13, factors := [2, 3, 3, 23, 29], residues := [(2, 6003), (3, 11403), (23, 9904), (29, 11898)] },
    { n := 12011, F := 12010, R := 1, a := 2, factors := [2, 5, 1201], residues := [(2, 6005), (5, 1640), (1201, 1949)] },
    { n := 12037, F := 12036, R := 1, a := 5, factors := [2, 2, 3, 17, 59], residues := [(2, 6018), (3, 4443), (17, 3487), (59, 7037)] },
    { n := 12041, F := 12040, R := 1, a := 3, factors := [2, 2, 2, 5, 7, 43], residues := [(2, 6020), (5, 1005), (7, 1759), (43, 7076)] },
    { n := 12043, F := 12042, R := 1, a := 2, factors := [2, 3, 3, 3, 223], residues := [(2, 6021), (3, 1054), (223, 230)] },
    { n := 12049, F := 12048, R := 1, a := 13, factors := [2, 2, 2, 2, 3, 251], residues := [(2, 6024), (3, 11820), (251, 11284)] },
    { n := 12071, F := 12070, R := 1, a := 11, factors := [2, 5, 17, 71], residues := [(2, 6035), (5, 11856), (17, 3067), (71, 6470)] },
    { n := 12073, F := 12072, R := 1, a := 7, factors := [2, 2, 2, 3, 503], residues := [(2, 6036), (3, 8805), (503, 11308)] },
    { n := 12097, F := 12096, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 3, 3, 3, 7], residues := [(2, 6048), (3, 12033), (7, 7462)] },
    { n := 12101, F := 12100, R := 1, a := 3, factors := [2, 2, 5, 5, 11, 11], residues := [(2, 6050), (5, 2814), (11, 8398)] },
    { n := 12107, F := 12106, R := 1, a := 2, factors := [2, 6053], residues := [(2, 6053), (6053, 4036)] },
    { n := 12109, F := 12108, R := 1, a := 6, factors := [2, 2, 3, 1009], residues := [(2, 6054), (3, 6928), (1009, 2073)] },
    { n := 12113, F := 12112, R := 1, a := 3, factors := [2, 2, 2, 2, 757], residues := [(2, 6056), (757, 10705)] },
    { n := 12119, F := 12118, R := 1, a := 7, factors := [2, 73, 83], residues := [(2, 6059), (73, 8518), (83, 4857)] },
    { n := 12143, F := 12142, R := 1, a := 10, factors := [2, 13, 467], residues := [(2, 6071), (13, 6061), (467, 8659)] },
    { n := 12149, F := 12148, R := 1, a := 2, factors := [2, 2, 3037], residues := [(2, 6074), (3037, 810)] },
    { n := 12157, F := 12156, R := 1, a := 2, factors := [2, 2, 3, 1013], residues := [(2, 6078), (3, 2189), (1013, 95)] },
    { n := 12161, F := 12160, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 5, 19], residues := [(2, 6080), (5, 7780), (19, 3195)] },
    { n := 12163, F := 12162, R := 1, a := 5, factors := [2, 3, 2027], residues := [(2, 6081), (3, 1898), (2027, 6020)] },
    { n := 12197, F := 12196, R := 1, a := 2, factors := [2, 2, 3049], residues := [(2, 6098), (3049, 5692)] },
    { n := 12203, F := 12202, R := 1, a := 2, factors := [2, 6101], residues := [(2, 6101), (6101, 4068)] },
    { n := 12211, F := 12210, R := 1, a := 2, factors := [2, 3, 5, 11, 37], residues := [(2, 6105), (3, 8177), (5, 11902), (11, 5157), (37, 10572)] },
    { n := 12227, F := 12226, R := 1, a := 2, factors := [2, 6113], residues := [(2, 6113), (6113, 4076)] },
    { n := 12239, F := 12238, R := 1, a := 13, factors := [2, 29, 211], residues := [(2, 6119), (29, 11871), (211, 1115)] },
    { n := 12241, F := 12240, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 3, 5, 17], residues := [(2, 6120), (3, 3102), (5, 6232), (17, 10055)] },
    { n := 12251, F := 12250, R := 1, a := 2, factors := [2, 5, 5, 5, 7, 7], residues := [(2, 6125), (5, 864), (7, 343)] },
    { n := 12253, F := 12252, R := 1, a := 2, factors := [2, 2, 3, 1021], residues := [(2, 6126), (3, 3923), (1021, 383)] },
    { n := 12263, F := 12262, R := 1, a := 5, factors := [2, 6131], residues := [(2, 6131), (6131, 511)] },
    { n := 12269, F := 12268, R := 1, a := 2, factors := [2, 2, 3067], residues := [(2, 6134), (3067, 818)] },
    { n := 12277, F := 12276, R := 1, a := 2, factors := [2, 2, 3, 3, 11, 31], residues := [(2, 6138), (3, 4225), (11, 9211), (31, 11559)] },
    { n := 12281, F := 12280, R := 1, a := 3, factors := [2, 2, 2, 5, 307], residues := [(2, 6140), (5, 9872), (307, 11008)] },
    { n := 12289, F := 12288, R := 1, a := 11, factors := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], residues := [(2, 6144), (3, 6112)] },
    { n := 12301, F := 12300, R := 1, a := 2, factors := [2, 2, 3, 5, 5, 41], residues := [(2, 6150), (3, 4842), (5, 11127), (41, 4046)] },
    { n := 12323, F := 12322, R := 1, a := 2, factors := [2, 61, 101], residues := [(2, 6161), (61, 5544), (101, 7108)] },
    { n := 12329, F := 12328, R := 1, a := 3, factors := [2, 2, 2, 23, 67], residues := [(2, 6164), (23, 5546), (67, 4919)] },
    { n := 12343, F := 12342, R := 1, a := 7, factors := [2, 3, 11, 11, 17], residues := [(2, 6171), (3, 2973), (11, 329), (17, 10564)] },
    { n := 12347, F := 12346, R := 1, a := 2, factors := [2, 6173], residues := [(2, 6173), (6173, 4116)] },
    { n := 12373, F := 12372, R := 1, a := 2, factors := [2, 2, 3, 1031], residues := [(2, 6186), (3, 3625), (1031, 2109)] },
    { n := 12377, F := 12376, R := 1, a := 6, factors := [2, 2, 2, 7, 13, 17], residues := [(2, 6188), (7, 8825), (13, 6991), (17, 11353)] },
    { n := 12379, F := 12378, R := 1, a := 2, factors := [2, 3, 2063], residues := [(2, 6189), (3, 6329), (2063, 393)] },
    { n := 12391, F := 12390, R := 1, a := 26, factors := [2, 3, 5, 7, 59], residues := [(2, 6195), (3, 1409), (5, 953), (7, 956), (59, 8506)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData11_valid : PocklingtonRow.Valid lowPocklingtonData11 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime11 (i : Fin lowPocklingtonData11.length) :
    Nat.Prime (lowPocklingtonData11.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData11_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11503) (q := 11519) (by
      have hp := lowPocklingtonPrime11 ⟨0, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11519) (q := 11527) (by
      have hp := lowPocklingtonPrime11 ⟨1, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11527) (q := 11549) (by
      have hp := lowPocklingtonPrime11 ⟨2, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11549) (q := 11551) (by
      have hp := lowPocklingtonPrime11 ⟨3, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11551) (q := 11579) (by
      have hp := lowPocklingtonPrime11 ⟨4, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11579) (q := 11587) (by
      have hp := lowPocklingtonPrime11 ⟨5, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11587) (q := 11593) (by
      have hp := lowPocklingtonPrime11 ⟨6, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11593) (q := 11597) (by
      have hp := lowPocklingtonPrime11 ⟨7, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part01_chain :
    DusartPrimeRowsChain 11503 11596 dusartPrimeRows_11503_12096_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12088, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11597) (q := 11617) (by
      have hp := lowPocklingtonPrime11 ⟨8, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11617) (q := 11621) (by
      have hp := lowPocklingtonPrime11 ⟨9, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11621) (q := 11633) (by
      have hp := lowPocklingtonPrime11 ⟨10, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11633) (q := 11657) (by
      have hp := lowPocklingtonPrime11 ⟨11, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11657) (q := 11677) (by
      have hp := lowPocklingtonPrime11 ⟨12, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11677) (q := 11681) (by
      have hp := lowPocklingtonPrime11 ⟨13, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11681) (q := 11689) (by
      have hp := lowPocklingtonPrime11 ⟨14, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11689) (q := 11699) (by
      have hp := lowPocklingtonPrime11 ⟨15, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part02_chain :
    DusartPrimeRowsChain 11597 11698 dusartPrimeRows_11503_12096_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12088, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11699) (q := 11701) (by
      have hp := lowPocklingtonPrime11 ⟨16, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11701) (q := 11717) (by
      have hp := lowPocklingtonPrime11 ⟨17, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11717) (q := 11719) (by
      have hp := lowPocklingtonPrime11 ⟨18, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11719) (q := 11731) (by
      have hp := lowPocklingtonPrime11 ⟨19, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11731) (q := 11743) (by
      have hp := lowPocklingtonPrime11 ⟨20, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11743) (q := 11777) (by
      have hp := lowPocklingtonPrime11 ⟨21, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11777) (q := 11779) (by
      have hp := lowPocklingtonPrime11 ⟨22, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11779) (q := 11783) (by
      have hp := lowPocklingtonPrime11 ⟨23, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part03_chain :
    DusartPrimeRowsChain 11699 11782 dusartPrimeRows_11503_12096_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12088, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11783) (q := 11789) (by
      have hp := lowPocklingtonPrime11 ⟨24, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11789) (q := 11801) (by
      have hp := lowPocklingtonPrime11 ⟨25, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11801) (q := 11807) (by
      have hp := lowPocklingtonPrime11 ⟨26, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11807) (q := 11813) (by
      have hp := lowPocklingtonPrime11 ⟨27, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11813) (q := 11821) (by
      have hp := lowPocklingtonPrime11 ⟨28, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11821) (q := 11827) (by
      have hp := lowPocklingtonPrime11 ⟨29, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11827) (q := 11831) (by
      have hp := lowPocklingtonPrime11 ⟨30, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11831) (q := 11833) (by
      have hp := lowPocklingtonPrime11 ⟨31, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part04_chain :
    DusartPrimeRowsChain 11783 11832 dusartPrimeRows_11503_12096_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12088, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11833) (q := 11839) (by
      have hp := lowPocklingtonPrime11 ⟨32, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11839) (q := 11863) (by
      have hp := lowPocklingtonPrime11 ⟨33, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11863) (q := 11867) (by
      have hp := lowPocklingtonPrime11 ⟨34, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11867) (q := 11887) (by
      have hp := lowPocklingtonPrime11 ⟨35, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11887) (q := 11897) (by
      have hp := lowPocklingtonPrime11 ⟨36, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11897) (q := 11903) (by
      have hp := lowPocklingtonPrime11 ⟨37, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11903) (q := 11909) (by
      have hp := lowPocklingtonPrime11 ⟨38, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11909) (q := 11923) (by
      have hp := lowPocklingtonPrime11 ⟨39, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part05_chain :
    DusartPrimeRowsChain 11833 11922 dusartPrimeRows_11503_12096_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12088, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11923) (q := 11927) (by
      have hp := lowPocklingtonPrime11 ⟨40, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11927) (q := 11933) (by
      have hp := lowPocklingtonPrime11 ⟨41, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11933) (q := 11939) (by
      have hp := lowPocklingtonPrime11 ⟨42, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11939) (q := 11941) (by
      have hp := lowPocklingtonPrime11 ⟨43, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11941) (q := 11953) (by
      have hp := lowPocklingtonPrime11 ⟨44, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11953) (q := 11959) (by
      have hp := lowPocklingtonPrime11 ⟨45, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11959) (q := 11969) (by
      have hp := lowPocklingtonPrime11 ⟨46, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11969) (q := 11971) (by
      have hp := lowPocklingtonPrime11 ⟨47, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part06_chain :
    DusartPrimeRowsChain 11923 11970 dusartPrimeRows_11503_12096_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12088, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11971) (q := 11981) (by
      have hp := lowPocklingtonPrime11 ⟨48, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11981) (q := 11987) (by
      have hp := lowPocklingtonPrime11 ⟨49, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11987) (q := 12007) (by
      have hp := lowPocklingtonPrime11 ⟨50, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12007) (q := 12011) (by
      have hp := lowPocklingtonPrime11 ⟨51, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12011) (q := 12037) (by
      have hp := lowPocklingtonPrime11 ⟨52, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12037) (q := 12041) (by
      have hp := lowPocklingtonPrime11 ⟨53, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12041) (q := 12043) (by
      have hp := lowPocklingtonPrime11 ⟨54, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12043) (q := 12049) (by
      have hp := lowPocklingtonPrime11 ⟨55, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part07_chain :
    DusartPrimeRowsChain 11971 12048 dusartPrimeRows_11503_12096_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12088, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 12049) (q := 12071) (by
      have hp := lowPocklingtonPrime11 ⟨56, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12071) (q := 12073) (by
      have hp := lowPocklingtonPrime11 ⟨57, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12073) (q := 12097) (by
      have hp := lowPocklingtonPrime11 ⟨58, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part08_chain :
    DusartPrimeRowsChain 12049 12096 dusartPrimeRows_11503_12096_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.empty
        norm_num [dusartPrimeRow_of_explicit_12088, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12097) (q := 12101) (by
      have hp := lowPocklingtonPrime11 ⟨59, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12101) (q := 12107) (by
      have hp := lowPocklingtonPrime11 ⟨60, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12107) (q := 12109) (by
      have hp := lowPocklingtonPrime11 ⟨61, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12109) (q := 12113) (by
      have hp := lowPocklingtonPrime11 ⟨62, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12113) (q := 12119) (by
      have hp := lowPocklingtonPrime11 ⟨63, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12119) (q := 12143) (by
      have hp := lowPocklingtonPrime11 ⟨64, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12143) (q := 12149) (by
      have hp := lowPocklingtonPrime11 ⟨65, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12149) (q := 12157) (by
      have hp := lowPocklingtonPrime11 ⟨66, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part01_chain :
    DusartPrimeRowsChain 12097 12156 dusartPrimeRows_12097_12712_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12157) (q := 12161) (by
      have hp := lowPocklingtonPrime11 ⟨67, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12161) (q := 12163) (by
      have hp := lowPocklingtonPrime11 ⟨68, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12163) (q := 12197) (by
      have hp := lowPocklingtonPrime11 ⟨69, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12197) (q := 12203) (by
      have hp := lowPocklingtonPrime11 ⟨70, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12203) (q := 12211) (by
      have hp := lowPocklingtonPrime11 ⟨71, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12211) (q := 12227) (by
      have hp := lowPocklingtonPrime11 ⟨72, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12227) (q := 12239) (by
      have hp := lowPocklingtonPrime11 ⟨73, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12239) (q := 12241) (by
      have hp := lowPocklingtonPrime11 ⟨74, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part02_chain :
    DusartPrimeRowsChain 12157 12240 dusartPrimeRows_12097_12712_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12241) (q := 12251) (by
      have hp := lowPocklingtonPrime11 ⟨75, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12251) (q := 12253) (by
      have hp := lowPocklingtonPrime11 ⟨76, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12253) (q := 12263) (by
      have hp := lowPocklingtonPrime11 ⟨77, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12263) (q := 12269) (by
      have hp := lowPocklingtonPrime11 ⟨78, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12269) (q := 12277) (by
      have hp := lowPocklingtonPrime11 ⟨79, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12277) (q := 12281) (by
      have hp := lowPocklingtonPrime11 ⟨80, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12281) (q := 12289) (by
      have hp := lowPocklingtonPrime11 ⟨81, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12289) (q := 12301) (by
      have hp := lowPocklingtonPrime11 ⟨82, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part03_chain :
    DusartPrimeRowsChain 12241 12300 dusartPrimeRows_12097_12712_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12301) (q := 12323) (by
      have hp := lowPocklingtonPrime11 ⟨83, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12323) (q := 12329) (by
      have hp := lowPocklingtonPrime11 ⟨84, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12329) (q := 12343) (by
      have hp := lowPocklingtonPrime11 ⟨85, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12343) (q := 12347) (by
      have hp := lowPocklingtonPrime11 ⟨86, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12347) (q := 12373) (by
      have hp := lowPocklingtonPrime11 ⟨87, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12373) (q := 12377) (by
      have hp := lowPocklingtonPrime11 ⟨88, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12377) (q := 12379) (by
      have hp := lowPocklingtonPrime11 ⟨89, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12379) (q := 12391) (by
      have hp := lowPocklingtonPrime11 ⟨90, by simp [lowPocklingtonData11]⟩
      simpa [lowPocklingtonData11] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part04_chain :
    DusartPrimeRowsChain 12301 12390 dusartPrimeRows_12097_12712_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]
