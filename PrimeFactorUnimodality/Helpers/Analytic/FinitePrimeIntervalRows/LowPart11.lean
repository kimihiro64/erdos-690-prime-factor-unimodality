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

theorem lowPrime_11519 : Nat.Prime 11519 := by
  let d := lowPocklingtonData11.get ⟨0, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11527 : Nat.Prime 11527 := by
  let d := lowPocklingtonData11.get ⟨1, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11549 : Nat.Prime 11549 := by
  let d := lowPocklingtonData11.get ⟨2, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11551 : Nat.Prime 11551 := by
  let d := lowPocklingtonData11.get ⟨3, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11579 : Nat.Prime 11579 := by
  let d := lowPocklingtonData11.get ⟨4, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11587 : Nat.Prime 11587 := by
  let d := lowPocklingtonData11.get ⟨5, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11593 : Nat.Prime 11593 := by
  let d := lowPocklingtonData11.get ⟨6, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11597 : Nat.Prime 11597 := by
  let d := lowPocklingtonData11.get ⟨7, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11617 : Nat.Prime 11617 := by
  let d := lowPocklingtonData11.get ⟨8, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11621 : Nat.Prime 11621 := by
  let d := lowPocklingtonData11.get ⟨9, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11633 : Nat.Prime 11633 := by
  let d := lowPocklingtonData11.get ⟨10, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11657 : Nat.Prime 11657 := by
  let d := lowPocklingtonData11.get ⟨11, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11677 : Nat.Prime 11677 := by
  let d := lowPocklingtonData11.get ⟨12, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11681 : Nat.Prime 11681 := by
  let d := lowPocklingtonData11.get ⟨13, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11689 : Nat.Prime 11689 := by
  let d := lowPocklingtonData11.get ⟨14, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11699 : Nat.Prime 11699 := by
  let d := lowPocklingtonData11.get ⟨15, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11701 : Nat.Prime 11701 := by
  let d := lowPocklingtonData11.get ⟨16, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11717 : Nat.Prime 11717 := by
  let d := lowPocklingtonData11.get ⟨17, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11719 : Nat.Prime 11719 := by
  let d := lowPocklingtonData11.get ⟨18, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11731 : Nat.Prime 11731 := by
  let d := lowPocklingtonData11.get ⟨19, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11743 : Nat.Prime 11743 := by
  let d := lowPocklingtonData11.get ⟨20, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11777 : Nat.Prime 11777 := by
  let d := lowPocklingtonData11.get ⟨21, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11779 : Nat.Prime 11779 := by
  let d := lowPocklingtonData11.get ⟨22, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11783 : Nat.Prime 11783 := by
  let d := lowPocklingtonData11.get ⟨23, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11789 : Nat.Prime 11789 := by
  let d := lowPocklingtonData11.get ⟨24, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11801 : Nat.Prime 11801 := by
  let d := lowPocklingtonData11.get ⟨25, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11807 : Nat.Prime 11807 := by
  let d := lowPocklingtonData11.get ⟨26, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11813 : Nat.Prime 11813 := by
  let d := lowPocklingtonData11.get ⟨27, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11821 : Nat.Prime 11821 := by
  let d := lowPocklingtonData11.get ⟨28, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11827 : Nat.Prime 11827 := by
  let d := lowPocklingtonData11.get ⟨29, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11831 : Nat.Prime 11831 := by
  let d := lowPocklingtonData11.get ⟨30, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11833 : Nat.Prime 11833 := by
  let d := lowPocklingtonData11.get ⟨31, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11839 : Nat.Prime 11839 := by
  let d := lowPocklingtonData11.get ⟨32, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11863 : Nat.Prime 11863 := by
  let d := lowPocklingtonData11.get ⟨33, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11867 : Nat.Prime 11867 := by
  let d := lowPocklingtonData11.get ⟨34, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11887 : Nat.Prime 11887 := by
  let d := lowPocklingtonData11.get ⟨35, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11897 : Nat.Prime 11897 := by
  let d := lowPocklingtonData11.get ⟨36, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11903 : Nat.Prime 11903 := by
  let d := lowPocklingtonData11.get ⟨37, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11909 : Nat.Prime 11909 := by
  let d := lowPocklingtonData11.get ⟨38, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11923 : Nat.Prime 11923 := by
  let d := lowPocklingtonData11.get ⟨39, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11927 : Nat.Prime 11927 := by
  let d := lowPocklingtonData11.get ⟨40, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11933 : Nat.Prime 11933 := by
  let d := lowPocklingtonData11.get ⟨41, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11939 : Nat.Prime 11939 := by
  let d := lowPocklingtonData11.get ⟨42, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11941 : Nat.Prime 11941 := by
  let d := lowPocklingtonData11.get ⟨43, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11953 : Nat.Prime 11953 := by
  let d := lowPocklingtonData11.get ⟨44, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11959 : Nat.Prime 11959 := by
  let d := lowPocklingtonData11.get ⟨45, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11969 : Nat.Prime 11969 := by
  let d := lowPocklingtonData11.get ⟨46, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11971 : Nat.Prime 11971 := by
  let d := lowPocklingtonData11.get ⟨47, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11981 : Nat.Prime 11981 := by
  let d := lowPocklingtonData11.get ⟨48, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_11987 : Nat.Prime 11987 := by
  let d := lowPocklingtonData11.get ⟨49, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12007 : Nat.Prime 12007 := by
  let d := lowPocklingtonData11.get ⟨50, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12011 : Nat.Prime 12011 := by
  let d := lowPocklingtonData11.get ⟨51, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12037 : Nat.Prime 12037 := by
  let d := lowPocklingtonData11.get ⟨52, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12041 : Nat.Prime 12041 := by
  let d := lowPocklingtonData11.get ⟨53, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12043 : Nat.Prime 12043 := by
  let d := lowPocklingtonData11.get ⟨54, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12049 : Nat.Prime 12049 := by
  let d := lowPocklingtonData11.get ⟨55, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12071 : Nat.Prime 12071 := by
  let d := lowPocklingtonData11.get ⟨56, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12073 : Nat.Prime 12073 := by
  let d := lowPocklingtonData11.get ⟨57, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12097 : Nat.Prime 12097 := by
  let d := lowPocklingtonData11.get ⟨58, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12101 : Nat.Prime 12101 := by
  let d := lowPocklingtonData11.get ⟨59, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12107 : Nat.Prime 12107 := by
  let d := lowPocklingtonData11.get ⟨60, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12109 : Nat.Prime 12109 := by
  let d := lowPocklingtonData11.get ⟨61, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12113 : Nat.Prime 12113 := by
  let d := lowPocklingtonData11.get ⟨62, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12119 : Nat.Prime 12119 := by
  let d := lowPocklingtonData11.get ⟨63, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12143 : Nat.Prime 12143 := by
  let d := lowPocklingtonData11.get ⟨64, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12149 : Nat.Prime 12149 := by
  let d := lowPocklingtonData11.get ⟨65, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12157 : Nat.Prime 12157 := by
  let d := lowPocklingtonData11.get ⟨66, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12161 : Nat.Prime 12161 := by
  let d := lowPocklingtonData11.get ⟨67, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12163 : Nat.Prime 12163 := by
  let d := lowPocklingtonData11.get ⟨68, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12197 : Nat.Prime 12197 := by
  let d := lowPocklingtonData11.get ⟨69, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12203 : Nat.Prime 12203 := by
  let d := lowPocklingtonData11.get ⟨70, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12211 : Nat.Prime 12211 := by
  let d := lowPocklingtonData11.get ⟨71, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12227 : Nat.Prime 12227 := by
  let d := lowPocklingtonData11.get ⟨72, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12239 : Nat.Prime 12239 := by
  let d := lowPocklingtonData11.get ⟨73, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12241 : Nat.Prime 12241 := by
  let d := lowPocklingtonData11.get ⟨74, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12251 : Nat.Prime 12251 := by
  let d := lowPocklingtonData11.get ⟨75, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12253 : Nat.Prime 12253 := by
  let d := lowPocklingtonData11.get ⟨76, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12263 : Nat.Prime 12263 := by
  let d := lowPocklingtonData11.get ⟨77, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12269 : Nat.Prime 12269 := by
  let d := lowPocklingtonData11.get ⟨78, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12277 : Nat.Prime 12277 := by
  let d := lowPocklingtonData11.get ⟨79, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12281 : Nat.Prime 12281 := by
  let d := lowPocklingtonData11.get ⟨80, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12289 : Nat.Prime 12289 := by
  let d := lowPocklingtonData11.get ⟨81, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12301 : Nat.Prime 12301 := by
  let d := lowPocklingtonData11.get ⟨82, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12323 : Nat.Prime 12323 := by
  let d := lowPocklingtonData11.get ⟨83, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12329 : Nat.Prime 12329 := by
  let d := lowPocklingtonData11.get ⟨84, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12343 : Nat.Prime 12343 := by
  let d := lowPocklingtonData11.get ⟨85, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12347 : Nat.Prime 12347 := by
  let d := lowPocklingtonData11.get ⟨86, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12373 : Nat.Prime 12373 := by
  let d := lowPocklingtonData11.get ⟨87, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12377 : Nat.Prime 12377 := by
  let d := lowPocklingtonData11.get ⟨88, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12379 : Nat.Prime 12379 := by
  let d := lowPocklingtonData11.get ⟨89, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp

theorem lowPrime_12391 : Nat.Prime 12391 := by
  let d := lowPocklingtonData11.get ⟨90, by simp [lowPocklingtonData11]⟩
  have hd : d ∈ lowPocklingtonData11 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData11_valid hd
  simpa [d, lowPocklingtonData11] using hp
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11503) (q := 11519) (by exact lowPrime_11519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11519) (q := 11527) (by exact lowPrime_11527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11527) (q := 11549) (by exact lowPrime_11549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11549) (q := 11551) (by exact lowPrime_11551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11551) (q := 11579) (by exact lowPrime_11579) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11579) (q := 11587) (by exact lowPrime_11587) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11587) (q := 11593) (by exact lowPrime_11593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11593) (q := 11597) (by exact lowPrime_11597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_12088 (p := 11597) (q := 11617) (by exact lowPrime_11617) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11617) (q := 11621) (by exact lowPrime_11621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11621) (q := 11633) (by exact lowPrime_11633) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11633) (q := 11657) (by exact lowPrime_11657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11657) (q := 11677) (by exact lowPrime_11677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11677) (q := 11681) (by exact lowPrime_11681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11681) (q := 11689) (by exact lowPrime_11689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11689) (q := 11699) (by exact lowPrime_11699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_12088 (p := 11699) (q := 11701) (by exact lowPrime_11701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11701) (q := 11717) (by exact lowPrime_11717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11717) (q := 11719) (by exact lowPrime_11719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11719) (q := 11731) (by exact lowPrime_11731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11731) (q := 11743) (by exact lowPrime_11743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11743) (q := 11777) (by exact lowPrime_11777) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11777) (q := 11779) (by exact lowPrime_11779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11779) (q := 11783) (by exact lowPrime_11783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_12088 (p := 11783) (q := 11789) (by exact lowPrime_11789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11789) (q := 11801) (by exact lowPrime_11801) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11801) (q := 11807) (by exact lowPrime_11807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11807) (q := 11813) (by exact lowPrime_11813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11813) (q := 11821) (by exact lowPrime_11821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11821) (q := 11827) (by exact lowPrime_11827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11827) (q := 11831) (by exact lowPrime_11831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11831) (q := 11833) (by exact lowPrime_11833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_12088 (p := 11833) (q := 11839) (by exact lowPrime_11839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11839) (q := 11863) (by exact lowPrime_11863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11863) (q := 11867) (by exact lowPrime_11867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11867) (q := 11887) (by exact lowPrime_11887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11887) (q := 11897) (by exact lowPrime_11897) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11897) (q := 11903) (by exact lowPrime_11903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11903) (q := 11909) (by exact lowPrime_11909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11909) (q := 11923) (by exact lowPrime_11923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_12088 (p := 11923) (q := 11927) (by exact lowPrime_11927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11927) (q := 11933) (by exact lowPrime_11933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11933) (q := 11939) (by exact lowPrime_11939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11939) (q := 11941) (by exact lowPrime_11941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11941) (q := 11953) (by exact lowPrime_11953) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11953) (q := 11959) (by exact lowPrime_11959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11959) (q := 11969) (by exact lowPrime_11969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11969) (q := 11971) (by exact lowPrime_11971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_12088 (p := 11971) (q := 11981) (by exact lowPrime_11981) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11981) (q := 11987) (by exact lowPrime_11987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11987) (q := 12007) (by exact lowPrime_12007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12007) (q := 12011) (by exact lowPrime_12011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12011) (q := 12037) (by exact lowPrime_12037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12037) (q := 12041) (by exact lowPrime_12041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12041) (q := 12043) (by exact lowPrime_12043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12043) (q := 12049) (by exact lowPrime_12049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_12088 (p := 12049) (q := 12071) (by exact lowPrime_12071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12071) (q := 12073) (by exact lowPrime_12073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12073) (q := 12097) (by exact lowPrime_12097) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_12708 (p := 12097) (q := 12101) (by exact lowPrime_12101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12101) (q := 12107) (by exact lowPrime_12107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12107) (q := 12109) (by exact lowPrime_12109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12109) (q := 12113) (by exact lowPrime_12113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12113) (q := 12119) (by exact lowPrime_12119) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12119) (q := 12143) (by exact lowPrime_12143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12143) (q := 12149) (by exact lowPrime_12149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12149) (q := 12157) (by exact lowPrime_12157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_12708 (p := 12157) (q := 12161) (by exact lowPrime_12161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12161) (q := 12163) (by exact lowPrime_12163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12163) (q := 12197) (by exact lowPrime_12197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12197) (q := 12203) (by exact lowPrime_12203) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12203) (q := 12211) (by exact lowPrime_12211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12211) (q := 12227) (by exact lowPrime_12227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12227) (q := 12239) (by exact lowPrime_12239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12239) (q := 12241) (by exact lowPrime_12241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_12708 (p := 12241) (q := 12251) (by exact lowPrime_12251) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12251) (q := 12253) (by exact lowPrime_12253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12253) (q := 12263) (by exact lowPrime_12263) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12263) (q := 12269) (by exact lowPrime_12269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12269) (q := 12277) (by exact lowPrime_12277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12277) (q := 12281) (by exact lowPrime_12281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12281) (q := 12289) (by exact lowPrime_12289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12289) (q := 12301) (by exact lowPrime_12301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_12708 (p := 12301) (q := 12323) (by exact lowPrime_12323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12323) (q := 12329) (by exact lowPrime_12329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12329) (q := 12343) (by exact lowPrime_12343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12343) (q := 12347) (by exact lowPrime_12347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12347) (q := 12373) (by exact lowPrime_12373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12373) (q := 12377) (by exact lowPrime_12377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12377) (q := 12379) (by exact lowPrime_12379) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12379) (q := 12391) (by exact lowPrime_12391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
