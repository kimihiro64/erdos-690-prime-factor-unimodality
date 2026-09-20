import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 12 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData12 : List PocklingtonData := [
    { n := 12401, F := 12400, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 5, 31], residues := [(2, 6200), (5, 6547), (31, 4992)] },
    { n := 12409, F := 12408, R := 1, a := 7, factors := [2, 2, 2, 3, 11, 47], residues := [(2, 6204), (3, 5073), (11, 2225), (47, 7159)] },
    { n := 12413, F := 12412, R := 1, a := 2, factors := [2, 2, 29, 107], residues := [(2, 6206), (29, 10094), (107, 12056)] },
    { n := 12421, F := 12420, R := 1, a := 7, factors := [2, 2, 3, 3, 3, 5, 23], residues := [(2, 6210), (3, 6094), (5, 2768), (23, 11217)] },
    { n := 12433, F := 12432, R := 1, a := 13, factors := [2, 2, 2, 2, 3, 7, 37], residues := [(2, 6216), (3, 4181), (7, 1734), (37, 1838)] },
    { n := 12437, F := 12436, R := 1, a := 2, factors := [2, 2, 3109], residues := [(2, 6218), (3109, 5804)] },
    { n := 12451, F := 12450, R := 1, a := 3, factors := [2, 3, 5, 5, 83], residues := [(2, 6225), (3, 11613), (5, 4657), (83, 10897)] },
    { n := 12457, F := 12456, R := 1, a := 10, factors := [2, 2, 2, 3, 3, 173], residues := [(2, 6228), (3, 8142), (173, 11299)] },
    { n := 12473, F := 12472, R := 1, a := 3, factors := [2, 2, 2, 1559], residues := [(2, 6236), (1559, 7345)] },
    { n := 12479, F := 12478, R := 1, a := 23, factors := [2, 17, 367], residues := [(2, 6239), (17, 149), (367, 9801)] },
    { n := 12487, F := 12486, R := 1, a := 3, factors := [2, 3, 2081], residues := [(2, 6243), (3, 2484), (2081, 8662)] },
    { n := 12491, F := 12490, R := 1, a := 2, factors := [2, 5, 1249], residues := [(2, 6245), (5, 9723), (1249, 3602)] },
    { n := 12497, F := 12496, R := 1, a := 3, factors := [2, 2, 2, 2, 11, 71], residues := [(2, 6248), (11, 1844), (71, 459)] },
    { n := 12503, F := 12502, R := 1, a := 5, factors := [2, 7, 19, 47], residues := [(2, 6251), (7, 10651), (19, 11847), (47, 1457)] },
    { n := 12511, F := 12510, R := 1, a := 3, factors := [2, 3, 3, 5, 139], residues := [(2, 6255), (3, 1131), (5, 4449), (139, 6900)] },
    { n := 12517, F := 12516, R := 1, a := 6, factors := [2, 2, 3, 7, 149], residues := [(2, 6258), (3, 10381), (7, 9433), (149, 10602)] },
    { n := 12527, F := 12526, R := 1, a := 5, factors := [2, 6263], residues := [(2, 6263), (6263, 522)] },
    { n := 12539, F := 12538, R := 1, a := 2, factors := [2, 6269], residues := [(2, 6269), (6269, 4180)] },
    { n := 12541, F := 12540, R := 1, a := 14, factors := [2, 2, 3, 5, 11, 19], residues := [(2, 6270), (3, 794), (5, 9909), (11, 11141), (19, 3226)] },
    { n := 12547, F := 12546, R := 1, a := 2, factors := [2, 3, 3, 17, 41], residues := [(2, 6273), (3, 10474), (17, 10732), (41, 2315)] },
    { n := 12553, F := 12552, R := 1, a := 5, factors := [2, 2, 2, 3, 523], residues := [(2, 6276), (3, 6649), (523, 8792)] },
    { n := 12569, F := 12568, R := 1, a := 3, factors := [2, 2, 2, 1571], residues := [(2, 6284), (1571, 1209)] },
    { n := 12577, F := 12576, R := 1, a := 10, factors := [2, 2, 2, 2, 2, 3, 131], residues := [(2, 6288), (3, 9989), (131, 286)] },
    { n := 12583, F := 12582, R := 1, a := 5, factors := [2, 3, 3, 3, 233], residues := [(2, 6291), (3, 3628), (233, 3258)] },
    { n := 12589, F := 12588, R := 1, a := 2, factors := [2, 2, 3, 1049], residues := [(2, 6294), (3, 5975), (1049, 11885)] },
    { n := 12601, F := 12600, R := 1, a := 11, factors := [2, 2, 2, 3, 3, 5, 5, 7], residues := [(2, 6300), (3, 282), (5, 11301), (7, 10631)] },
    { n := 12611, F := 12610, R := 1, a := 2, factors := [2, 5, 13, 97], residues := [(2, 6305), (5, 5112), (13, 7453), (97, 7749)] },
    { n := 12613, F := 12612, R := 1, a := 2, factors := [2, 2, 3, 1051], residues := [(2, 6306), (3, 6029), (1051, 11344)] },
    { n := 12619, F := 12618, R := 1, a := 2, factors := [2, 3, 3, 701], residues := [(2, 6309), (3, 5464), (701, 2735)] },
    { n := 12637, F := 12636, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 3, 3, 13], residues := [(2, 6318), (3, 2024), (13, 8630)] },
    { n := 12641, F := 12640, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 5, 79], residues := [(2, 6320), (5, 3382), (79, 1581)] },
    { n := 12647, F := 12646, R := 1, a := 5, factors := [2, 6323], residues := [(2, 6323), (6323, 527)] },
    { n := 12653, F := 12652, R := 1, a := 2, factors := [2, 2, 3163], residues := [(2, 6326), (3163, 10966)] },
    { n := 12659, F := 12658, R := 1, a := 2, factors := [2, 6329], residues := [(2, 6329), (6329, 4220)] },
    { n := 12671, F := 12670, R := 1, a := 14, factors := [2, 5, 7, 181], residues := [(2, 6335), (5, 5372), (7, 9543), (181, 4836)] },
    { n := 12689, F := 12688, R := 1, a := 3, factors := [2, 2, 2, 2, 13, 61], residues := [(2, 6344), (13, 11382), (61, 11571)] },
    { n := 12697, F := 12696, R := 1, a := 7, factors := [2, 2, 2, 3, 23, 23], residues := [(2, 6348), (3, 8031), (23, 3721)] },
    { n := 12703, F := 12702, R := 1, a := 3, factors := [2, 3, 29, 73], residues := [(2, 6351), (3, 2449), (29, 9325), (73, 9787)] },
    { n := 12713, F := 12712, R := 1, a := 3, factors := [2, 2, 2, 7, 227], residues := [(2, 6356), (7, 4119), (227, 11856)] },
    { n := 12721, F := 12720, R := 1, a := 13, factors := [2, 2, 2, 2, 3, 5, 53], residues := [(2, 6360), (3, 11077), (5, 409), (53, 6892)] },
    { n := 12739, F := 12738, R := 1, a := 2, factors := [2, 3, 11, 193], residues := [(2, 6369), (3, 2384), (11, 5470), (193, 4199)] },
    { n := 12743, F := 12742, R := 1, a := 5, factors := [2, 23, 277], residues := [(2, 6371), (23, 11691), (277, 8739)] },
    { n := 12757, F := 12756, R := 1, a := 2, factors := [2, 2, 3, 1063], residues := [(2, 6378), (3, 9293), (1063, 8838)] },
    { n := 12763, F := 12762, R := 1, a := 2, factors := [2, 3, 3, 709], residues := [(2, 6381), (3, 7497), (709, 3792)] },
    { n := 12781, F := 12780, R := 1, a := 2, factors := [2, 2, 3, 3, 5, 71], residues := [(2, 6390), (3, 1074), (5, 8861), (71, 10809)] },
    { n := 12791, F := 12790, R := 1, a := 7, factors := [2, 5, 1279], residues := [(2, 6395), (5, 131), (1279, 7219)] },
    { n := 12799, F := 12798, R := 1, a := 13, factors := [2, 3, 3, 3, 3, 79], residues := [(2, 6399), (3, 7726), (79, 4348)] },
    { n := 12809, F := 12808, R := 1, a := 3, factors := [2, 2, 2, 1601], residues := [(2, 6404), (1601, 7949)] },
    { n := 12821, F := 12820, R := 1, a := 2, factors := [2, 2, 5, 641], residues := [(2, 6410), (5, 10098), (641, 2567)] },
    { n := 12823, F := 12822, R := 1, a := 3, factors := [2, 3, 2137], residues := [(2, 6411), (3, 9012), (2137, 1004)] },
    { n := 12829, F := 12828, R := 1, a := 2, factors := [2, 2, 3, 1069], residues := [(2, 6414), (3, 7996), (1069, 2995)] },
    { n := 12841, F := 12840, R := 1, a := 21, factors := [2, 2, 2, 3, 5, 107], residues := [(2, 6420), (3, 1917), (5, 9998), (107, 10763)] },
    { n := 12853, F := 12852, R := 1, a := 5, factors := [2, 2, 3, 3, 3, 7, 17], residues := [(2, 6426), (3, 6544), (7, 5835), (17, 1482)] },
    { n := 12889, F := 12888, R := 1, a := 13, factors := [2, 2, 2, 3, 3, 179], residues := [(2, 6444), (3, 1419), (179, 11563)] },
    { n := 12893, F := 12892, R := 1, a := 3, factors := [2, 2, 11, 293], residues := [(2, 6446), (11, 7505), (293, 12725)] },
    { n := 12899, F := 12898, R := 1, a := 2, factors := [2, 6449], residues := [(2, 6449), (6449, 4300)] },
    { n := 12907, F := 12906, R := 1, a := 2, factors := [2, 3, 3, 3, 239], residues := [(2, 6453), (3, 11927), (239, 10694)] },
    { n := 12911, F := 12910, R := 1, a := 23, factors := [2, 5, 1291], residues := [(2, 6455), (5, 3482), (1291, 12198)] },
    { n := 12917, F := 12916, R := 1, a := 2, factors := [2, 2, 3229], residues := [(2, 6458), (3229, 6028)] },
    { n := 12919, F := 12918, R := 1, a := 6, factors := [2, 3, 2153], residues := [(2, 6459), (3, 6772), (2153, 705)] },
    { n := 12923, F := 12922, R := 1, a := 2, factors := [2, 7, 13, 71], residues := [(2, 6461), (7, 2364), (13, 710), (71, 204)] },
    { n := 12941, F := 12940, R := 1, a := 2, factors := [2, 2, 5, 647], residues := [(2, 6470), (5, 11933), (647, 4204)] },
    { n := 12953, F := 12952, R := 1, a := 3, factors := [2, 2, 2, 1619], residues := [(2, 6476), (1619, 10471)] },
    { n := 12959, F := 12958, R := 1, a := 7, factors := [2, 11, 19, 31], residues := [(2, 6479), (11, 5493), (19, 1943), (31, 5925)] },
    { n := 12967, F := 12966, R := 1, a := 3, factors := [2, 3, 2161], residues := [(2, 6483), (3, 10550), (2161, 8140)] },
    { n := 12973, F := 12972, R := 1, a := 14, factors := [2, 2, 3, 23, 47], residues := [(2, 6486), (3, 6286), (23, 6563), (47, 8449)] },
    { n := 12979, F := 12978, R := 1, a := 2, factors := [2, 3, 3, 7, 103], residues := [(2, 6489), (3, 1280), (7, 7548), (103, 12058)] },
    { n := 12983, F := 12982, R := 1, a := 5, factors := [2, 6491], residues := [(2, 6491), (6491, 541)] },
    { n := 13001, F := 13000, R := 1, a := 3, factors := [2, 2, 2, 5, 5, 5, 13], residues := [(2, 6500), (5, 10677), (13, 9781)] },
    { n := 13003, F := 13002, R := 1, a := 5, factors := [2, 3, 11, 197], residues := [(2, 6501), (3, 562), (11, 1109), (197, 4618)] },
    { n := 13007, F := 13006, R := 1, a := 5, factors := [2, 7, 929], residues := [(2, 6503), (7, 1412), (929, 9066)] },
    { n := 13009, F := 13008, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 271], residues := [(2, 6504), (3, 5673), (271, 7014)] },
    { n := 13033, F := 13032, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 181], residues := [(2, 6516), (3, 9429), (181, 4308)] },
    { n := 13037, F := 13036, R := 1, a := 2, factors := [2, 2, 3259], residues := [(2, 6518), (3259, 6084)] },
    { n := 13043, F := 13042, R := 1, a := 2, factors := [2, 6521], residues := [(2, 6521), (6521, 4348)] },
    { n := 13049, F := 13048, R := 1, a := 3, factors := [2, 2, 2, 7, 233], residues := [(2, 6524), (7, 1367), (233, 5250)] },
    { n := 13063, F := 13062, R := 1, a := 5, factors := [2, 3, 7, 311], residues := [(2, 6531), (3, 4803), (7, 6029), (311, 11075)] },
    { n := 13093, F := 13092, R := 1, a := 6, factors := [2, 2, 3, 1091], residues := [(2, 6546), (3, 9158), (1091, 11376)] },
    { n := 13099, F := 13098, R := 1, a := 3, factors := [2, 3, 37, 59], residues := [(2, 6549), (3, 10271), (37, 3049), (59, 10509)] },
    { n := 13103, F := 13102, R := 1, a := 5, factors := [2, 6551], residues := [(2, 6551), (6551, 546)] },
    { n := 13109, F := 13108, R := 1, a := 2, factors := [2, 2, 29, 113], residues := [(2, 6554), (29, 12698), (113, 4325)] },
    { n := 13121, F := 13120, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 5, 41], residues := [(2, 6560), (5, 7246), (41, 9941)] },
    { n := 13127, F := 13126, R := 1, a := 5, factors := [2, 6563], residues := [(2, 6563), (6563, 547)] },
    { n := 13147, F := 13146, R := 1, a := 2, factors := [2, 3, 7, 313], residues := [(2, 6573), (3, 12515), (7, 8180), (313, 9613)] },
    { n := 13151, F := 13150, R := 1, a := 13, factors := [2, 5, 5, 263], residues := [(2, 6575), (5, 251), (263, 9639)] },
    { n := 13159, F := 13158, R := 1, a := 3, factors := [2, 3, 3, 17, 43], residues := [(2, 6579), (3, 8671), (17, 6336), (43, 7451)] },
    { n := 13163, F := 13162, R := 1, a := 2, factors := [2, 6581], residues := [(2, 6581), (6581, 4388)] },
    { n := 13171, F := 13170, R := 1, a := 11, factors := [2, 3, 5, 439], residues := [(2, 6585), (3, 11215), (5, 302), (439, 8691)] },
    { n := 13177, F := 13176, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 3, 61], residues := [(2, 6588), (3, 9790), (61, 4466)] },
    { n := 13183, F := 13182, R := 1, a := 3, factors := [2, 3, 13, 13, 13], residues := [(2, 6591), (3, 4973), (13, 2299)] },
    { n := 13187, F := 13186, R := 1, a := 2, factors := [2, 19, 347], residues := [(2, 6593), (19, 6384), (347, 7007)] },
    { n := 13217, F := 13216, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 7, 59], residues := [(2, 6608), (7, 3824), (59, 6257)] },
    { n := 13219, F := 13218, R := 1, a := 3, factors := [2, 3, 2203], residues := [(2, 6609), (3, 6904), (2203, 12874)] },
    { n := 13229, F := 13228, R := 1, a := 2, factors := [2, 2, 3307], residues := [(2, 6614), (3307, 882)] },
    { n := 13241, F := 13240, R := 1, a := 3, factors := [2, 2, 2, 5, 331], residues := [(2, 6620), (5, 779), (331, 4678)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData12_valid : PocklingtonRow.Valid lowPocklingtonData12 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPrime_12401 : Nat.Prime 12401 := by
  let d := lowPocklingtonData12.get ⟨0, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12409 : Nat.Prime 12409 := by
  let d := lowPocklingtonData12.get ⟨1, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12413 : Nat.Prime 12413 := by
  let d := lowPocklingtonData12.get ⟨2, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12421 : Nat.Prime 12421 := by
  let d := lowPocklingtonData12.get ⟨3, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12433 : Nat.Prime 12433 := by
  let d := lowPocklingtonData12.get ⟨4, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12437 : Nat.Prime 12437 := by
  let d := lowPocklingtonData12.get ⟨5, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12451 : Nat.Prime 12451 := by
  let d := lowPocklingtonData12.get ⟨6, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12457 : Nat.Prime 12457 := by
  let d := lowPocklingtonData12.get ⟨7, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12473 : Nat.Prime 12473 := by
  let d := lowPocklingtonData12.get ⟨8, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12479 : Nat.Prime 12479 := by
  let d := lowPocklingtonData12.get ⟨9, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12487 : Nat.Prime 12487 := by
  let d := lowPocklingtonData12.get ⟨10, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12491 : Nat.Prime 12491 := by
  let d := lowPocklingtonData12.get ⟨11, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12497 : Nat.Prime 12497 := by
  let d := lowPocklingtonData12.get ⟨12, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12503 : Nat.Prime 12503 := by
  let d := lowPocklingtonData12.get ⟨13, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12511 : Nat.Prime 12511 := by
  let d := lowPocklingtonData12.get ⟨14, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12517 : Nat.Prime 12517 := by
  let d := lowPocklingtonData12.get ⟨15, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12527 : Nat.Prime 12527 := by
  let d := lowPocklingtonData12.get ⟨16, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12539 : Nat.Prime 12539 := by
  let d := lowPocklingtonData12.get ⟨17, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12541 : Nat.Prime 12541 := by
  let d := lowPocklingtonData12.get ⟨18, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12547 : Nat.Prime 12547 := by
  let d := lowPocklingtonData12.get ⟨19, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12553 : Nat.Prime 12553 := by
  let d := lowPocklingtonData12.get ⟨20, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12569 : Nat.Prime 12569 := by
  let d := lowPocklingtonData12.get ⟨21, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12577 : Nat.Prime 12577 := by
  let d := lowPocklingtonData12.get ⟨22, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12583 : Nat.Prime 12583 := by
  let d := lowPocklingtonData12.get ⟨23, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12589 : Nat.Prime 12589 := by
  let d := lowPocklingtonData12.get ⟨24, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12601 : Nat.Prime 12601 := by
  let d := lowPocklingtonData12.get ⟨25, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12611 : Nat.Prime 12611 := by
  let d := lowPocklingtonData12.get ⟨26, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12613 : Nat.Prime 12613 := by
  let d := lowPocklingtonData12.get ⟨27, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12619 : Nat.Prime 12619 := by
  let d := lowPocklingtonData12.get ⟨28, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12637 : Nat.Prime 12637 := by
  let d := lowPocklingtonData12.get ⟨29, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12641 : Nat.Prime 12641 := by
  let d := lowPocklingtonData12.get ⟨30, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12647 : Nat.Prime 12647 := by
  let d := lowPocklingtonData12.get ⟨31, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12653 : Nat.Prime 12653 := by
  let d := lowPocklingtonData12.get ⟨32, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12659 : Nat.Prime 12659 := by
  let d := lowPocklingtonData12.get ⟨33, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12671 : Nat.Prime 12671 := by
  let d := lowPocklingtonData12.get ⟨34, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12689 : Nat.Prime 12689 := by
  let d := lowPocklingtonData12.get ⟨35, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12697 : Nat.Prime 12697 := by
  let d := lowPocklingtonData12.get ⟨36, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12703 : Nat.Prime 12703 := by
  let d := lowPocklingtonData12.get ⟨37, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12713 : Nat.Prime 12713 := by
  let d := lowPocklingtonData12.get ⟨38, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12721 : Nat.Prime 12721 := by
  let d := lowPocklingtonData12.get ⟨39, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12739 : Nat.Prime 12739 := by
  let d := lowPocklingtonData12.get ⟨40, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12743 : Nat.Prime 12743 := by
  let d := lowPocklingtonData12.get ⟨41, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12757 : Nat.Prime 12757 := by
  let d := lowPocklingtonData12.get ⟨42, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12763 : Nat.Prime 12763 := by
  let d := lowPocklingtonData12.get ⟨43, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12781 : Nat.Prime 12781 := by
  let d := lowPocklingtonData12.get ⟨44, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12791 : Nat.Prime 12791 := by
  let d := lowPocklingtonData12.get ⟨45, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12799 : Nat.Prime 12799 := by
  let d := lowPocklingtonData12.get ⟨46, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12809 : Nat.Prime 12809 := by
  let d := lowPocklingtonData12.get ⟨47, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12821 : Nat.Prime 12821 := by
  let d := lowPocklingtonData12.get ⟨48, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12823 : Nat.Prime 12823 := by
  let d := lowPocklingtonData12.get ⟨49, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12829 : Nat.Prime 12829 := by
  let d := lowPocklingtonData12.get ⟨50, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12841 : Nat.Prime 12841 := by
  let d := lowPocklingtonData12.get ⟨51, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12853 : Nat.Prime 12853 := by
  let d := lowPocklingtonData12.get ⟨52, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12889 : Nat.Prime 12889 := by
  let d := lowPocklingtonData12.get ⟨53, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12893 : Nat.Prime 12893 := by
  let d := lowPocklingtonData12.get ⟨54, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12899 : Nat.Prime 12899 := by
  let d := lowPocklingtonData12.get ⟨55, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12907 : Nat.Prime 12907 := by
  let d := lowPocklingtonData12.get ⟨56, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12911 : Nat.Prime 12911 := by
  let d := lowPocklingtonData12.get ⟨57, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12917 : Nat.Prime 12917 := by
  let d := lowPocklingtonData12.get ⟨58, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12919 : Nat.Prime 12919 := by
  let d := lowPocklingtonData12.get ⟨59, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12923 : Nat.Prime 12923 := by
  let d := lowPocklingtonData12.get ⟨60, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12941 : Nat.Prime 12941 := by
  let d := lowPocklingtonData12.get ⟨61, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12953 : Nat.Prime 12953 := by
  let d := lowPocklingtonData12.get ⟨62, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12959 : Nat.Prime 12959 := by
  let d := lowPocklingtonData12.get ⟨63, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12967 : Nat.Prime 12967 := by
  let d := lowPocklingtonData12.get ⟨64, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12973 : Nat.Prime 12973 := by
  let d := lowPocklingtonData12.get ⟨65, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12979 : Nat.Prime 12979 := by
  let d := lowPocklingtonData12.get ⟨66, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_12983 : Nat.Prime 12983 := by
  let d := lowPocklingtonData12.get ⟨67, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13001 : Nat.Prime 13001 := by
  let d := lowPocklingtonData12.get ⟨68, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13003 : Nat.Prime 13003 := by
  let d := lowPocklingtonData12.get ⟨69, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13007 : Nat.Prime 13007 := by
  let d := lowPocklingtonData12.get ⟨70, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13009 : Nat.Prime 13009 := by
  let d := lowPocklingtonData12.get ⟨71, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13033 : Nat.Prime 13033 := by
  let d := lowPocklingtonData12.get ⟨72, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13037 : Nat.Prime 13037 := by
  let d := lowPocklingtonData12.get ⟨73, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13043 : Nat.Prime 13043 := by
  let d := lowPocklingtonData12.get ⟨74, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13049 : Nat.Prime 13049 := by
  let d := lowPocklingtonData12.get ⟨75, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13063 : Nat.Prime 13063 := by
  let d := lowPocklingtonData12.get ⟨76, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13093 : Nat.Prime 13093 := by
  let d := lowPocklingtonData12.get ⟨77, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13099 : Nat.Prime 13099 := by
  let d := lowPocklingtonData12.get ⟨78, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13103 : Nat.Prime 13103 := by
  let d := lowPocklingtonData12.get ⟨79, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13109 : Nat.Prime 13109 := by
  let d := lowPocklingtonData12.get ⟨80, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13121 : Nat.Prime 13121 := by
  let d := lowPocklingtonData12.get ⟨81, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13127 : Nat.Prime 13127 := by
  let d := lowPocklingtonData12.get ⟨82, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13147 : Nat.Prime 13147 := by
  let d := lowPocklingtonData12.get ⟨83, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13151 : Nat.Prime 13151 := by
  let d := lowPocklingtonData12.get ⟨84, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13159 : Nat.Prime 13159 := by
  let d := lowPocklingtonData12.get ⟨85, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13163 : Nat.Prime 13163 := by
  let d := lowPocklingtonData12.get ⟨86, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13171 : Nat.Prime 13171 := by
  let d := lowPocklingtonData12.get ⟨87, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13177 : Nat.Prime 13177 := by
  let d := lowPocklingtonData12.get ⟨88, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13183 : Nat.Prime 13183 := by
  let d := lowPocklingtonData12.get ⟨89, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13187 : Nat.Prime 13187 := by
  let d := lowPocklingtonData12.get ⟨90, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13217 : Nat.Prime 13217 := by
  let d := lowPocklingtonData12.get ⟨91, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13219 : Nat.Prime 13219 := by
  let d := lowPocklingtonData12.get ⟨92, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13229 : Nat.Prime 13229 := by
  let d := lowPocklingtonData12.get ⟨93, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp

theorem lowPrime_13241 : Nat.Prime 13241 := by
  let d := lowPocklingtonData12.get ⟨94, by simp [lowPocklingtonData12]⟩
  have hd : d ∈ lowPocklingtonData12 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData12_valid hd
  simpa [d, lowPocklingtonData12] using hp
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12391) (q := 12401) (by exact lowPrime_12401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12401) (q := 12409) (by exact lowPrime_12409) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12409) (q := 12413) (by exact lowPrime_12413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12413) (q := 12421) (by exact lowPrime_12421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12421) (q := 12433) (by exact lowPrime_12433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12433) (q := 12437) (by exact lowPrime_12437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12437) (q := 12451) (by exact lowPrime_12451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12451) (q := 12457) (by exact lowPrime_12457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part05_chain :
    DusartPrimeRowsChain 12391 12456 dusartPrimeRows_12097_12712_part05 := by
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
def dusartPrimeRows_12097_12712_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12457) (q := 12473) (by exact lowPrime_12473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12473) (q := 12479) (by exact lowPrime_12479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12479) (q := 12487) (by exact lowPrime_12487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12487) (q := 12491) (by exact lowPrime_12491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12491) (q := 12497) (by exact lowPrime_12497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12497) (q := 12503) (by exact lowPrime_12503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12503) (q := 12511) (by exact lowPrime_12511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12511) (q := 12517) (by exact lowPrime_12517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part06_chain :
    DusartPrimeRowsChain 12457 12516 dusartPrimeRows_12097_12712_part06 := by
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
def dusartPrimeRows_12097_12712_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12517) (q := 12527) (by exact lowPrime_12527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12527) (q := 12539) (by exact lowPrime_12539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12539) (q := 12541) (by exact lowPrime_12541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12541) (q := 12547) (by exact lowPrime_12547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12547) (q := 12553) (by exact lowPrime_12553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12553) (q := 12569) (by exact lowPrime_12569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12569) (q := 12577) (by exact lowPrime_12577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12577) (q := 12583) (by exact lowPrime_12583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part07_chain :
    DusartPrimeRowsChain 12517 12582 dusartPrimeRows_12097_12712_part07 := by
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
def dusartPrimeRows_12097_12712_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12583) (q := 12589) (by exact lowPrime_12589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12589) (q := 12601) (by exact lowPrime_12601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12601) (q := 12611) (by exact lowPrime_12611) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12611) (q := 12613) (by exact lowPrime_12613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12613) (q := 12619) (by exact lowPrime_12619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12619) (q := 12637) (by exact lowPrime_12637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12637) (q := 12641) (by exact lowPrime_12641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12641) (q := 12647) (by exact lowPrime_12647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part08_chain :
    DusartPrimeRowsChain 12583 12646 dusartPrimeRows_12097_12712_part08 := by
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
def dusartPrimeRows_12097_12712_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12647) (q := 12653) (by exact lowPrime_12653) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12653) (q := 12659) (by exact lowPrime_12659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12659) (q := 12671) (by exact lowPrime_12671) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12671) (q := 12689) (by exact lowPrime_12689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12689) (q := 12697) (by exact lowPrime_12697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12697) (q := 12703) (by exact lowPrime_12703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12703) (q := 12713) (by exact lowPrime_12713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part09_chain :
    DusartPrimeRowsChain 12647 12712 dusartPrimeRows_12097_12712_part09 := by
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
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12713) (q := 12721) (by exact lowPrime_12721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12721) (q := 12739) (by exact lowPrime_12739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12739) (q := 12743) (by exact lowPrime_12743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12743) (q := 12757) (by exact lowPrime_12757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12757) (q := 12763) (by exact lowPrime_12763) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12763) (q := 12781) (by exact lowPrime_12781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12781) (q := 12791) (by exact lowPrime_12791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12791) (q := 12799) (by exact lowPrime_12799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part01_chain :
    DusartPrimeRowsChain 12713 12798 dusartPrimeRows_12713_13366_part01 := by
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
def dusartPrimeRows_12713_13366_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12799) (q := 12809) (by exact lowPrime_12809) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12809) (q := 12821) (by exact lowPrime_12821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12821) (q := 12823) (by exact lowPrime_12823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12823) (q := 12829) (by exact lowPrime_12829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12829) (q := 12841) (by exact lowPrime_12841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12841) (q := 12853) (by exact lowPrime_12853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12853) (q := 12889) (by exact lowPrime_12889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12889) (q := 12893) (by exact lowPrime_12893) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part02_chain :
    DusartPrimeRowsChain 12799 12892 dusartPrimeRows_12713_13366_part02 := by
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
def dusartPrimeRows_12713_13366_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12893) (q := 12899) (by exact lowPrime_12899) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12899) (q := 12907) (by exact lowPrime_12907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12907) (q := 12911) (by exact lowPrime_12911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12911) (q := 12917) (by exact lowPrime_12917) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12917) (q := 12919) (by exact lowPrime_12919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12919) (q := 12923) (by exact lowPrime_12923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12923) (q := 12941) (by exact lowPrime_12941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12941) (q := 12953) (by exact lowPrime_12953) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part03_chain :
    DusartPrimeRowsChain 12893 12952 dusartPrimeRows_12713_13366_part03 := by
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
def dusartPrimeRows_12713_13366_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12953) (q := 12959) (by exact lowPrime_12959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12959) (q := 12967) (by exact lowPrime_12967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12967) (q := 12973) (by exact lowPrime_12973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12973) (q := 12979) (by exact lowPrime_12979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12979) (q := 12983) (by exact lowPrime_12983) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12983) (q := 13001) (by exact lowPrime_13001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13001) (q := 13003) (by exact lowPrime_13003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13003) (q := 13007) (by exact lowPrime_13007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part04_chain :
    DusartPrimeRowsChain 12953 13006 dusartPrimeRows_12713_13366_part04 := by
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
def dusartPrimeRows_12713_13366_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13007) (q := 13009) (by exact lowPrime_13009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13009) (q := 13033) (by exact lowPrime_13033) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13033) (q := 13037) (by exact lowPrime_13037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13037) (q := 13043) (by exact lowPrime_13043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13043) (q := 13049) (by exact lowPrime_13049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13049) (q := 13063) (by exact lowPrime_13063) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13063) (q := 13093) (by exact lowPrime_13093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13093) (q := 13099) (by exact lowPrime_13099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part05_chain :
    DusartPrimeRowsChain 13007 13098 dusartPrimeRows_12713_13366_part05 := by
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
def dusartPrimeRows_12713_13366_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13099) (q := 13103) (by exact lowPrime_13103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13103) (q := 13109) (by exact lowPrime_13109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13109) (q := 13121) (by exact lowPrime_13121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13121) (q := 13127) (by exact lowPrime_13127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13127) (q := 13147) (by exact lowPrime_13147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13147) (q := 13151) (by exact lowPrime_13151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13151) (q := 13159) (by exact lowPrime_13159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13159) (q := 13163) (by exact lowPrime_13163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part06_chain :
    DusartPrimeRowsChain 13099 13162 dusartPrimeRows_12713_13366_part06 := by
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
def dusartPrimeRows_12713_13366_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13163) (q := 13171) (by exact lowPrime_13171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13171) (q := 13177) (by exact lowPrime_13177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13177) (q := 13183) (by exact lowPrime_13183) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13183) (q := 13187) (by exact lowPrime_13187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13187) (q := 13217) (by exact lowPrime_13217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13217) (q := 13219) (by exact lowPrime_13219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13219) (q := 13229) (by exact lowPrime_13229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13229) (q := 13241) (by exact lowPrime_13241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part07_chain :
    DusartPrimeRowsChain 13163 13240 dusartPrimeRows_12713_13366_part07 := by
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
