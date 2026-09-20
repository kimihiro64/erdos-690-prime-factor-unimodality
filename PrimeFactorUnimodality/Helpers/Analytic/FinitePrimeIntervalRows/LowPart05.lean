import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 05 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData05 : List PocklingtonData := [
    { n := 6451, F := 6450, R := 1, a := 3, factors := [2, 3, 5, 5, 43], residues := [(2, 3225), (3, 2079), (5, 2381), (43, 4976)] },
    { n := 6469, F := 6468, R := 1, a := 2, factors := [2, 2, 3, 7, 7, 11], residues := [(2, 3234), (3, 2648), (7, 2440), (11, 4342)] },
    { n := 6473, F := 6472, R := 1, a := 3, factors := [2, 2, 2, 809], residues := [(2, 3236), (809, 6101)] },
    { n := 6481, F := 6480, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 3, 3, 3, 5], residues := [(2, 3240), (3, 2133), (5, 1195)] },
    { n := 6491, F := 6490, R := 1, a := 2, factors := [2, 5, 11, 59], residues := [(2, 3245), (5, 963), (11, 1063), (59, 5417)] },
    { n := 6521, F := 6520, R := 1, a := 6, factors := [2, 2, 2, 5, 163], residues := [(2, 3260), (5, 3465), (163, 3708)] },
    { n := 6529, F := 6528, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 2, 3, 17], residues := [(2, 3264), (3, 4516), (17, 1450)] },
    { n := 6547, F := 6546, R := 1, a := 2, factors := [2, 3, 1091], residues := [(2, 3273), (3, 777), (1091, 3949)] },
    { n := 6551, F := 6550, R := 1, a := 17, factors := [2, 5, 5, 131], residues := [(2, 3275), (5, 5283), (131, 3333)] },
    { n := 6553, F := 6552, R := 1, a := 10, factors := [2, 2, 2, 3, 3, 7, 13], residues := [(2, 3276), (3, 3720), (7, 1608), (13, 661)] },
    { n := 6563, F := 6562, R := 1, a := 5, factors := [2, 17, 193], residues := [(2, 3281), (17, 3199), (193, 2244)] },
    { n := 6569, F := 6568, R := 1, a := 3, factors := [2, 2, 2, 821], residues := [(2, 3284), (821, 5839)] },
    { n := 6571, F := 6570, R := 1, a := 3, factors := [2, 3, 3, 5, 73], residues := [(2, 3285), (3, 3387), (5, 6443), (73, 6452)] },
    { n := 6577, F := 6576, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 137], residues := [(2, 3288), (3, 4502), (137, 2000)] },
    { n := 6581, F := 6580, R := 1, a := 14, factors := [2, 2, 5, 7, 47], residues := [(2, 3290), (5, 5454), (7, 1674), (47, 369)] },
    { n := 6599, F := 6598, R := 1, a := 13, factors := [2, 3299], residues := [(2, 3299), (3299, 982)] },
    { n := 6607, F := 6606, R := 1, a := 3, factors := [2, 3, 3, 367], residues := [(2, 3303), (3, 3898), (367, 6055)] },
    { n := 6619, F := 6618, R := 1, a := 2, factors := [2, 3, 1103], residues := [(2, 3309), (3, 4602), (1103, 4938)] },
    { n := 6637, F := 6636, R := 1, a := 2, factors := [2, 2, 3, 7, 79], residues := [(2, 3318), (3, 4881), (7, 2523), (79, 2313)] },
    { n := 6653, F := 6652, R := 1, a := 2, factors := [2, 2, 1663], residues := [(2, 3326), (1663, 5766)] },
    { n := 6659, F := 6658, R := 1, a := 2, factors := [2, 3329], residues := [(2, 3329), (3329, 2220)] },
    { n := 6661, F := 6660, R := 1, a := 6, factors := [2, 2, 3, 3, 5, 37], residues := [(2, 3330), (3, 449), (5, 2784), (37, 4999)] },
    { n := 6673, F := 6672, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 139], residues := [(2, 3336), (3, 464), (139, 6387)] },
    { n := 6679, F := 6678, R := 1, a := 7, factors := [2, 3, 3, 7, 53], residues := [(2, 3339), (3, 4138), (7, 705), (53, 5402)] },
    { n := 6689, F := 6688, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 11, 19], residues := [(2, 3344), (11, 2711), (19, 4069)] },
    { n := 6691, F := 6690, R := 1, a := 2, factors := [2, 3, 5, 223], residues := [(2, 3345), (3, 5433), (5, 3847), (223, 106)] },
    { n := 6701, F := 6700, R := 1, a := 2, factors := [2, 2, 5, 5, 67], residues := [(2, 3350), (5, 4052), (67, 2296)] },
    { n := 6703, F := 6702, R := 1, a := 5, factors := [2, 3, 1117], residues := [(2, 3351), (3, 6209), (1117, 4651)] },
    { n := 6709, F := 6708, R := 1, a := 2, factors := [2, 2, 3, 13, 43], residues := [(2, 3354), (3, 4059), (13, 2379), (43, 380)] },
    { n := 6719, F := 6718, R := 1, a := 11, factors := [2, 3359], residues := [(2, 3359), (3359, 56)] },
    { n := 6733, F := 6732, R := 1, a := 2, factors := [2, 2, 3, 3, 11, 17], residues := [(2, 3366), (3, 206), (11, 1997), (17, 4469)] },
    { n := 6737, F := 6736, R := 1, a := 3, factors := [2, 2, 2, 2, 421], residues := [(2, 3368), (421, 6471)] },
    { n := 6761, F := 6760, R := 1, a := 3, factors := [2, 2, 2, 5, 13, 13], residues := [(2, 3380), (5, 2883), (13, 6066)] },
    { n := 6763, F := 6762, R := 1, a := 2, factors := [2, 3, 7, 7, 23], residues := [(2, 3381), (3, 718), (7, 573), (23, 2861)] },
    { n := 6779, F := 6778, R := 1, a := 2, factors := [2, 3389], residues := [(2, 3389), (3389, 2260)] },
    { n := 6781, F := 6780, R := 1, a := 2, factors := [2, 2, 3, 5, 113], residues := [(2, 3390), (3, 5805), (5, 2015), (113, 4281)] },
    { n := 6791, F := 6790, R := 1, a := 7, factors := [2, 5, 7, 97], residues := [(2, 3395), (5, 2688), (7, 208), (97, 6748)] },
    { n := 6793, F := 6792, R := 1, a := 10, factors := [2, 2, 2, 3, 283], residues := [(2, 3396), (3, 6403), (283, 3816)] },
    { n := 6803, F := 6802, R := 1, a := 2, factors := [2, 19, 179], residues := [(2, 3401), (19, 585), (179, 3982)] },
    { n := 6823, F := 6822, R := 1, a := 3, factors := [2, 3, 3, 379], residues := [(2, 3411), (3, 3169), (379, 3504)] },
    { n := 6827, F := 6826, R := 1, a := 2, factors := [2, 3413], residues := [(2, 3413), (3413, 2276)] },
    { n := 6829, F := 6828, R := 1, a := 2, factors := [2, 2, 3, 569], residues := [(2, 3414), (3, 2031), (569, 2845)] },
    { n := 6833, F := 6832, R := 1, a := 3, factors := [2, 2, 2, 2, 7, 61], residues := [(2, 3416), (7, 6811), (61, 2179)] },
    { n := 6841, F := 6840, R := 1, a := 22, factors := [2, 2, 2, 3, 3, 5, 19], residues := [(2, 3420), (3, 3624), (5, 3423), (19, 4003)] },
    { n := 6857, F := 6856, R := 1, a := 3, factors := [2, 2, 2, 857], residues := [(2, 3428), (857, 1847)] },
    { n := 6863, F := 6862, R := 1, a := 5, factors := [2, 47, 73], residues := [(2, 3431), (47, 382), (73, 4422)] },
    { n := 6869, F := 6868, R := 1, a := 2, factors := [2, 2, 17, 101], residues := [(2, 3434), (17, 572), (101, 3734)] },
    { n := 6871, F := 6870, R := 1, a := 3, factors := [2, 3, 5, 229], residues := [(2, 3435), (3, 1801), (5, 3908), (229, 411)] },
    { n := 6883, F := 6882, R := 1, a := 2, factors := [2, 3, 31, 37], residues := [(2, 3441), (3, 2367), (31, 1683), (37, 6021)] },
    { n := 6899, F := 6898, R := 1, a := 2, factors := [2, 3449], residues := [(2, 3449), (3449, 2300)] },
    { n := 6907, F := 6906, R := 1, a := 2, factors := [2, 3, 1151], residues := [(2, 3453), (3, 5223), (1151, 1206)] },
    { n := 6911, F := 6910, R := 1, a := 7, factors := [2, 5, 691], residues := [(2, 3455), (5, 4248), (691, 3372)] },
    { n := 6917, F := 6916, R := 1, a := 2, factors := [2, 2, 7, 13, 19], residues := [(2, 3458), (7, 3679), (13, 5162), (19, 3633)] },
    { n := 6947, F := 6946, R := 1, a := 2, factors := [2, 23, 151], residues := [(2, 3473), (23, 5825), (151, 4994)] },
    { n := 6949, F := 6948, R := 1, a := 2, factors := [2, 2, 3, 3, 193], residues := [(2, 3474), (3, 6301), (193, 4961)] },
    { n := 6959, F := 6958, R := 1, a := 7, factors := [2, 7, 7, 71], residues := [(2, 3479), (7, 3825), (71, 4115)] },
    { n := 6961, F := 6960, R := 1, a := 13, factors := [2, 2, 2, 2, 3, 5, 29], residues := [(2, 3480), (3, 4471), (5, 640), (29, 749)] },
    { n := 6967, F := 6966, R := 1, a := 5, factors := [2, 3, 3, 3, 3, 43], residues := [(2, 3483), (3, 127), (43, 4605)] },
    { n := 6971, F := 6970, R := 1, a := 2, factors := [2, 5, 17, 41], residues := [(2, 3485), (5, 2715), (17, 5236), (41, 923)] },
    { n := 6977, F := 6976, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 109], residues := [(2, 3488), (109, 3841)] },
    { n := 6983, F := 6982, R := 1, a := 5, factors := [2, 3491], residues := [(2, 3491), (3491, 291)] },
    { n := 6991, F := 6990, R := 1, a := 6, factors := [2, 3, 5, 233], residues := [(2, 3495), (3, 460), (5, 1550), (233, 5837)] },
    { n := 6997, F := 6996, R := 1, a := 5, factors := [2, 2, 3, 11, 53], residues := [(2, 3498), (3, 969), (11, 3594), (53, 1658)] },
    { n := 7001, F := 7000, R := 1, a := 3, factors := [2, 2, 2, 5, 5, 5, 7], residues := [(2, 3500), (5, 6077), (7, 4721)] },
    { n := 7013, F := 7012, R := 1, a := 2, factors := [2, 2, 1753], residues := [(2, 3506), (1753, 6078)] },
    { n := 7019, F := 7018, R := 1, a := 2, factors := [2, 11, 11, 29], residues := [(2, 3509), (11, 607), (29, 2965)] },
    { n := 7027, F := 7026, R := 1, a := 2, factors := [2, 3, 1171], residues := [(2, 3513), (3, 174), (1171, 5577)] },
    { n := 7039, F := 7038, R := 1, a := 3, factors := [2, 3, 3, 17, 23], residues := [(2, 3519), (3, 2245), (17, 3663), (23, 6035)] },
    { n := 7043, F := 7042, R := 1, a := 2, factors := [2, 7, 503], residues := [(2, 3521), (7, 686), (503, 417)] },
    { n := 7057, F := 7056, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 3, 7, 7], residues := [(2, 3528), (3, 7008), (7, 5029)] },
    { n := 7069, F := 7068, R := 1, a := 2, factors := [2, 2, 3, 19, 31], residues := [(2, 3534), (3, 3036), (19, 1821), (31, 2187)] },
    { n := 7079, F := 7078, R := 1, a := 7, factors := [2, 3539], residues := [(2, 3539), (3539, 3687)] },
    { n := 7103, F := 7102, R := 1, a := 5, factors := [2, 53, 67], residues := [(2, 3551), (53, 5310), (67, 131)] },
    { n := 7109, F := 7108, R := 1, a := 2, factors := [2, 2, 1777], residues := [(2, 3554), (1777, 474)] },
    { n := 7121, F := 7120, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 89], residues := [(2, 3560), (5, 68), (89, 2793)] },
    { n := 7127, F := 7126, R := 1, a := 5, factors := [2, 7, 509], residues := [(2, 3563), (7, 4943), (509, 331)] },
    { n := 7129, F := 7128, R := 1, a := 7, factors := [2, 2, 2, 3, 3, 3, 3, 11], residues := [(2, 3564), (3, 416), (11, 3828)] },
    { n := 7151, F := 7150, R := 1, a := 7, factors := [2, 5, 5, 11, 13], residues := [(2, 3575), (5, 7117), (11, 7054), (13, 546)] },
    { n := 7159, F := 7158, R := 1, a := 3, factors := [2, 3, 1193], residues := [(2, 3579), (3, 3812), (1193, 3550)] },
    { n := 7177, F := 7176, R := 1, a := 10, factors := [2, 2, 2, 3, 13, 23], residues := [(2, 3588), (3, 679), (13, 175), (23, 3766)] },
    { n := 7187, F := 7186, R := 1, a := 2, factors := [2, 3593], residues := [(2, 3593), (3593, 2396)] },
    { n := 7193, F := 7192, R := 1, a := 3, factors := [2, 2, 2, 29, 31], residues := [(2, 3596), (29, 2978), (31, 722)] },
    { n := 7207, F := 7206, R := 1, a := 3, factors := [2, 3, 1201], residues := [(2, 3603), (3, 5417), (1201, 3653)] },
    { n := 7211, F := 7210, R := 1, a := 2, factors := [2, 5, 7, 103], residues := [(2, 3605), (5, 2383), (7, 1978), (103, 205)] },
    { n := 7213, F := 7212, R := 1, a := 5, factors := [2, 2, 3, 601], residues := [(2, 3606), (3, 867), (601, 6170)] },
    { n := 7219, F := 7218, R := 1, a := 2, factors := [2, 3, 3, 401], residues := [(2, 3609), (3, 6310), (401, 7072)] },
    { n := 7229, F := 7228, R := 1, a := 2, factors := [2, 2, 13, 139], residues := [(2, 3614), (13, 3225), (139, 2416)] },
    { n := 7237, F := 7236, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 67], residues := [(2, 3618), (3, 4214), (67, 1453)] },
    { n := 7243, F := 7242, R := 1, a := 2, factors := [2, 3, 17, 71], residues := [(2, 3621), (3, 3686), (17, 1136), (71, 3374)] },
    { n := 7247, F := 7246, R := 1, a := 5, factors := [2, 3623], residues := [(2, 3623), (3623, 302)] },
    { n := 7253, F := 7252, R := 1, a := 2, factors := [2, 2, 7, 7, 37], residues := [(2, 3626), (7, 3339), (37, 1021)] },
    { n := 7283, F := 7282, R := 1, a := 2, factors := [2, 11, 331], residues := [(2, 3641), (11, 1689), (331, 6064)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData05_valid : PocklingtonRow.Valid lowPocklingtonData05 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPrime_6451 : Nat.Prime 6451 := by
  let d := lowPocklingtonData05.get ⟨0, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6469 : Nat.Prime 6469 := by
  let d := lowPocklingtonData05.get ⟨1, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6473 : Nat.Prime 6473 := by
  let d := lowPocklingtonData05.get ⟨2, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6481 : Nat.Prime 6481 := by
  let d := lowPocklingtonData05.get ⟨3, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6491 : Nat.Prime 6491 := by
  let d := lowPocklingtonData05.get ⟨4, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6521 : Nat.Prime 6521 := by
  let d := lowPocklingtonData05.get ⟨5, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6529 : Nat.Prime 6529 := by
  let d := lowPocklingtonData05.get ⟨6, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6547 : Nat.Prime 6547 := by
  let d := lowPocklingtonData05.get ⟨7, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6551 : Nat.Prime 6551 := by
  let d := lowPocklingtonData05.get ⟨8, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6553 : Nat.Prime 6553 := by
  let d := lowPocklingtonData05.get ⟨9, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6563 : Nat.Prime 6563 := by
  let d := lowPocklingtonData05.get ⟨10, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6569 : Nat.Prime 6569 := by
  let d := lowPocklingtonData05.get ⟨11, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6571 : Nat.Prime 6571 := by
  let d := lowPocklingtonData05.get ⟨12, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6577 : Nat.Prime 6577 := by
  let d := lowPocklingtonData05.get ⟨13, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6581 : Nat.Prime 6581 := by
  let d := lowPocklingtonData05.get ⟨14, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6599 : Nat.Prime 6599 := by
  let d := lowPocklingtonData05.get ⟨15, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6607 : Nat.Prime 6607 := by
  let d := lowPocklingtonData05.get ⟨16, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6619 : Nat.Prime 6619 := by
  let d := lowPocklingtonData05.get ⟨17, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6637 : Nat.Prime 6637 := by
  let d := lowPocklingtonData05.get ⟨18, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6653 : Nat.Prime 6653 := by
  let d := lowPocklingtonData05.get ⟨19, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6659 : Nat.Prime 6659 := by
  let d := lowPocklingtonData05.get ⟨20, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6661 : Nat.Prime 6661 := by
  let d := lowPocklingtonData05.get ⟨21, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6673 : Nat.Prime 6673 := by
  let d := lowPocklingtonData05.get ⟨22, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6679 : Nat.Prime 6679 := by
  let d := lowPocklingtonData05.get ⟨23, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6689 : Nat.Prime 6689 := by
  let d := lowPocklingtonData05.get ⟨24, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6691 : Nat.Prime 6691 := by
  let d := lowPocklingtonData05.get ⟨25, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6701 : Nat.Prime 6701 := by
  let d := lowPocklingtonData05.get ⟨26, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6703 : Nat.Prime 6703 := by
  let d := lowPocklingtonData05.get ⟨27, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6709 : Nat.Prime 6709 := by
  let d := lowPocklingtonData05.get ⟨28, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6719 : Nat.Prime 6719 := by
  let d := lowPocklingtonData05.get ⟨29, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6733 : Nat.Prime 6733 := by
  let d := lowPocklingtonData05.get ⟨30, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6737 : Nat.Prime 6737 := by
  let d := lowPocklingtonData05.get ⟨31, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6761 : Nat.Prime 6761 := by
  let d := lowPocklingtonData05.get ⟨32, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6763 : Nat.Prime 6763 := by
  let d := lowPocklingtonData05.get ⟨33, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6779 : Nat.Prime 6779 := by
  let d := lowPocklingtonData05.get ⟨34, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6781 : Nat.Prime 6781 := by
  let d := lowPocklingtonData05.get ⟨35, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6791 : Nat.Prime 6791 := by
  let d := lowPocklingtonData05.get ⟨36, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6793 : Nat.Prime 6793 := by
  let d := lowPocklingtonData05.get ⟨37, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6803 : Nat.Prime 6803 := by
  let d := lowPocklingtonData05.get ⟨38, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6823 : Nat.Prime 6823 := by
  let d := lowPocklingtonData05.get ⟨39, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6827 : Nat.Prime 6827 := by
  let d := lowPocklingtonData05.get ⟨40, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6829 : Nat.Prime 6829 := by
  let d := lowPocklingtonData05.get ⟨41, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6833 : Nat.Prime 6833 := by
  let d := lowPocklingtonData05.get ⟨42, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6841 : Nat.Prime 6841 := by
  let d := lowPocklingtonData05.get ⟨43, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6857 : Nat.Prime 6857 := by
  let d := lowPocklingtonData05.get ⟨44, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6863 : Nat.Prime 6863 := by
  let d := lowPocklingtonData05.get ⟨45, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6869 : Nat.Prime 6869 := by
  let d := lowPocklingtonData05.get ⟨46, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6871 : Nat.Prime 6871 := by
  let d := lowPocklingtonData05.get ⟨47, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6883 : Nat.Prime 6883 := by
  let d := lowPocklingtonData05.get ⟨48, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6899 : Nat.Prime 6899 := by
  let d := lowPocklingtonData05.get ⟨49, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6907 : Nat.Prime 6907 := by
  let d := lowPocklingtonData05.get ⟨50, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6911 : Nat.Prime 6911 := by
  let d := lowPocklingtonData05.get ⟨51, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6917 : Nat.Prime 6917 := by
  let d := lowPocklingtonData05.get ⟨52, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6947 : Nat.Prime 6947 := by
  let d := lowPocklingtonData05.get ⟨53, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6949 : Nat.Prime 6949 := by
  let d := lowPocklingtonData05.get ⟨54, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6959 : Nat.Prime 6959 := by
  let d := lowPocklingtonData05.get ⟨55, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6961 : Nat.Prime 6961 := by
  let d := lowPocklingtonData05.get ⟨56, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6967 : Nat.Prime 6967 := by
  let d := lowPocklingtonData05.get ⟨57, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6971 : Nat.Prime 6971 := by
  let d := lowPocklingtonData05.get ⟨58, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6977 : Nat.Prime 6977 := by
  let d := lowPocklingtonData05.get ⟨59, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6983 : Nat.Prime 6983 := by
  let d := lowPocklingtonData05.get ⟨60, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6991 : Nat.Prime 6991 := by
  let d := lowPocklingtonData05.get ⟨61, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_6997 : Nat.Prime 6997 := by
  let d := lowPocklingtonData05.get ⟨62, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7001 : Nat.Prime 7001 := by
  let d := lowPocklingtonData05.get ⟨63, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7013 : Nat.Prime 7013 := by
  let d := lowPocklingtonData05.get ⟨64, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7019 : Nat.Prime 7019 := by
  let d := lowPocklingtonData05.get ⟨65, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7027 : Nat.Prime 7027 := by
  let d := lowPocklingtonData05.get ⟨66, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7039 : Nat.Prime 7039 := by
  let d := lowPocklingtonData05.get ⟨67, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7043 : Nat.Prime 7043 := by
  let d := lowPocklingtonData05.get ⟨68, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7057 : Nat.Prime 7057 := by
  let d := lowPocklingtonData05.get ⟨69, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7069 : Nat.Prime 7069 := by
  let d := lowPocklingtonData05.get ⟨70, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7079 : Nat.Prime 7079 := by
  let d := lowPocklingtonData05.get ⟨71, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7103 : Nat.Prime 7103 := by
  let d := lowPocklingtonData05.get ⟨72, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7109 : Nat.Prime 7109 := by
  let d := lowPocklingtonData05.get ⟨73, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7121 : Nat.Prime 7121 := by
  let d := lowPocklingtonData05.get ⟨74, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7127 : Nat.Prime 7127 := by
  let d := lowPocklingtonData05.get ⟨75, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7129 : Nat.Prime 7129 := by
  let d := lowPocklingtonData05.get ⟨76, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7151 : Nat.Prime 7151 := by
  let d := lowPocklingtonData05.get ⟨77, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7159 : Nat.Prime 7159 := by
  let d := lowPocklingtonData05.get ⟨78, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7177 : Nat.Prime 7177 := by
  let d := lowPocklingtonData05.get ⟨79, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7187 : Nat.Prime 7187 := by
  let d := lowPocklingtonData05.get ⟨80, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7193 : Nat.Prime 7193 := by
  let d := lowPocklingtonData05.get ⟨81, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7207 : Nat.Prime 7207 := by
  let d := lowPocklingtonData05.get ⟨82, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7211 : Nat.Prime 7211 := by
  let d := lowPocklingtonData05.get ⟨83, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7213 : Nat.Prime 7213 := by
  let d := lowPocklingtonData05.get ⟨84, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7219 : Nat.Prime 7219 := by
  let d := lowPocklingtonData05.get ⟨85, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7229 : Nat.Prime 7229 := by
  let d := lowPocklingtonData05.get ⟨86, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7237 : Nat.Prime 7237 := by
  let d := lowPocklingtonData05.get ⟨87, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7243 : Nat.Prime 7243 := by
  let d := lowPocklingtonData05.get ⟨88, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7247 : Nat.Prime 7247 := by
  let d := lowPocklingtonData05.get ⟨89, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7253 : Nat.Prime 7253 := by
  let d := lowPocklingtonData05.get ⟨90, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp

theorem lowPrime_7283 : Nat.Prime 7283 := by
  let d := lowPocklingtonData05.get ⟨91, by simp [lowPocklingtonData05]⟩
  have hd : d ∈ lowPocklingtonData05 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData05_valid hd
  simpa [d, lowPocklingtonData05] using hp
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6449) (q := 6451) (by exact lowPrime_6451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6451) (q := 6469) (by exact lowPrime_6469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6469) (q := 6473) (by exact lowPrime_6473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6473) (q := 6481) (by exact lowPrime_6481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6481) (q := 6491) (by exact lowPrime_6491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6491) (q := 6521) (by exact lowPrime_6521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6521) (q := 6529) (by exact lowPrime_6529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6529) (q := 6547) (by exact lowPrime_6547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part03_chain :
    DusartPrimeRowsChain 6449 6546 dusartPrimeRows_6311_6636_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6634, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6547) (q := 6551) (by exact lowPrime_6551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6551) (q := 6553) (by exact lowPrime_6553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6553) (q := 6563) (by exact lowPrime_6563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6563) (q := 6569) (by exact lowPrime_6569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6569) (q := 6571) (by exact lowPrime_6571) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6571) (q := 6577) (by exact lowPrime_6577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6577) (q := 6581) (by exact lowPrime_6581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6581) (q := 6599) (by exact lowPrime_6599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part04_chain :
    DusartPrimeRowsChain 6547 6598 dusartPrimeRows_6311_6636_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6634, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6599) (q := 6607) (by exact lowPrime_6607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6607) (q := 6619) (by exact lowPrime_6619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6619) (q := 6637) (by exact lowPrime_6637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part05_chain :
    DusartPrimeRowsChain 6599 6636 dusartPrimeRows_6311_6636_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · apply DusartPrimeRowsChain.empty
        norm_num [dusartPrimeRow_of_explicit_6634, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6637) (q := 6653) (by exact lowPrime_6653) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6653) (q := 6659) (by exact lowPrime_6659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6659) (q := 6661) (by exact lowPrime_6661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6661) (q := 6673) (by exact lowPrime_6673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6673) (q := 6679) (by exact lowPrime_6679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6679) (q := 6689) (by exact lowPrime_6689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6689) (q := 6691) (by exact lowPrime_6691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6691) (q := 6701) (by exact lowPrime_6701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part01_chain :
    DusartPrimeRowsChain 6637 6700 dusartPrimeRows_6637_6976_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6974, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6701) (q := 6703) (by exact lowPrime_6703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6703) (q := 6709) (by exact lowPrime_6709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6709) (q := 6719) (by exact lowPrime_6719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6719) (q := 6733) (by exact lowPrime_6733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6733) (q := 6737) (by exact lowPrime_6737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6737) (q := 6761) (by exact lowPrime_6761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6761) (q := 6763) (by exact lowPrime_6763) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6763) (q := 6779) (by exact lowPrime_6779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part02_chain :
    DusartPrimeRowsChain 6701 6778 dusartPrimeRows_6637_6976_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6974, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6779) (q := 6781) (by exact lowPrime_6781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6781) (q := 6791) (by exact lowPrime_6791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6791) (q := 6793) (by exact lowPrime_6793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6793) (q := 6803) (by exact lowPrime_6803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6803) (q := 6823) (by exact lowPrime_6823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6823) (q := 6827) (by exact lowPrime_6827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6827) (q := 6829) (by exact lowPrime_6829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6829) (q := 6833) (by exact lowPrime_6833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part03_chain :
    DusartPrimeRowsChain 6779 6832 dusartPrimeRows_6637_6976_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6974, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6833) (q := 6841) (by exact lowPrime_6841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6841) (q := 6857) (by exact lowPrime_6857) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6857) (q := 6863) (by exact lowPrime_6863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6863) (q := 6869) (by exact lowPrime_6869) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6869) (q := 6871) (by exact lowPrime_6871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6871) (q := 6883) (by exact lowPrime_6883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6883) (q := 6899) (by exact lowPrime_6899) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6899) (q := 6907) (by exact lowPrime_6907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part04_chain :
    DusartPrimeRowsChain 6833 6906 dusartPrimeRows_6637_6976_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6974, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6907) (q := 6911) (by exact lowPrime_6911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6911) (q := 6917) (by exact lowPrime_6917) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6917) (q := 6947) (by exact lowPrime_6947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6947) (q := 6949) (by exact lowPrime_6949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6949) (q := 6959) (by exact lowPrime_6959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6959) (q := 6961) (by exact lowPrime_6961) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6961) (q := 6967) (by exact lowPrime_6967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6967) (q := 6971) (by exact lowPrime_6971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part05_chain :
    DusartPrimeRowsChain 6907 6970 dusartPrimeRows_6637_6976_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6974, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6971) (q := 6977) (by exact lowPrime_6977) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part06_chain :
    DusartPrimeRowsChain 6971 6976 dusartPrimeRows_6637_6976_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_6974, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 6977) (q := 6983) (by exact lowPrime_6983) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6983) (q := 6991) (by exact lowPrime_6991) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6991) (q := 6997) (by exact lowPrime_6997) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6997) (q := 7001) (by exact lowPrime_7001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7001) (q := 7013) (by exact lowPrime_7013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7013) (q := 7019) (by exact lowPrime_7019) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7019) (q := 7027) (by exact lowPrime_7027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7027) (q := 7039) (by exact lowPrime_7039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part01_chain :
    DusartPrimeRowsChain 6977 7038 dusartPrimeRows_6977_7332_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_7331, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7039) (q := 7043) (by exact lowPrime_7043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7043) (q := 7057) (by exact lowPrime_7057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7057) (q := 7069) (by exact lowPrime_7069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7069) (q := 7079) (by exact lowPrime_7079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7079) (q := 7103) (by exact lowPrime_7103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7103) (q := 7109) (by exact lowPrime_7109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7109) (q := 7121) (by exact lowPrime_7121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7121) (q := 7127) (by exact lowPrime_7127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part02_chain :
    DusartPrimeRowsChain 7039 7126 dusartPrimeRows_6977_7332_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_7331, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7127) (q := 7129) (by exact lowPrime_7129) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7129) (q := 7151) (by exact lowPrime_7151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7151) (q := 7159) (by exact lowPrime_7159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7159) (q := 7177) (by exact lowPrime_7177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7177) (q := 7187) (by exact lowPrime_7187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7187) (q := 7193) (by exact lowPrime_7193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7193) (q := 7207) (by exact lowPrime_7207) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7207) (q := 7211) (by exact lowPrime_7211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part03_chain :
    DusartPrimeRowsChain 7127 7210 dusartPrimeRows_6977_7332_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_7331, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7211) (q := 7213) (by exact lowPrime_7213) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7213) (q := 7219) (by exact lowPrime_7219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7219) (q := 7229) (by exact lowPrime_7229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7229) (q := 7237) (by exact lowPrime_7237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7237) (q := 7243) (by exact lowPrime_7243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7243) (q := 7247) (by exact lowPrime_7247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7247) (q := 7253) (by exact lowPrime_7253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7253) (q := 7283) (by exact lowPrime_7283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part04_chain :
    DusartPrimeRowsChain 7211 7282 dusartPrimeRows_6977_7332_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_7331, dusartPrimeRow_of_explicit_right]
