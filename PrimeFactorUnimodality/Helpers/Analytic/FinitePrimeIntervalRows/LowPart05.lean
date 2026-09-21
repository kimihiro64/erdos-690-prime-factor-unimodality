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

theorem lowPocklingtonPrime05 (i : Fin lowPocklingtonData05.length) :
    Nat.Prime (lowPocklingtonData05.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData05_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6449) (q := 6451) (by
      have hp := lowPocklingtonPrime05 ⟨0, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6451) (q := 6469) (by
      have hp := lowPocklingtonPrime05 ⟨1, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6469) (q := 6473) (by
      have hp := lowPocklingtonPrime05 ⟨2, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6473) (q := 6481) (by
      have hp := lowPocklingtonPrime05 ⟨3, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6481) (q := 6491) (by
      have hp := lowPocklingtonPrime05 ⟨4, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6491) (q := 6521) (by
      have hp := lowPocklingtonPrime05 ⟨5, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6521) (q := 6529) (by
      have hp := lowPocklingtonPrime05 ⟨6, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6529) (q := 6547) (by
      have hp := lowPocklingtonPrime05 ⟨7, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_6634 (p := 6547) (q := 6551) (by
      have hp := lowPocklingtonPrime05 ⟨8, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6551) (q := 6553) (by
      have hp := lowPocklingtonPrime05 ⟨9, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6553) (q := 6563) (by
      have hp := lowPocklingtonPrime05 ⟨10, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6563) (q := 6569) (by
      have hp := lowPocklingtonPrime05 ⟨11, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6569) (q := 6571) (by
      have hp := lowPocklingtonPrime05 ⟨12, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6571) (q := 6577) (by
      have hp := lowPocklingtonPrime05 ⟨13, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6577) (q := 6581) (by
      have hp := lowPocklingtonPrime05 ⟨14, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6581) (q := 6599) (by
      have hp := lowPocklingtonPrime05 ⟨15, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_6634 (p := 6599) (q := 6607) (by
      have hp := lowPocklingtonPrime05 ⟨16, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6607) (q := 6619) (by
      have hp := lowPocklingtonPrime05 ⟨17, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6619) (q := 6637) (by
      have hp := lowPocklingtonPrime05 ⟨18, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_6974 (p := 6637) (q := 6653) (by
      have hp := lowPocklingtonPrime05 ⟨19, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6653) (q := 6659) (by
      have hp := lowPocklingtonPrime05 ⟨20, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6659) (q := 6661) (by
      have hp := lowPocklingtonPrime05 ⟨21, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6661) (q := 6673) (by
      have hp := lowPocklingtonPrime05 ⟨22, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6673) (q := 6679) (by
      have hp := lowPocklingtonPrime05 ⟨23, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6679) (q := 6689) (by
      have hp := lowPocklingtonPrime05 ⟨24, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6689) (q := 6691) (by
      have hp := lowPocklingtonPrime05 ⟨25, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6691) (q := 6701) (by
      have hp := lowPocklingtonPrime05 ⟨26, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_6974 (p := 6701) (q := 6703) (by
      have hp := lowPocklingtonPrime05 ⟨27, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6703) (q := 6709) (by
      have hp := lowPocklingtonPrime05 ⟨28, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6709) (q := 6719) (by
      have hp := lowPocklingtonPrime05 ⟨29, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6719) (q := 6733) (by
      have hp := lowPocklingtonPrime05 ⟨30, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6733) (q := 6737) (by
      have hp := lowPocklingtonPrime05 ⟨31, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6737) (q := 6761) (by
      have hp := lowPocklingtonPrime05 ⟨32, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6761) (q := 6763) (by
      have hp := lowPocklingtonPrime05 ⟨33, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6763) (q := 6779) (by
      have hp := lowPocklingtonPrime05 ⟨34, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_6974 (p := 6779) (q := 6781) (by
      have hp := lowPocklingtonPrime05 ⟨35, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6781) (q := 6791) (by
      have hp := lowPocklingtonPrime05 ⟨36, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6791) (q := 6793) (by
      have hp := lowPocklingtonPrime05 ⟨37, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6793) (q := 6803) (by
      have hp := lowPocklingtonPrime05 ⟨38, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6803) (q := 6823) (by
      have hp := lowPocklingtonPrime05 ⟨39, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6823) (q := 6827) (by
      have hp := lowPocklingtonPrime05 ⟨40, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6827) (q := 6829) (by
      have hp := lowPocklingtonPrime05 ⟨41, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6829) (q := 6833) (by
      have hp := lowPocklingtonPrime05 ⟨42, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_6974 (p := 6833) (q := 6841) (by
      have hp := lowPocklingtonPrime05 ⟨43, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6841) (q := 6857) (by
      have hp := lowPocklingtonPrime05 ⟨44, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6857) (q := 6863) (by
      have hp := lowPocklingtonPrime05 ⟨45, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6863) (q := 6869) (by
      have hp := lowPocklingtonPrime05 ⟨46, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6869) (q := 6871) (by
      have hp := lowPocklingtonPrime05 ⟨47, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6871) (q := 6883) (by
      have hp := lowPocklingtonPrime05 ⟨48, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6883) (q := 6899) (by
      have hp := lowPocklingtonPrime05 ⟨49, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6899) (q := 6907) (by
      have hp := lowPocklingtonPrime05 ⟨50, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_6974 (p := 6907) (q := 6911) (by
      have hp := lowPocklingtonPrime05 ⟨51, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6911) (q := 6917) (by
      have hp := lowPocklingtonPrime05 ⟨52, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6917) (q := 6947) (by
      have hp := lowPocklingtonPrime05 ⟨53, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6947) (q := 6949) (by
      have hp := lowPocklingtonPrime05 ⟨54, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6949) (q := 6959) (by
      have hp := lowPocklingtonPrime05 ⟨55, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6959) (q := 6961) (by
      have hp := lowPocklingtonPrime05 ⟨56, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6961) (q := 6967) (by
      have hp := lowPocklingtonPrime05 ⟨57, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6967) (q := 6971) (by
      have hp := lowPocklingtonPrime05 ⟨58, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_6974 (p := 6971) (q := 6977) (by
      have hp := lowPocklingtonPrime05 ⟨59, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_7331 (p := 6977) (q := 6983) (by
      have hp := lowPocklingtonPrime05 ⟨60, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6983) (q := 6991) (by
      have hp := lowPocklingtonPrime05 ⟨61, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6991) (q := 6997) (by
      have hp := lowPocklingtonPrime05 ⟨62, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6997) (q := 7001) (by
      have hp := lowPocklingtonPrime05 ⟨63, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7001) (q := 7013) (by
      have hp := lowPocklingtonPrime05 ⟨64, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7013) (q := 7019) (by
      have hp := lowPocklingtonPrime05 ⟨65, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7019) (q := 7027) (by
      have hp := lowPocklingtonPrime05 ⟨66, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7027) (q := 7039) (by
      have hp := lowPocklingtonPrime05 ⟨67, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_7331 (p := 7039) (q := 7043) (by
      have hp := lowPocklingtonPrime05 ⟨68, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7043) (q := 7057) (by
      have hp := lowPocklingtonPrime05 ⟨69, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7057) (q := 7069) (by
      have hp := lowPocklingtonPrime05 ⟨70, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7069) (q := 7079) (by
      have hp := lowPocklingtonPrime05 ⟨71, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7079) (q := 7103) (by
      have hp := lowPocklingtonPrime05 ⟨72, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7103) (q := 7109) (by
      have hp := lowPocklingtonPrime05 ⟨73, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7109) (q := 7121) (by
      have hp := lowPocklingtonPrime05 ⟨74, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7121) (q := 7127) (by
      have hp := lowPocklingtonPrime05 ⟨75, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_7331 (p := 7127) (q := 7129) (by
      have hp := lowPocklingtonPrime05 ⟨76, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7129) (q := 7151) (by
      have hp := lowPocklingtonPrime05 ⟨77, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7151) (q := 7159) (by
      have hp := lowPocklingtonPrime05 ⟨78, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7159) (q := 7177) (by
      have hp := lowPocklingtonPrime05 ⟨79, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7177) (q := 7187) (by
      have hp := lowPocklingtonPrime05 ⟨80, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7187) (q := 7193) (by
      have hp := lowPocklingtonPrime05 ⟨81, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7193) (q := 7207) (by
      have hp := lowPocklingtonPrime05 ⟨82, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7207) (q := 7211) (by
      have hp := lowPocklingtonPrime05 ⟨83, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_7331 (p := 7211) (q := 7213) (by
      have hp := lowPocklingtonPrime05 ⟨84, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7213) (q := 7219) (by
      have hp := lowPocklingtonPrime05 ⟨85, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7219) (q := 7229) (by
      have hp := lowPocklingtonPrime05 ⟨86, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7229) (q := 7237) (by
      have hp := lowPocklingtonPrime05 ⟨87, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7237) (q := 7243) (by
      have hp := lowPocklingtonPrime05 ⟨88, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7243) (q := 7247) (by
      have hp := lowPocklingtonPrime05 ⟨89, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7247) (q := 7253) (by
      have hp := lowPocklingtonPrime05 ⟨90, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7253) (q := 7283) (by
      have hp := lowPocklingtonPrime05 ⟨91, by simp [lowPocklingtonData05]⟩
      simpa [lowPocklingtonData05] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
