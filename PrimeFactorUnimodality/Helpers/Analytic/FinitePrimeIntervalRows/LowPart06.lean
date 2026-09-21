import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart05


set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 06 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData06 : List PocklingtonData := [
    { n := 7297, F := 7296, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 2, 3, 19], residues := [(2, 3648), (3, 6118), (19, 462)] },
    { n := 7307, F := 7306, R := 1, a := 2, factors := [2, 13, 281], residues := [(2, 3653), (13, 1176), (281, 2960)] },
    { n := 7309, F := 7308, R := 1, a := 6, factors := [2, 2, 3, 3, 7, 29], residues := [(2, 3654), (3, 1297), (7, 3846), (29, 5445)] },
    { n := 7321, F := 7320, R := 1, a := 7, factors := [2, 2, 2, 3, 5, 61], residues := [(2, 3660), (3, 2337), (5, 3995), (61, 853)] },
    { n := 7331, F := 7330, R := 1, a := 2, factors := [2, 5, 733], residues := [(2, 3665), (5, 5638), (733, 2458)] },
    { n := 7333, F := 7332, R := 1, a := 6, factors := [2, 2, 3, 13, 47], residues := [(2, 3666), (3, 5909), (13, 2053), (47, 5179)] },
    { n := 7349, F := 7348, R := 1, a := 2, factors := [2, 2, 11, 167], residues := [(2, 3674), (11, 4401), (167, 4288)] },
    { n := 7351, F := 7350, R := 1, a := 6, factors := [2, 3, 5, 5, 7, 7], residues := [(2, 3675), (3, 7301), (5, 1681), (7, 562)] },
    { n := 7369, F := 7368, R := 1, a := 7, factors := [2, 2, 2, 3, 307], residues := [(2, 3684), (3, 3309), (307, 4219)] },
    { n := 7393, F := 7392, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 3, 7, 11], residues := [(2, 3696), (3, 6820), (7, 4639), (11, 1531)] },
    { n := 7411, F := 7410, R := 1, a := 2, factors := [2, 3, 5, 13, 19], residues := [(2, 3705), (3, 7279), (5, 6680), (13, 6714), (19, 6930)] },
    { n := 7417, F := 7416, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 103], residues := [(2, 3708), (3, 1701), (103, 6171)] },
    { n := 7433, F := 7432, R := 1, a := 3, factors := [2, 2, 2, 929], residues := [(2, 3716), (929, 298)] },
    { n := 7451, F := 7450, R := 1, a := 2, factors := [2, 5, 5, 149], residues := [(2, 3725), (5, 7046), (149, 1670)] },
    { n := 7457, F := 7456, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 233], residues := [(2, 3728), (233, 4858)] },
    { n := 7459, F := 7458, R := 1, a := 2, factors := [2, 3, 11, 113], residues := [(2, 3729), (3, 2562), (11, 4094), (113, 5218)] },
    { n := 7477, F := 7476, R := 1, a := 2, factors := [2, 2, 3, 7, 89], residues := [(2, 3738), (3, 3828), (7, 4413), (89, 2010)] },
    { n := 7481, F := 7480, R := 1, a := 6, factors := [2, 2, 2, 5, 11, 17], residues := [(2, 3740), (5, 1350), (11, 1129), (17, 2799)] },
    { n := 7487, F := 7486, R := 1, a := 5, factors := [2, 19, 197], residues := [(2, 3743), (19, 794), (197, 2258)] },
    { n := 7489, F := 7488, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 3, 3, 13], residues := [(2, 3744), (3, 822), (13, 7432)] },
    { n := 7499, F := 7498, R := 1, a := 2, factors := [2, 23, 163], residues := [(2, 3749), (23, 1804), (163, 646)] },
    { n := 7507, F := 7506, R := 1, a := 2, factors := [2, 3, 3, 3, 139], residues := [(2, 3753), (3, 4802), (139, 6606)] },
    { n := 7517, F := 7516, R := 1, a := 2, factors := [2, 2, 1879], residues := [(2, 3758), (1879, 3508)] },
    { n := 7523, F := 7522, R := 1, a := 2, factors := [2, 3761], residues := [(2, 3761), (3761, 2508)] },
    { n := 7529, F := 7528, R := 1, a := 3, factors := [2, 2, 2, 941], residues := [(2, 3764), (941, 2836)] },
    { n := 7537, F := 7536, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 157], residues := [(2, 3768), (3, 4370), (157, 4862)] },
    { n := 7541, F := 7540, R := 1, a := 2, factors := [2, 2, 5, 13, 29], residues := [(2, 3770), (5, 5508), (13, 227), (29, 6838)] },
    { n := 7547, F := 7546, R := 1, a := 2, factors := [2, 7, 7, 7, 11], residues := [(2, 3773), (7, 7341), (11, 5352)] },
    { n := 7549, F := 7548, R := 1, a := 2, factors := [2, 2, 3, 17, 37], residues := [(2, 3774), (3, 4856), (17, 2349), (37, 580)] },
    { n := 7559, F := 7558, R := 1, a := 13, factors := [2, 3779], residues := [(2, 3779), (3779, 45)] },
    { n := 7561, F := 7560, R := 1, a := 13, factors := [2, 2, 2, 3, 3, 3, 5, 7], residues := [(2, 3780), (3, 2087), (5, 278), (7, 3561)] },
    { n := 7573, F := 7572, R := 1, a := 2, factors := [2, 2, 3, 631], residues := [(2, 3786), (3, 5734), (631, 5646)] },
    { n := 7577, F := 7576, R := 1, a := 3, factors := [2, 2, 2, 947], residues := [(2, 3788), (947, 4351)] },
    { n := 7583, F := 7582, R := 1, a := 5, factors := [2, 17, 223], residues := [(2, 3791), (17, 1199), (223, 2873)] },
    { n := 7589, F := 7588, R := 1, a := 2, factors := [2, 2, 7, 271], residues := [(2, 3794), (7, 4982), (271, 964)] },
    { n := 7591, F := 7590, R := 1, a := 6, factors := [2, 3, 5, 11, 23], residues := [(2, 3795), (3, 5878), (5, 6259), (11, 5417), (23, 1949)] },
    { n := 7603, F := 7602, R := 1, a := 2, factors := [2, 3, 7, 181], residues := [(2, 3801), (3, 3232), (7, 2473), (181, 255)] },
    { n := 7607, F := 7606, R := 1, a := 5, factors := [2, 3803], residues := [(2, 3803), (3803, 317)] },
    { n := 7621, F := 7620, R := 1, a := 2, factors := [2, 2, 3, 5, 127], residues := [(2, 3810), (3, 6579), (5, 3611), (127, 597)] },
    { n := 7639, F := 7638, R := 1, a := 7, factors := [2, 3, 19, 67], residues := [(2, 3819), (3, 1554), (19, 6711), (67, 7484)] },
    { n := 7643, F := 7642, R := 1, a := 2, factors := [2, 3821], residues := [(2, 3821), (3821, 2548)] },
    { n := 7649, F := 7648, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 239], residues := [(2, 3824), (239, 7552)] },
    { n := 7669, F := 7668, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 71], residues := [(2, 3834), (3, 3246), (71, 1530)] },
    { n := 7673, F := 7672, R := 1, a := 3, factors := [2, 2, 2, 7, 137], residues := [(2, 3836), (7, 195), (137, 2222)] },
    { n := 7681, F := 7680, R := 1, a := 17, factors := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5], residues := [(2, 3840), (3, 4892), (5, 288)] },
    { n := 7687, F := 7686, R := 1, a := 6, factors := [2, 3, 3, 7, 61], residues := [(2, 3843), (3, 4366), (7, 27), (61, 1642)] },
    { n := 7691, F := 7690, R := 1, a := 2, factors := [2, 5, 769], residues := [(2, 3845), (5, 7630), (769, 7067)] },
    { n := 7699, F := 7698, R := 1, a := 3, factors := [2, 3, 1283], residues := [(2, 3849), (3, 6942), (1283, 6229)] },
    { n := 7703, F := 7702, R := 1, a := 5, factors := [2, 3851], residues := [(2, 3851), (3851, 321)] },
    { n := 7717, F := 7716, R := 1, a := 2, factors := [2, 2, 3, 643], residues := [(2, 3858), (3, 1146), (643, 1191)] },
    { n := 7723, F := 7722, R := 1, a := 3, factors := [2, 3, 3, 3, 11, 13], residues := [(2, 3861), (3, 2268), (11, 5436), (13, 2495)] },
    { n := 7727, F := 7726, R := 1, a := 5, factors := [2, 3863], residues := [(2, 3863), (3863, 322)] },
    { n := 7741, F := 7740, R := 1, a := 7, factors := [2, 2, 3, 3, 5, 43], residues := [(2, 3870), (3, 6923), (5, 6692), (43, 6190)] },
    { n := 7753, F := 7752, R := 1, a := 10, factors := [2, 2, 2, 3, 17, 19], residues := [(2, 3876), (3, 134), (17, 6588), (19, 276)] },
    { n := 7757, F := 7756, R := 1, a := 2, factors := [2, 2, 7, 277], residues := [(2, 3878), (7, 3715), (277, 6780)] },
    { n := 7759, F := 7758, R := 1, a := 3, factors := [2, 3, 3, 431], residues := [(2, 3879), (3, 586), (431, 976)] },
    { n := 7789, F := 7788, R := 1, a := 2, factors := [2, 2, 3, 11, 59], residues := [(2, 3894), (3, 2518), (11, 5304), (59, 5307)] },
    { n := 7793, F := 7792, R := 1, a := 3, factors := [2, 2, 2, 2, 487], residues := [(2, 3896), (487, 1673)] },
    { n := 7817, F := 7816, R := 1, a := 3, factors := [2, 2, 2, 977], residues := [(2, 3908), (977, 199)] },
    { n := 7823, F := 7822, R := 1, a := 5, factors := [2, 3911], residues := [(2, 3911), (3911, 326)] },
    { n := 7829, F := 7828, R := 1, a := 2, factors := [2, 2, 19, 103], residues := [(2, 3914), (19, 6811), (103, 2733)] },
    { n := 7841, F := 7840, R := 1, a := 12, factors := [2, 2, 2, 2, 2, 5, 7, 7], residues := [(2, 3920), (5, 1195), (7, 2473)] },
    { n := 7853, F := 7852, R := 1, a := 2, factors := [2, 2, 13, 151], residues := [(2, 3926), (13, 5013), (151, 5732)] },
    { n := 7867, F := 7866, R := 1, a := 3, factors := [2, 3, 3, 19, 23], residues := [(2, 3933), (3, 7378), (19, 6739), (23, 5227)] },
    { n := 7873, F := 7872, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 3, 41], residues := [(2, 3936), (3, 5713), (41, 4507)] },
    { n := 7877, F := 7876, R := 1, a := 2, factors := [2, 2, 11, 179], residues := [(2, 3938), (11, 4769), (179, 5211)] },
    { n := 7879, F := 7878, R := 1, a := 3, factors := [2, 3, 13, 101], residues := [(2, 3939), (3, 7423), (13, 1076), (101, 4802)] },
    { n := 7883, F := 7882, R := 1, a := 2, factors := [2, 7, 563], residues := [(2, 3941), (7, 7597), (563, 6912)] },
    { n := 7901, F := 7900, R := 1, a := 2, factors := [2, 2, 5, 5, 79], residues := [(2, 3950), (5, 4943), (79, 92)] },
    { n := 7907, F := 7906, R := 1, a := 2, factors := [2, 59, 67], residues := [(2, 3953), (59, 3922), (67, 813)] },
    { n := 7919, F := 7918, R := 1, a := 7, factors := [2, 37, 107], residues := [(2, 3959), (37, 5934), (107, 3370)] },
    { n := 7927, F := 7926, R := 1, a := 3, factors := [2, 3, 1321], residues := [(2, 3963), (3, 3895), (1321, 98)] },
    { n := 7933, F := 7932, R := 1, a := 2, factors := [2, 2, 3, 661], residues := [(2, 3966), (3, 668), (661, 3735)] },
    { n := 7937, F := 7936, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 2, 31], residues := [(2, 3968), (31, 4154)] },
    { n := 7949, F := 7948, R := 1, a := 2, factors := [2, 2, 1987], residues := [(2, 3974), (1987, 530)] },
    { n := 7951, F := 7950, R := 1, a := 6, factors := [2, 3, 5, 5, 53], residues := [(2, 3975), (3, 2757), (5, 1845), (53, 54)] },
    { n := 7963, F := 7962, R := 1, a := 5, factors := [2, 3, 1327], residues := [(2, 3981), (3, 4767), (1327, 3085)] },
    { n := 7993, F := 7992, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 3, 37], residues := [(2, 3996), (3, 1081), (37, 6551)] },
    { n := 8009, F := 8008, R := 1, a := 3, factors := [2, 2, 2, 7, 11, 13], residues := [(2, 4004), (7, 6638), (11, 7070), (13, 5524)] },
    { n := 8011, F := 8010, R := 1, a := 14, factors := [2, 3, 3, 5, 89], residues := [(2, 4005), (3, 5370), (5, 1854), (89, 5977)] },
    { n := 8017, F := 8016, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 167], residues := [(2, 4008), (3, 6225), (167, 5098)] },
    { n := 8039, F := 8038, R := 1, a := 11, factors := [2, 4019], residues := [(2, 4019), (4019, 67)] },
    { n := 8053, F := 8052, R := 1, a := 2, factors := [2, 2, 3, 11, 61], residues := [(2, 4026), (3, 1518), (11, 1992), (61, 5193)] },
    { n := 8059, F := 8058, R := 1, a := 3, factors := [2, 3, 17, 79], residues := [(2, 4029), (3, 6294), (17, 254), (79, 4922)] },
    { n := 8069, F := 8068, R := 1, a := 2, factors := [2, 2, 2017], residues := [(2, 4034), (2017, 538)] },
    { n := 8081, F := 8080, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 101], residues := [(2, 4040), (5, 1879), (101, 4940)] },
    { n := 8087, F := 8086, R := 1, a := 5, factors := [2, 13, 311], residues := [(2, 4043), (13, 1618), (311, 2827)] },
    { n := 8089, F := 8088, R := 1, a := 17, factors := [2, 2, 2, 3, 337], residues := [(2, 4044), (3, 3167), (337, 2666)] },
    { n := 8093, F := 8092, R := 1, a := 2, factors := [2, 2, 7, 17, 17], residues := [(2, 4046), (7, 636), (17, 4863)] },
    { n := 8101, F := 8100, R := 1, a := 6, factors := [2, 2, 3, 3, 3, 3, 5, 5], residues := [(2, 4050), (3, 3439), (5, 2794)] },
    { n := 8111, F := 8110, R := 1, a := 11, factors := [2, 5, 811], residues := [(2, 4055), (5, 7491), (811, 3137)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData06_valid : PocklingtonRow.Valid lowPocklingtonData06 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime06 (i : Fin lowPocklingtonData06.length) :
    Nat.Prime (lowPocklingtonData06.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData06_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7283) (q := 7297) (by
      have hp := lowPocklingtonPrime06 ⟨0, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7297) (q := 7307) (by
      have hp := lowPocklingtonPrime06 ⟨1, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7307) (q := 7309) (by
      have hp := lowPocklingtonPrime06 ⟨2, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7309) (q := 7321) (by
      have hp := lowPocklingtonPrime06 ⟨3, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7321) (q := 7331) (by
      have hp := lowPocklingtonPrime06 ⟨4, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7331) (q := 7333) (by
      have hp := lowPocklingtonPrime06 ⟨5, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part05_chain :
    DusartPrimeRowsChain 7283 7332 dusartPrimeRows_6977_7332_part05 := by
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
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_7331, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7333) (q := 7349) (by
      have hp := lowPocklingtonPrime06 ⟨6, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7349) (q := 7351) (by
      have hp := lowPocklingtonPrime06 ⟨7, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7351) (q := 7369) (by
      have hp := lowPocklingtonPrime06 ⟨8, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7369) (q := 7393) (by
      have hp := lowPocklingtonPrime06 ⟨9, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7393) (q := 7411) (by
      have hp := lowPocklingtonPrime06 ⟨10, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7411) (q := 7417) (by
      have hp := lowPocklingtonPrime06 ⟨11, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7417) (q := 7433) (by
      have hp := lowPocklingtonPrime06 ⟨12, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7433) (q := 7451) (by
      have hp := lowPocklingtonPrime06 ⟨13, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part01_chain :
    DusartPrimeRowsChain 7333 7450 dusartPrimeRows_7333_7716_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7451) (q := 7457) (by
      have hp := lowPocklingtonPrime06 ⟨14, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7457) (q := 7459) (by
      have hp := lowPocklingtonPrime06 ⟨15, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7459) (q := 7477) (by
      have hp := lowPocklingtonPrime06 ⟨16, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7477) (q := 7481) (by
      have hp := lowPocklingtonPrime06 ⟨17, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7481) (q := 7487) (by
      have hp := lowPocklingtonPrime06 ⟨18, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7487) (q := 7489) (by
      have hp := lowPocklingtonPrime06 ⟨19, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7489) (q := 7499) (by
      have hp := lowPocklingtonPrime06 ⟨20, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7499) (q := 7507) (by
      have hp := lowPocklingtonPrime06 ⟨21, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part02_chain :
    DusartPrimeRowsChain 7451 7506 dusartPrimeRows_7333_7716_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7507) (q := 7517) (by
      have hp := lowPocklingtonPrime06 ⟨22, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7517) (q := 7523) (by
      have hp := lowPocklingtonPrime06 ⟨23, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7523) (q := 7529) (by
      have hp := lowPocklingtonPrime06 ⟨24, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7529) (q := 7537) (by
      have hp := lowPocklingtonPrime06 ⟨25, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7537) (q := 7541) (by
      have hp := lowPocklingtonPrime06 ⟨26, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7541) (q := 7547) (by
      have hp := lowPocklingtonPrime06 ⟨27, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7547) (q := 7549) (by
      have hp := lowPocklingtonPrime06 ⟨28, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7549) (q := 7559) (by
      have hp := lowPocklingtonPrime06 ⟨29, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part03_chain :
    DusartPrimeRowsChain 7507 7558 dusartPrimeRows_7333_7716_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7559) (q := 7561) (by
      have hp := lowPocklingtonPrime06 ⟨30, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7561) (q := 7573) (by
      have hp := lowPocklingtonPrime06 ⟨31, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7573) (q := 7577) (by
      have hp := lowPocklingtonPrime06 ⟨32, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7577) (q := 7583) (by
      have hp := lowPocklingtonPrime06 ⟨33, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7583) (q := 7589) (by
      have hp := lowPocklingtonPrime06 ⟨34, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7589) (q := 7591) (by
      have hp := lowPocklingtonPrime06 ⟨35, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7591) (q := 7603) (by
      have hp := lowPocklingtonPrime06 ⟨36, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7603) (q := 7607) (by
      have hp := lowPocklingtonPrime06 ⟨37, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part04_chain :
    DusartPrimeRowsChain 7559 7606 dusartPrimeRows_7333_7716_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7607) (q := 7621) (by
      have hp := lowPocklingtonPrime06 ⟨38, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7621) (q := 7639) (by
      have hp := lowPocklingtonPrime06 ⟨39, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7639) (q := 7643) (by
      have hp := lowPocklingtonPrime06 ⟨40, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7643) (q := 7649) (by
      have hp := lowPocklingtonPrime06 ⟨41, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7649) (q := 7669) (by
      have hp := lowPocklingtonPrime06 ⟨42, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7669) (q := 7673) (by
      have hp := lowPocklingtonPrime06 ⟨43, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7673) (q := 7681) (by
      have hp := lowPocklingtonPrime06 ⟨44, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7681) (q := 7687) (by
      have hp := lowPocklingtonPrime06 ⟨45, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part05_chain :
    DusartPrimeRowsChain 7607 7686 dusartPrimeRows_7333_7716_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7687) (q := 7691) (by
      have hp := lowPocklingtonPrime06 ⟨46, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7691) (q := 7699) (by
      have hp := lowPocklingtonPrime06 ⟨47, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7699) (q := 7703) (by
      have hp := lowPocklingtonPrime06 ⟨48, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7703) (q := 7717) (by
      have hp := lowPocklingtonPrime06 ⟨49, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part06_chain :
    DusartPrimeRowsChain 7687 7716 dusartPrimeRows_7333_7716_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · apply DusartPrimeRowsChain.empty
          norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7717) (q := 7723) (by
      have hp := lowPocklingtonPrime06 ⟨50, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7723) (q := 7727) (by
      have hp := lowPocklingtonPrime06 ⟨51, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7727) (q := 7741) (by
      have hp := lowPocklingtonPrime06 ⟨52, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7741) (q := 7753) (by
      have hp := lowPocklingtonPrime06 ⟨53, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7753) (q := 7757) (by
      have hp := lowPocklingtonPrime06 ⟨54, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7757) (q := 7759) (by
      have hp := lowPocklingtonPrime06 ⟨55, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7759) (q := 7789) (by
      have hp := lowPocklingtonPrime06 ⟨56, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7789) (q := 7793) (by
      have hp := lowPocklingtonPrime06 ⟨57, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part01_chain :
    DusartPrimeRowsChain 7717 7792 dusartPrimeRows_7717_8110_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7793) (q := 7817) (by
      have hp := lowPocklingtonPrime06 ⟨58, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7817) (q := 7823) (by
      have hp := lowPocklingtonPrime06 ⟨59, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7823) (q := 7829) (by
      have hp := lowPocklingtonPrime06 ⟨60, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7829) (q := 7841) (by
      have hp := lowPocklingtonPrime06 ⟨61, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7841) (q := 7853) (by
      have hp := lowPocklingtonPrime06 ⟨62, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7853) (q := 7867) (by
      have hp := lowPocklingtonPrime06 ⟨63, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7867) (q := 7873) (by
      have hp := lowPocklingtonPrime06 ⟨64, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7873) (q := 7877) (by
      have hp := lowPocklingtonPrime06 ⟨65, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part02_chain :
    DusartPrimeRowsChain 7793 7876 dusartPrimeRows_7717_8110_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7877) (q := 7879) (by
      have hp := lowPocklingtonPrime06 ⟨66, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7879) (q := 7883) (by
      have hp := lowPocklingtonPrime06 ⟨67, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7883) (q := 7901) (by
      have hp := lowPocklingtonPrime06 ⟨68, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7901) (q := 7907) (by
      have hp := lowPocklingtonPrime06 ⟨69, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7907) (q := 7919) (by
      have hp := lowPocklingtonPrime06 ⟨70, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7919) (q := 7927) (by
      have hp := lowPocklingtonPrime06 ⟨71, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7927) (q := 7933) (by
      have hp := lowPocklingtonPrime06 ⟨72, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7933) (q := 7937) (by
      have hp := lowPocklingtonPrime06 ⟨73, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part03_chain :
    DusartPrimeRowsChain 7877 7936 dusartPrimeRows_7717_8110_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 7937) (q := 7949) (by
      have hp := lowPocklingtonPrime06 ⟨74, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7949) (q := 7951) (by
      have hp := lowPocklingtonPrime06 ⟨75, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7951) (q := 7963) (by
      have hp := lowPocklingtonPrime06 ⟨76, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7963) (q := 7993) (by
      have hp := lowPocklingtonPrime06 ⟨77, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7993) (q := 8009) (by
      have hp := lowPocklingtonPrime06 ⟨78, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8009) (q := 8011) (by
      have hp := lowPocklingtonPrime06 ⟨79, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8011) (q := 8017) (by
      have hp := lowPocklingtonPrime06 ⟨80, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8017) (q := 8039) (by
      have hp := lowPocklingtonPrime06 ⟨81, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part04_chain :
    DusartPrimeRowsChain 7937 8038 dusartPrimeRows_7717_8110_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 8039) (q := 8053) (by
      have hp := lowPocklingtonPrime06 ⟨82, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8053) (q := 8059) (by
      have hp := lowPocklingtonPrime06 ⟨83, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8059) (q := 8069) (by
      have hp := lowPocklingtonPrime06 ⟨84, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8069) (q := 8081) (by
      have hp := lowPocklingtonPrime06 ⟨85, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8081) (q := 8087) (by
      have hp := lowPocklingtonPrime06 ⟨86, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8087) (q := 8089) (by
      have hp := lowPocklingtonPrime06 ⟨87, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8089) (q := 8093) (by
      have hp := lowPocklingtonPrime06 ⟨88, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8093) (q := 8101) (by
      have hp := lowPocklingtonPrime06 ⟨89, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part05_chain :
    DusartPrimeRowsChain 8039 8100 dusartPrimeRows_7717_8110_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · norm_num [dusartPrimeRow_of_explicit_8103]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · norm_num [dusartPrimeRow_of_explicit_8103]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · norm_num [dusartPrimeRow_of_explicit_8103]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · norm_num [dusartPrimeRow_of_explicit_8103]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · norm_num [dusartPrimeRow_of_explicit_8103]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · norm_num [dusartPrimeRow_of_explicit_8103]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · norm_num [dusartPrimeRow_of_explicit_8103]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 8101) (q := 8111) (by
      have hp := lowPocklingtonPrime06 ⟨90, by simp [lowPocklingtonData06]⟩
      simpa [lowPocklingtonData06] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part06_chain :
    DusartPrimeRowsChain 8101 8110 dusartPrimeRows_7717_8110_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]
