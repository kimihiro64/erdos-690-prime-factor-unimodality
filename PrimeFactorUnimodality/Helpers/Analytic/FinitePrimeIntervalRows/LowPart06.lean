import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

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

theorem lowPrime_7297 : Nat.Prime 7297 := by
  let d := lowPocklingtonData06.get ⟨0, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7307 : Nat.Prime 7307 := by
  let d := lowPocklingtonData06.get ⟨1, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7309 : Nat.Prime 7309 := by
  let d := lowPocklingtonData06.get ⟨2, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7321 : Nat.Prime 7321 := by
  let d := lowPocklingtonData06.get ⟨3, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7331 : Nat.Prime 7331 := by
  let d := lowPocklingtonData06.get ⟨4, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7333 : Nat.Prime 7333 := by
  let d := lowPocklingtonData06.get ⟨5, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7349 : Nat.Prime 7349 := by
  let d := lowPocklingtonData06.get ⟨6, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7351 : Nat.Prime 7351 := by
  let d := lowPocklingtonData06.get ⟨7, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7369 : Nat.Prime 7369 := by
  let d := lowPocklingtonData06.get ⟨8, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7393 : Nat.Prime 7393 := by
  let d := lowPocklingtonData06.get ⟨9, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7411 : Nat.Prime 7411 := by
  let d := lowPocklingtonData06.get ⟨10, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7417 : Nat.Prime 7417 := by
  let d := lowPocklingtonData06.get ⟨11, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7433 : Nat.Prime 7433 := by
  let d := lowPocklingtonData06.get ⟨12, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7451 : Nat.Prime 7451 := by
  let d := lowPocklingtonData06.get ⟨13, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7457 : Nat.Prime 7457 := by
  let d := lowPocklingtonData06.get ⟨14, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7459 : Nat.Prime 7459 := by
  let d := lowPocklingtonData06.get ⟨15, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7477 : Nat.Prime 7477 := by
  let d := lowPocklingtonData06.get ⟨16, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7481 : Nat.Prime 7481 := by
  let d := lowPocklingtonData06.get ⟨17, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7487 : Nat.Prime 7487 := by
  let d := lowPocklingtonData06.get ⟨18, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7489 : Nat.Prime 7489 := by
  let d := lowPocklingtonData06.get ⟨19, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7499 : Nat.Prime 7499 := by
  let d := lowPocklingtonData06.get ⟨20, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7507 : Nat.Prime 7507 := by
  let d := lowPocklingtonData06.get ⟨21, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7517 : Nat.Prime 7517 := by
  let d := lowPocklingtonData06.get ⟨22, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7523 : Nat.Prime 7523 := by
  let d := lowPocklingtonData06.get ⟨23, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7529 : Nat.Prime 7529 := by
  let d := lowPocklingtonData06.get ⟨24, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7537 : Nat.Prime 7537 := by
  let d := lowPocklingtonData06.get ⟨25, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7541 : Nat.Prime 7541 := by
  let d := lowPocklingtonData06.get ⟨26, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7547 : Nat.Prime 7547 := by
  let d := lowPocklingtonData06.get ⟨27, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7549 : Nat.Prime 7549 := by
  let d := lowPocklingtonData06.get ⟨28, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7559 : Nat.Prime 7559 := by
  let d := lowPocklingtonData06.get ⟨29, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7561 : Nat.Prime 7561 := by
  let d := lowPocklingtonData06.get ⟨30, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7573 : Nat.Prime 7573 := by
  let d := lowPocklingtonData06.get ⟨31, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7577 : Nat.Prime 7577 := by
  let d := lowPocklingtonData06.get ⟨32, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7583 : Nat.Prime 7583 := by
  let d := lowPocklingtonData06.get ⟨33, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7589 : Nat.Prime 7589 := by
  let d := lowPocklingtonData06.get ⟨34, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7591 : Nat.Prime 7591 := by
  let d := lowPocklingtonData06.get ⟨35, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7603 : Nat.Prime 7603 := by
  let d := lowPocklingtonData06.get ⟨36, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7607 : Nat.Prime 7607 := by
  let d := lowPocklingtonData06.get ⟨37, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7621 : Nat.Prime 7621 := by
  let d := lowPocklingtonData06.get ⟨38, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7639 : Nat.Prime 7639 := by
  let d := lowPocklingtonData06.get ⟨39, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7643 : Nat.Prime 7643 := by
  let d := lowPocklingtonData06.get ⟨40, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7649 : Nat.Prime 7649 := by
  let d := lowPocklingtonData06.get ⟨41, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7669 : Nat.Prime 7669 := by
  let d := lowPocklingtonData06.get ⟨42, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7673 : Nat.Prime 7673 := by
  let d := lowPocklingtonData06.get ⟨43, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7681 : Nat.Prime 7681 := by
  let d := lowPocklingtonData06.get ⟨44, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7687 : Nat.Prime 7687 := by
  let d := lowPocklingtonData06.get ⟨45, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7691 : Nat.Prime 7691 := by
  let d := lowPocklingtonData06.get ⟨46, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7699 : Nat.Prime 7699 := by
  let d := lowPocklingtonData06.get ⟨47, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7703 : Nat.Prime 7703 := by
  let d := lowPocklingtonData06.get ⟨48, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7717 : Nat.Prime 7717 := by
  let d := lowPocklingtonData06.get ⟨49, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7723 : Nat.Prime 7723 := by
  let d := lowPocklingtonData06.get ⟨50, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7727 : Nat.Prime 7727 := by
  let d := lowPocklingtonData06.get ⟨51, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7741 : Nat.Prime 7741 := by
  let d := lowPocklingtonData06.get ⟨52, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7753 : Nat.Prime 7753 := by
  let d := lowPocklingtonData06.get ⟨53, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7757 : Nat.Prime 7757 := by
  let d := lowPocklingtonData06.get ⟨54, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7759 : Nat.Prime 7759 := by
  let d := lowPocklingtonData06.get ⟨55, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7789 : Nat.Prime 7789 := by
  let d := lowPocklingtonData06.get ⟨56, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7793 : Nat.Prime 7793 := by
  let d := lowPocklingtonData06.get ⟨57, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7817 : Nat.Prime 7817 := by
  let d := lowPocklingtonData06.get ⟨58, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7823 : Nat.Prime 7823 := by
  let d := lowPocklingtonData06.get ⟨59, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7829 : Nat.Prime 7829 := by
  let d := lowPocklingtonData06.get ⟨60, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7841 : Nat.Prime 7841 := by
  let d := lowPocklingtonData06.get ⟨61, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7853 : Nat.Prime 7853 := by
  let d := lowPocklingtonData06.get ⟨62, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7867 : Nat.Prime 7867 := by
  let d := lowPocklingtonData06.get ⟨63, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7873 : Nat.Prime 7873 := by
  let d := lowPocklingtonData06.get ⟨64, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7877 : Nat.Prime 7877 := by
  let d := lowPocklingtonData06.get ⟨65, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7879 : Nat.Prime 7879 := by
  let d := lowPocklingtonData06.get ⟨66, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7883 : Nat.Prime 7883 := by
  let d := lowPocklingtonData06.get ⟨67, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7901 : Nat.Prime 7901 := by
  let d := lowPocklingtonData06.get ⟨68, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7907 : Nat.Prime 7907 := by
  let d := lowPocklingtonData06.get ⟨69, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7919 : Nat.Prime 7919 := by
  let d := lowPocklingtonData06.get ⟨70, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7927 : Nat.Prime 7927 := by
  let d := lowPocklingtonData06.get ⟨71, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7933 : Nat.Prime 7933 := by
  let d := lowPocklingtonData06.get ⟨72, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7937 : Nat.Prime 7937 := by
  let d := lowPocklingtonData06.get ⟨73, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7949 : Nat.Prime 7949 := by
  let d := lowPocklingtonData06.get ⟨74, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7951 : Nat.Prime 7951 := by
  let d := lowPocklingtonData06.get ⟨75, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7963 : Nat.Prime 7963 := by
  let d := lowPocklingtonData06.get ⟨76, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_7993 : Nat.Prime 7993 := by
  let d := lowPocklingtonData06.get ⟨77, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8009 : Nat.Prime 8009 := by
  let d := lowPocklingtonData06.get ⟨78, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8011 : Nat.Prime 8011 := by
  let d := lowPocklingtonData06.get ⟨79, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8017 : Nat.Prime 8017 := by
  let d := lowPocklingtonData06.get ⟨80, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8039 : Nat.Prime 8039 := by
  let d := lowPocklingtonData06.get ⟨81, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8053 : Nat.Prime 8053 := by
  let d := lowPocklingtonData06.get ⟨82, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8059 : Nat.Prime 8059 := by
  let d := lowPocklingtonData06.get ⟨83, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8069 : Nat.Prime 8069 := by
  let d := lowPocklingtonData06.get ⟨84, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8081 : Nat.Prime 8081 := by
  let d := lowPocklingtonData06.get ⟨85, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8087 : Nat.Prime 8087 := by
  let d := lowPocklingtonData06.get ⟨86, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8089 : Nat.Prime 8089 := by
  let d := lowPocklingtonData06.get ⟨87, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8093 : Nat.Prime 8093 := by
  let d := lowPocklingtonData06.get ⟨88, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8101 : Nat.Prime 8101 := by
  let d := lowPocklingtonData06.get ⟨89, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp

theorem lowPrime_8111 : Nat.Prime 8111 := by
  let d := lowPocklingtonData06.get ⟨90, by simp [lowPocklingtonData06]⟩
  have hd : d ∈ lowPocklingtonData06 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData06_valid hd
  simpa [d, lowPocklingtonData06] using hp
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7283) (q := 7297) (by exact lowPrime_7297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7297) (q := 7307) (by exact lowPrime_7307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7307) (q := 7309) (by exact lowPrime_7309) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7309) (q := 7321) (by exact lowPrime_7321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7321) (q := 7331) (by exact lowPrime_7331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7331) (q := 7333) (by exact lowPrime_7333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_7707 (p := 7333) (q := 7349) (by exact lowPrime_7349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7349) (q := 7351) (by exact lowPrime_7351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7351) (q := 7369) (by exact lowPrime_7369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7369) (q := 7393) (by exact lowPrime_7393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7393) (q := 7411) (by exact lowPrime_7411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7411) (q := 7417) (by exact lowPrime_7417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7417) (q := 7433) (by exact lowPrime_7433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7433) (q := 7451) (by exact lowPrime_7451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_7707 (p := 7451) (q := 7457) (by exact lowPrime_7457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7457) (q := 7459) (by exact lowPrime_7459) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7459) (q := 7477) (by exact lowPrime_7477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7477) (q := 7481) (by exact lowPrime_7481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7481) (q := 7487) (by exact lowPrime_7487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7487) (q := 7489) (by exact lowPrime_7489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7489) (q := 7499) (by exact lowPrime_7499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7499) (q := 7507) (by exact lowPrime_7507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_7707 (p := 7507) (q := 7517) (by exact lowPrime_7517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7517) (q := 7523) (by exact lowPrime_7523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7523) (q := 7529) (by exact lowPrime_7529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7529) (q := 7537) (by exact lowPrime_7537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7537) (q := 7541) (by exact lowPrime_7541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7541) (q := 7547) (by exact lowPrime_7547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7547) (q := 7549) (by exact lowPrime_7549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7549) (q := 7559) (by exact lowPrime_7559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_7707 (p := 7559) (q := 7561) (by exact lowPrime_7561) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7561) (q := 7573) (by exact lowPrime_7573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7573) (q := 7577) (by exact lowPrime_7577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7577) (q := 7583) (by exact lowPrime_7583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7583) (q := 7589) (by exact lowPrime_7589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7589) (q := 7591) (by exact lowPrime_7591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7591) (q := 7603) (by exact lowPrime_7603) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7603) (q := 7607) (by exact lowPrime_7607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_7707 (p := 7607) (q := 7621) (by exact lowPrime_7621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7621) (q := 7639) (by exact lowPrime_7639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7639) (q := 7643) (by exact lowPrime_7643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7643) (q := 7649) (by exact lowPrime_7649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7649) (q := 7669) (by exact lowPrime_7669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7669) (q := 7673) (by exact lowPrime_7673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7673) (q := 7681) (by exact lowPrime_7681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7681) (q := 7687) (by exact lowPrime_7687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_7707 (p := 7687) (q := 7691) (by exact lowPrime_7691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7691) (q := 7699) (by exact lowPrime_7699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7699) (q := 7703) (by exact lowPrime_7703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7703) (q := 7717) (by exact lowPrime_7717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8103 (p := 7717) (q := 7723) (by exact lowPrime_7723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7723) (q := 7727) (by exact lowPrime_7727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7727) (q := 7741) (by exact lowPrime_7741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7741) (q := 7753) (by exact lowPrime_7753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7753) (q := 7757) (by exact lowPrime_7757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7757) (q := 7759) (by exact lowPrime_7759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7759) (q := 7789) (by exact lowPrime_7789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7789) (q := 7793) (by exact lowPrime_7793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8103 (p := 7793) (q := 7817) (by exact lowPrime_7817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7817) (q := 7823) (by exact lowPrime_7823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7823) (q := 7829) (by exact lowPrime_7829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7829) (q := 7841) (by exact lowPrime_7841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7841) (q := 7853) (by exact lowPrime_7853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7853) (q := 7867) (by exact lowPrime_7867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7867) (q := 7873) (by exact lowPrime_7873) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7873) (q := 7877) (by exact lowPrime_7877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8103 (p := 7877) (q := 7879) (by exact lowPrime_7879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7879) (q := 7883) (by exact lowPrime_7883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7883) (q := 7901) (by exact lowPrime_7901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7901) (q := 7907) (by exact lowPrime_7907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7907) (q := 7919) (by exact lowPrime_7919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7919) (q := 7927) (by exact lowPrime_7927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7927) (q := 7933) (by exact lowPrime_7933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7933) (q := 7937) (by exact lowPrime_7937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8103 (p := 7937) (q := 7949) (by exact lowPrime_7949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7949) (q := 7951) (by exact lowPrime_7951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7951) (q := 7963) (by exact lowPrime_7963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7963) (q := 7993) (by exact lowPrime_7993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 7993) (q := 8009) (by exact lowPrime_8009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8009) (q := 8011) (by exact lowPrime_8011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8011) (q := 8017) (by exact lowPrime_8017) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8017) (q := 8039) (by exact lowPrime_8039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8103 (p := 8039) (q := 8053) (by exact lowPrime_8053) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8053) (q := 8059) (by exact lowPrime_8059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8059) (q := 8069) (by exact lowPrime_8069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8069) (q := 8081) (by exact lowPrime_8081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8081) (q := 8087) (by exact lowPrime_8087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8087) (q := 8089) (by exact lowPrime_8089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8089) (q := 8093) (by exact lowPrime_8093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8103 (p := 8093) (q := 8101) (by exact lowPrime_8101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_8103 (p := 8101) (q := 8111) (by exact lowPrime_8111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part06_chain :
    DusartPrimeRowsChain 8101 8110 dusartPrimeRows_7717_8110_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]
