import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 14 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData14 : List PocklingtonData := [
    { n := 14153, F := 14152, R := 1, a := 3, factors := [2, 2, 2, 29, 61], residues := [(2, 7076), (29, 2649), (61, 4356)] },
    { n := 14159, F := 14158, R := 1, a := 13, factors := [2, 7079], residues := [(2, 7079), (7079, 2107)] },
    { n := 14173, F := 14172, R := 1, a := 2, factors := [2, 2, 3, 1181], residues := [(2, 7086), (3, 8277), (1181, 5998)] },
    { n := 14177, F := 14176, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 443], residues := [(2, 7088), (443, 12653)] },
    { n := 14197, F := 14196, R := 1, a := 11, factors := [2, 2, 3, 7, 13, 13], residues := [(2, 7098), (3, 3024), (7, 9977), (13, 2297)] },
    { n := 14207, F := 14206, R := 1, a := 5, factors := [2, 7103], residues := [(2, 7103), (7103, 592)] },
    { n := 14221, F := 14220, R := 1, a := 2, factors := [2, 2, 3, 3, 5, 79], residues := [(2, 7110), (3, 6355), (5, 7151), (79, 8558)] },
    { n := 14243, F := 14242, R := 1, a := 2, factors := [2, 7121], residues := [(2, 7121), (7121, 4748)] },
    { n := 14249, F := 14248, R := 1, a := 3, factors := [2, 2, 2, 13, 137], residues := [(2, 7124), (13, 11654), (137, 8319)] },
    { n := 14251, F := 14250, R := 1, a := 3, factors := [2, 3, 5, 5, 5, 19], residues := [(2, 7125), (3, 2800), (5, 8142), (19, 4205)] },
    { n := 14281, F := 14280, R := 1, a := 19, factors := [2, 2, 2, 3, 5, 7, 17], residues := [(2, 7140), (3, 9560), (5, 7194), (7, 9439), (17, 11150)] },
    { n := 14293, F := 14292, R := 1, a := 6, factors := [2, 2, 3, 3, 397], residues := [(2, 7146), (3, 13679), (397, 1679)] },
    { n := 14303, F := 14302, R := 1, a := 5, factors := [2, 7151], residues := [(2, 7151), (7151, 596)] },
    { n := 14321, F := 14320, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 179], residues := [(2, 7160), (5, 13722), (179, 9776)] },
    { n := 14323, F := 14322, R := 1, a := 5, factors := [2, 3, 7, 11, 31], residues := [(2, 7161), (3, 12779), (7, 10494), (11, 2467), (31, 2051)] },
    { n := 14327, F := 14326, R := 1, a := 5, factors := [2, 13, 19, 29], residues := [(2, 7163), (13, 11573), (19, 7610), (29, 6669)] },
    { n := 14341, F := 14340, R := 1, a := 2, factors := [2, 2, 3, 5, 239], residues := [(2, 7170), (3, 7440), (5, 4814), (239, 8442)] },
    { n := 14347, F := 14346, R := 1, a := 3, factors := [2, 3, 3, 797], residues := [(2, 7173), (3, 8074), (797, 445)] },
    { n := 14369, F := 14368, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 449], residues := [(2, 7184), (449, 11784)] },
    { n := 14387, F := 14386, R := 1, a := 2, factors := [2, 7193], residues := [(2, 7193), (7193, 4796)] },
    { n := 14389, F := 14388, R := 1, a := 2, factors := [2, 2, 3, 11, 109], residues := [(2, 7194), (3, 4940), (11, 10589), (109, 11347)] },
    { n := 14401, F := 14400, R := 1, a := 11, factors := [2, 2, 2, 2, 2, 2, 3, 3, 5, 5], residues := [(2, 7200), (3, 4694), (5, 1139)] },
    { n := 14407, F := 14406, R := 1, a := 19, factors := [2, 3, 7, 7, 7, 7], residues := [(2, 7203), (3, 5907), (7, 8040)] },
    { n := 14411, F := 14410, R := 1, a := 2, factors := [2, 5, 11, 131], residues := [(2, 7205), (5, 10844), (11, 5190), (131, 7605)] },
    { n := 14419, F := 14418, R := 1, a := 2, factors := [2, 3, 3, 3, 3, 89], residues := [(2, 7209), (3, 7402), (89, 12556)] },
    { n := 14423, F := 14422, R := 1, a := 5, factors := [2, 7211], residues := [(2, 7211), (7211, 601)] },
    { n := 14431, F := 14430, R := 1, a := 3, factors := [2, 3, 5, 13, 37], residues := [(2, 7215), (3, 183), (5, 8290), (13, 8085), (37, 8644)] },
    { n := 14437, F := 14436, R := 1, a := 5, factors := [2, 2, 3, 3, 401], residues := [(2, 7218), (3, 11119), (401, 5437)] },
    { n := 14447, F := 14446, R := 1, a := 5, factors := [2, 31, 233], residues := [(2, 7223), (31, 715), (233, 14202)] },
    { n := 14449, F := 14448, R := 1, a := 22, factors := [2, 2, 2, 2, 3, 7, 43], residues := [(2, 7224), (3, 10277), (7, 5335), (43, 2888)] },
    { n := 14461, F := 14460, R := 1, a := 2, factors := [2, 2, 3, 5, 241], residues := [(2, 7230), (3, 6987), (5, 1223), (241, 985)] },
    { n := 14479, F := 14478, R := 1, a := 3, factors := [2, 3, 19, 127], residues := [(2, 7239), (3, 9827), (19, 4435), (127, 8358)] },
    { n := 14489, F := 14488, R := 1, a := 3, factors := [2, 2, 2, 1811], residues := [(2, 7244), (1811, 11642)] },
    { n := 14503, F := 14502, R := 1, a := 3, factors := [2, 3, 2417], residues := [(2, 7251), (3, 8277), (2417, 5598)] },
    { n := 14519, F := 14518, R := 1, a := 13, factors := [2, 7, 17, 61], residues := [(2, 7259), (7, 4315), (17, 7766), (61, 5722)] },
    { n := 14533, F := 14532, R := 1, a := 2, factors := [2, 2, 3, 7, 173], residues := [(2, 7266), (3, 12302), (7, 9414), (173, 10065)] },
    { n := 14537, F := 14536, R := 1, a := 3, factors := [2, 2, 2, 23, 79], residues := [(2, 7268), (23, 4092), (79, 2603)] },
    { n := 14543, F := 14542, R := 1, a := 5, factors := [2, 11, 661], residues := [(2, 7271), (11, 527), (661, 9003)] },
    { n := 14549, F := 14548, R := 1, a := 2, factors := [2, 2, 3637], residues := [(2, 7274), (3637, 970)] },
    { n := 14551, F := 14550, R := 1, a := 3, factors := [2, 3, 5, 5, 97], residues := [(2, 7275), (3, 13272), (5, 12157), (97, 4288)] },
    { n := 14557, F := 14556, R := 1, a := 2, factors := [2, 2, 3, 1213], residues := [(2, 7278), (3, 11778), (1213, 10245)] },
    { n := 14561, F := 14560, R := 1, a := 6, factors := [2, 2, 2, 2, 2, 5, 7, 13], residues := [(2, 7280), (5, 4203), (7, 2796), (13, 1947)] },
    { n := 14563, F := 14562, R := 1, a := 3, factors := [2, 3, 3, 809], residues := [(2, 7281), (3, 3422), (809, 1691)] },
    { n := 14591, F := 14590, R := 1, a := 11, factors := [2, 5, 1459], residues := [(2, 7295), (5, 4619), (1459, 1339)] },
    { n := 14593, F := 14592, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 2, 2, 3, 19], residues := [(2, 7296), (3, 2636), (19, 1013)] },
    { n := 14621, F := 14620, R := 1, a := 2, factors := [2, 2, 5, 17, 43], residues := [(2, 7310), (5, 4131), (17, 5640), (43, 13020)] },
    { n := 14627, F := 14626, R := 1, a := 2, factors := [2, 71, 103], residues := [(2, 7313), (71, 1662), (103, 9269)] },
    { n := 14629, F := 14628, R := 1, a := 2, factors := [2, 2, 3, 23, 53], residues := [(2, 7314), (3, 2491), (23, 2557), (53, 219)] },
    { n := 14633, F := 14632, R := 1, a := 3, factors := [2, 2, 2, 31, 59], residues := [(2, 7316), (31, 5497), (59, 4455)] },
    { n := 14639, F := 14638, R := 1, a := 11, factors := [2, 13, 563], residues := [(2, 7319), (13, 2738), (563, 12565)] },
    { n := 14653, F := 14652, R := 1, a := 2, factors := [2, 2, 3, 3, 11, 37], residues := [(2, 7326), (3, 8537), (11, 6705), (37, 8480)] },
    { n := 14657, F := 14656, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 229], residues := [(2, 7328), (229, 10484)] },
    { n := 14669, F := 14668, R := 1, a := 2, factors := [2, 2, 19, 193], residues := [(2, 7334), (19, 8211), (193, 5074)] },
    { n := 14683, F := 14682, R := 1, a := 3, factors := [2, 3, 2447], residues := [(2, 7341), (3, 13583), (2447, 10266)] },
    { n := 14699, F := 14698, R := 1, a := 2, factors := [2, 7349], residues := [(2, 7349), (7349, 4900)] },
    { n := 14713, F := 14712, R := 1, a := 5, factors := [2, 2, 2, 3, 613], residues := [(2, 7356), (3, 252), (613, 4586)] },
    { n := 14717, F := 14716, R := 1, a := 2, factors := [2, 2, 13, 283], residues := [(2, 7358), (13, 12473), (283, 7774)] },
    { n := 14723, F := 14722, R := 1, a := 2, factors := [2, 17, 433], residues := [(2, 7361), (17, 8205), (433, 5156)] },
    { n := 14731, F := 14730, R := 1, a := 10, factors := [2, 3, 5, 491], residues := [(2, 7365), (3, 4274), (5, 14105), (491, 2987)] },
    { n := 14737, F := 14736, R := 1, a := 10, factors := [2, 2, 2, 2, 3, 307], residues := [(2, 7368), (3, 6359), (307, 8565)] },
    { n := 14741, F := 14740, R := 1, a := 2, factors := [2, 2, 5, 11, 67], residues := [(2, 7370), (5, 14703), (11, 5286), (67, 12019)] },
    { n := 14747, F := 14746, R := 1, a := 2, factors := [2, 73, 101], residues := [(2, 7373), (73, 6507), (101, 3481)] },
    { n := 14753, F := 14752, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 461], residues := [(2, 7376), (461, 7110)] },
    { n := 14759, F := 14758, R := 1, a := 17, factors := [2, 47, 157], residues := [(2, 7379), (47, 2089), (157, 9439)] },
    { n := 14767, F := 14766, R := 1, a := 3, factors := [2, 3, 23, 107], residues := [(2, 7383), (3, 1676), (23, 13686), (107, 6270)] },
    { n := 14771, F := 14770, R := 1, a := 2, factors := [2, 5, 7, 211], residues := [(2, 7385), (5, 4762), (7, 12421), (211, 613)] },
    { n := 14779, F := 14778, R := 1, a := 3, factors := [2, 3, 3, 821], residues := [(2, 7389), (3, 2229), (821, 2075)] },
    { n := 14783, F := 14782, R := 1, a := 5, factors := [2, 19, 389], residues := [(2, 7391), (19, 2389), (389, 10717)] },
    { n := 14797, F := 14796, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 137], residues := [(2, 7398), (3, 4648), (137, 4826)] },
    { n := 14813, F := 14812, R := 1, a := 2, factors := [2, 2, 7, 23, 23], residues := [(2, 7406), (7, 10548), (23, 13469)] },
    { n := 14821, F := 14820, R := 1, a := 2, factors := [2, 2, 3, 5, 13, 19], residues := [(2, 7410), (3, 14150), (5, 4607), (13, 6641), (19, 9334)] },
    { n := 14827, F := 14826, R := 1, a := 2, factors := [2, 3, 7, 353], residues := [(2, 7413), (3, 7320), (7, 6715), (353, 9274)] },
    { n := 14831, F := 14830, R := 1, a := 11, factors := [2, 5, 1483], residues := [(2, 7415), (5, 11829), (1483, 13667)] },
    { n := 14843, F := 14842, R := 1, a := 2, factors := [2, 41, 181], residues := [(2, 7421), (41, 4039), (181, 1614)] },
    { n := 14851, F := 14850, R := 1, a := 2, factors := [2, 3, 3, 3, 5, 5, 11], residues := [(2, 7425), (3, 4005), (5, 9599), (11, 14426)] },
    { n := 14867, F := 14866, R := 1, a := 2, factors := [2, 7433], residues := [(2, 7433), (7433, 4956)] },
    { n := 14869, F := 14868, R := 1, a := 2, factors := [2, 2, 3, 3, 7, 59], residues := [(2, 7434), (3, 4000), (7, 2332), (59, 6943)] },
    { n := 14879, F := 14878, R := 1, a := 7, factors := [2, 43, 173], residues := [(2, 7439), (43, 3231), (173, 995)] },
    { n := 14887, F := 14886, R := 1, a := 3, factors := [2, 3, 3, 827], residues := [(2, 7443), (3, 12385), (827, 4677)] },
    { n := 14891, F := 14890, R := 1, a := 2, factors := [2, 5, 1489], residues := [(2, 7445), (5, 13533), (1489, 2460)] },
    { n := 14897, F := 14896, R := 1, a := 3, factors := [2, 2, 2, 2, 7, 7, 19], residues := [(2, 7448), (7, 959), (19, 6437)] },
    { n := 14923, F := 14922, R := 1, a := 2, factors := [2, 3, 3, 829], residues := [(2, 7461), (3, 6385), (829, 3759)] },
    { n := 14929, F := 14928, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 311], residues := [(2, 7464), (3, 3575), (311, 13690)] },
    { n := 14939, F := 14938, R := 1, a := 2, factors := [2, 7, 11, 97], residues := [(2, 7469), (7, 1327), (11, 175), (97, 662)] },
    { n := 14947, F := 14946, R := 1, a := 2, factors := [2, 3, 47, 53], residues := [(2, 7473), (3, 254), (47, 10231), (53, 11356)] },
    { n := 14951, F := 14950, R := 1, a := 19, factors := [2, 5, 5, 13, 23], residues := [(2, 7475), (5, 5726), (13, 10447), (23, 11706)] },
    { n := 14957, F := 14956, R := 1, a := 2, factors := [2, 2, 3739], residues := [(2, 7478), (3739, 6980)] },
    { n := 14969, F := 14968, R := 1, a := 3, factors := [2, 2, 2, 1871], residues := [(2, 7484), (1871, 9472)] },
    { n := 14983, F := 14982, R := 1, a := 3, factors := [2, 3, 11, 227], residues := [(2, 7491), (3, 885), (11, 14901), (227, 4244)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData14_valid : PocklingtonRow.Valid lowPocklingtonData14 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPrime_14153 : Nat.Prime 14153 := by
  let d := lowPocklingtonData14.get ⟨0, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14159 : Nat.Prime 14159 := by
  let d := lowPocklingtonData14.get ⟨1, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14173 : Nat.Prime 14173 := by
  let d := lowPocklingtonData14.get ⟨2, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14177 : Nat.Prime 14177 := by
  let d := lowPocklingtonData14.get ⟨3, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14197 : Nat.Prime 14197 := by
  let d := lowPocklingtonData14.get ⟨4, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14207 : Nat.Prime 14207 := by
  let d := lowPocklingtonData14.get ⟨5, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14221 : Nat.Prime 14221 := by
  let d := lowPocklingtonData14.get ⟨6, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14243 : Nat.Prime 14243 := by
  let d := lowPocklingtonData14.get ⟨7, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14249 : Nat.Prime 14249 := by
  let d := lowPocklingtonData14.get ⟨8, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14251 : Nat.Prime 14251 := by
  let d := lowPocklingtonData14.get ⟨9, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14281 : Nat.Prime 14281 := by
  let d := lowPocklingtonData14.get ⟨10, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14293 : Nat.Prime 14293 := by
  let d := lowPocklingtonData14.get ⟨11, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14303 : Nat.Prime 14303 := by
  let d := lowPocklingtonData14.get ⟨12, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14321 : Nat.Prime 14321 := by
  let d := lowPocklingtonData14.get ⟨13, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14323 : Nat.Prime 14323 := by
  let d := lowPocklingtonData14.get ⟨14, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14327 : Nat.Prime 14327 := by
  let d := lowPocklingtonData14.get ⟨15, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14341 : Nat.Prime 14341 := by
  let d := lowPocklingtonData14.get ⟨16, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14347 : Nat.Prime 14347 := by
  let d := lowPocklingtonData14.get ⟨17, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14369 : Nat.Prime 14369 := by
  let d := lowPocklingtonData14.get ⟨18, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14387 : Nat.Prime 14387 := by
  let d := lowPocklingtonData14.get ⟨19, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14389 : Nat.Prime 14389 := by
  let d := lowPocklingtonData14.get ⟨20, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14401 : Nat.Prime 14401 := by
  let d := lowPocklingtonData14.get ⟨21, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14407 : Nat.Prime 14407 := by
  let d := lowPocklingtonData14.get ⟨22, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14411 : Nat.Prime 14411 := by
  let d := lowPocklingtonData14.get ⟨23, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14419 : Nat.Prime 14419 := by
  let d := lowPocklingtonData14.get ⟨24, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14423 : Nat.Prime 14423 := by
  let d := lowPocklingtonData14.get ⟨25, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14431 : Nat.Prime 14431 := by
  let d := lowPocklingtonData14.get ⟨26, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14437 : Nat.Prime 14437 := by
  let d := lowPocklingtonData14.get ⟨27, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14447 : Nat.Prime 14447 := by
  let d := lowPocklingtonData14.get ⟨28, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14449 : Nat.Prime 14449 := by
  let d := lowPocklingtonData14.get ⟨29, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14461 : Nat.Prime 14461 := by
  let d := lowPocklingtonData14.get ⟨30, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14479 : Nat.Prime 14479 := by
  let d := lowPocklingtonData14.get ⟨31, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14489 : Nat.Prime 14489 := by
  let d := lowPocklingtonData14.get ⟨32, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14503 : Nat.Prime 14503 := by
  let d := lowPocklingtonData14.get ⟨33, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14519 : Nat.Prime 14519 := by
  let d := lowPocklingtonData14.get ⟨34, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14533 : Nat.Prime 14533 := by
  let d := lowPocklingtonData14.get ⟨35, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14537 : Nat.Prime 14537 := by
  let d := lowPocklingtonData14.get ⟨36, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14543 : Nat.Prime 14543 := by
  let d := lowPocklingtonData14.get ⟨37, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14549 : Nat.Prime 14549 := by
  let d := lowPocklingtonData14.get ⟨38, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14551 : Nat.Prime 14551 := by
  let d := lowPocklingtonData14.get ⟨39, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14557 : Nat.Prime 14557 := by
  let d := lowPocklingtonData14.get ⟨40, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14561 : Nat.Prime 14561 := by
  let d := lowPocklingtonData14.get ⟨41, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14563 : Nat.Prime 14563 := by
  let d := lowPocklingtonData14.get ⟨42, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14591 : Nat.Prime 14591 := by
  let d := lowPocklingtonData14.get ⟨43, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14593 : Nat.Prime 14593 := by
  let d := lowPocklingtonData14.get ⟨44, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14621 : Nat.Prime 14621 := by
  let d := lowPocklingtonData14.get ⟨45, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14627 : Nat.Prime 14627 := by
  let d := lowPocklingtonData14.get ⟨46, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14629 : Nat.Prime 14629 := by
  let d := lowPocklingtonData14.get ⟨47, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14633 : Nat.Prime 14633 := by
  let d := lowPocklingtonData14.get ⟨48, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14639 : Nat.Prime 14639 := by
  let d := lowPocklingtonData14.get ⟨49, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14653 : Nat.Prime 14653 := by
  let d := lowPocklingtonData14.get ⟨50, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14657 : Nat.Prime 14657 := by
  let d := lowPocklingtonData14.get ⟨51, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14669 : Nat.Prime 14669 := by
  let d := lowPocklingtonData14.get ⟨52, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14683 : Nat.Prime 14683 := by
  let d := lowPocklingtonData14.get ⟨53, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14699 : Nat.Prime 14699 := by
  let d := lowPocklingtonData14.get ⟨54, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14713 : Nat.Prime 14713 := by
  let d := lowPocklingtonData14.get ⟨55, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14717 : Nat.Prime 14717 := by
  let d := lowPocklingtonData14.get ⟨56, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14723 : Nat.Prime 14723 := by
  let d := lowPocklingtonData14.get ⟨57, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14731 : Nat.Prime 14731 := by
  let d := lowPocklingtonData14.get ⟨58, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14737 : Nat.Prime 14737 := by
  let d := lowPocklingtonData14.get ⟨59, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14741 : Nat.Prime 14741 := by
  let d := lowPocklingtonData14.get ⟨60, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14747 : Nat.Prime 14747 := by
  let d := lowPocklingtonData14.get ⟨61, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14753 : Nat.Prime 14753 := by
  let d := lowPocklingtonData14.get ⟨62, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14759 : Nat.Prime 14759 := by
  let d := lowPocklingtonData14.get ⟨63, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14767 : Nat.Prime 14767 := by
  let d := lowPocklingtonData14.get ⟨64, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14771 : Nat.Prime 14771 := by
  let d := lowPocklingtonData14.get ⟨65, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14779 : Nat.Prime 14779 := by
  let d := lowPocklingtonData14.get ⟨66, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14783 : Nat.Prime 14783 := by
  let d := lowPocklingtonData14.get ⟨67, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14797 : Nat.Prime 14797 := by
  let d := lowPocklingtonData14.get ⟨68, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14813 : Nat.Prime 14813 := by
  let d := lowPocklingtonData14.get ⟨69, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14821 : Nat.Prime 14821 := by
  let d := lowPocklingtonData14.get ⟨70, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14827 : Nat.Prime 14827 := by
  let d := lowPocklingtonData14.get ⟨71, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14831 : Nat.Prime 14831 := by
  let d := lowPocklingtonData14.get ⟨72, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14843 : Nat.Prime 14843 := by
  let d := lowPocklingtonData14.get ⟨73, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14851 : Nat.Prime 14851 := by
  let d := lowPocklingtonData14.get ⟨74, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14867 : Nat.Prime 14867 := by
  let d := lowPocklingtonData14.get ⟨75, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14869 : Nat.Prime 14869 := by
  let d := lowPocklingtonData14.get ⟨76, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14879 : Nat.Prime 14879 := by
  let d := lowPocklingtonData14.get ⟨77, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14887 : Nat.Prime 14887 := by
  let d := lowPocklingtonData14.get ⟨78, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14891 : Nat.Prime 14891 := by
  let d := lowPocklingtonData14.get ⟨79, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14897 : Nat.Prime 14897 := by
  let d := lowPocklingtonData14.get ⟨80, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14923 : Nat.Prime 14923 := by
  let d := lowPocklingtonData14.get ⟨81, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14929 : Nat.Prime 14929 := by
  let d := lowPocklingtonData14.get ⟨82, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14939 : Nat.Prime 14939 := by
  let d := lowPocklingtonData14.get ⟨83, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14947 : Nat.Prime 14947 := by
  let d := lowPocklingtonData14.get ⟨84, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14951 : Nat.Prime 14951 := by
  let d := lowPocklingtonData14.get ⟨85, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14957 : Nat.Prime 14957 := by
  let d := lowPocklingtonData14.get ⟨86, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14969 : Nat.Prime 14969 := by
  let d := lowPocklingtonData14.get ⟨87, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp

theorem lowPrime_14983 : Nat.Prime 14983 := by
  let d := lowPocklingtonData14.get ⟨88, by simp [lowPocklingtonData14]⟩
  have hd : d ∈ lowPocklingtonData14 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData14_valid hd
  simpa [d, lowPocklingtonData14] using hp
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14149) (q := 14153) (by exact lowPrime_14153) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14153) (q := 14159) (by exact lowPrime_14159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14159) (q := 14173) (by exact lowPrime_14173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14173) (q := 14177) (by exact lowPrime_14177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14177) (q := 14197) (by exact lowPrime_14197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14197) (q := 14207) (by exact lowPrime_14207) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14207) (q := 14221) (by exact lowPrime_14221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14221) (q := 14243) (by exact lowPrime_14243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part02_chain :
    DusartPrimeRowsChain 14149 14242 dusartPrimeRows_14051_14766_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14243) (q := 14249) (by exact lowPrime_14249) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14249) (q := 14251) (by exact lowPrime_14251) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14251) (q := 14281) (by exact lowPrime_14281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14281) (q := 14293) (by exact lowPrime_14293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14293) (q := 14303) (by exact lowPrime_14303) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14303) (q := 14321) (by exact lowPrime_14321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14321) (q := 14323) (by exact lowPrime_14323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14323) (q := 14327) (by exact lowPrime_14327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part03_chain :
    DusartPrimeRowsChain 14243 14326 dusartPrimeRows_14051_14766_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14327) (q := 14341) (by exact lowPrime_14341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14341) (q := 14347) (by exact lowPrime_14347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14347) (q := 14369) (by exact lowPrime_14369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14369) (q := 14387) (by exact lowPrime_14387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14387) (q := 14389) (by exact lowPrime_14389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14389) (q := 14401) (by exact lowPrime_14401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14401) (q := 14407) (by exact lowPrime_14407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14407) (q := 14411) (by exact lowPrime_14411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part04_chain :
    DusartPrimeRowsChain 14327 14410 dusartPrimeRows_14051_14766_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14411) (q := 14419) (by exact lowPrime_14419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14419) (q := 14423) (by exact lowPrime_14423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14423) (q := 14431) (by exact lowPrime_14431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14431) (q := 14437) (by exact lowPrime_14437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14437) (q := 14447) (by exact lowPrime_14447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14447) (q := 14449) (by exact lowPrime_14449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14449) (q := 14461) (by exact lowPrime_14461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14461) (q := 14479) (by exact lowPrime_14479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part05_chain :
    DusartPrimeRowsChain 14411 14478 dusartPrimeRows_14051_14766_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14479) (q := 14489) (by exact lowPrime_14489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14489) (q := 14503) (by exact lowPrime_14503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14503) (q := 14519) (by exact lowPrime_14519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14519) (q := 14533) (by exact lowPrime_14533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14533) (q := 14537) (by exact lowPrime_14537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14537) (q := 14543) (by exact lowPrime_14543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14543) (q := 14549) (by exact lowPrime_14549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14549) (q := 14551) (by exact lowPrime_14551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part06_chain :
    DusartPrimeRowsChain 14479 14550 dusartPrimeRows_14051_14766_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14551) (q := 14557) (by exact lowPrime_14557) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14557) (q := 14561) (by exact lowPrime_14561) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14561) (q := 14563) (by exact lowPrime_14563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14563) (q := 14591) (by exact lowPrime_14591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14591) (q := 14593) (by exact lowPrime_14593) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14593) (q := 14621) (by exact lowPrime_14621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14621) (q := 14627) (by exact lowPrime_14627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14627) (q := 14629) (by exact lowPrime_14629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part07_chain :
    DusartPrimeRowsChain 14551 14628 dusartPrimeRows_14051_14766_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14629) (q := 14633) (by exact lowPrime_14633) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14633) (q := 14639) (by exact lowPrime_14639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14639) (q := 14653) (by exact lowPrime_14653) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14653) (q := 14657) (by exact lowPrime_14657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14657) (q := 14669) (by exact lowPrime_14669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14669) (q := 14683) (by exact lowPrime_14683) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14683) (q := 14699) (by exact lowPrime_14699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14699) (q := 14713) (by exact lowPrime_14713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part08_chain :
    DusartPrimeRowsChain 14629 14712 dusartPrimeRows_14051_14766_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14713) (q := 14717) (by exact lowPrime_14717) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14717) (q := 14723) (by exact lowPrime_14723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14723) (q := 14731) (by exact lowPrime_14731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14731) (q := 14737) (by exact lowPrime_14737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14737) (q := 14741) (by exact lowPrime_14741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14741) (q := 14747) (by exact lowPrime_14747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14747) (q := 14753) (by exact lowPrime_14753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14753) (q := 14759) (by exact lowPrime_14759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part09_chain :
    DusartPrimeRowsChain 14713 14758 dusartPrimeRows_14051_14766_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14759) (q := 14767) (by exact lowPrime_14767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part10_chain :
    DusartPrimeRowsChain 14759 14766 dusartPrimeRows_14051_14766_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14767) (q := 14771) (by exact lowPrime_14771) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14771) (q := 14779) (by exact lowPrime_14779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14779) (q := 14783) (by exact lowPrime_14783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14783) (q := 14797) (by exact lowPrime_14797) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14797) (q := 14813) (by exact lowPrime_14813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14813) (q := 14821) (by exact lowPrime_14821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14821) (q := 14827) (by exact lowPrime_14827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14827) (q := 14831) (by exact lowPrime_14831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part01_chain :
    DusartPrimeRowsChain 14767 14830 dusartPrimeRows_14767_15526_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_15521, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14831) (q := 14843) (by exact lowPrime_14843) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14843) (q := 14851) (by exact lowPrime_14851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14851) (q := 14867) (by exact lowPrime_14867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14867) (q := 14869) (by exact lowPrime_14869) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14869) (q := 14879) (by exact lowPrime_14879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14879) (q := 14887) (by exact lowPrime_14887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14887) (q := 14891) (by exact lowPrime_14891) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14891) (q := 14897) (by exact lowPrime_14897) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part02_chain :
    DusartPrimeRowsChain 14831 14896 dusartPrimeRows_14767_15526_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_15521, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14897) (q := 14923) (by exact lowPrime_14923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14923) (q := 14929) (by exact lowPrime_14929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14929) (q := 14939) (by exact lowPrime_14939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14939) (q := 14947) (by exact lowPrime_14947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14947) (q := 14951) (by exact lowPrime_14951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14951) (q := 14957) (by exact lowPrime_14957) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14957) (q := 14969) (by exact lowPrime_14969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 14969) (q := 14983) (by exact lowPrime_14983) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part03_chain :
    DusartPrimeRowsChain 14897 14982 dusartPrimeRows_14767_15526_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_15521, dusartPrimeRow_of_explicit_right]
