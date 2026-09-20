import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 15 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData15 : List PocklingtonData := [
    { n := 15013, F := 15012, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 139], residues := [(2, 7506), (3, 13358), (139, 14240)] },
    { n := 15017, F := 15016, R := 1, a := 3, factors := [2, 2, 2, 1877], residues := [(2, 7508), (1877, 9539)] },
    { n := 15031, F := 15030, R := 1, a := 3, factors := [2, 3, 3, 5, 167], residues := [(2, 7515), (3, 13244), (5, 8239), (167, 8961)] },
    { n := 15053, F := 15052, R := 1, a := 2, factors := [2, 2, 53, 71], residues := [(2, 7526), (53, 11650), (71, 1120)] },
    { n := 15061, F := 15060, R := 1, a := 2, factors := [2, 2, 3, 5, 251], residues := [(2, 7530), (3, 394), (5, 13891), (251, 4145)] },
    { n := 15073, F := 15072, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 3, 157], residues := [(2, 7536), (3, 12768), (157, 603)] },
    { n := 15077, F := 15076, R := 1, a := 2, factors := [2, 2, 3769], residues := [(2, 7538), (3769, 7036)] },
    { n := 15083, F := 15082, R := 1, a := 2, factors := [2, 7541], residues := [(2, 7541), (7541, 5028)] },
    { n := 15091, F := 15090, R := 1, a := 2, factors := [2, 3, 5, 503], residues := [(2, 7545), (3, 13860), (5, 3229), (503, 1080)] },
    { n := 15101, F := 15100, R := 1, a := 2, factors := [2, 2, 5, 5, 151], residues := [(2, 7550), (5, 4599), (151, 7219)] },
    { n := 15107, F := 15106, R := 1, a := 2, factors := [2, 7, 13, 83], residues := [(2, 7553), (7, 6935), (13, 6728), (83, 13015)] },
    { n := 15121, F := 15120, R := 1, a := 11, factors := [2, 2, 2, 2, 3, 3, 3, 5, 7], residues := [(2, 7560), (3, 2609), (5, 14801), (7, 12872)] },
    { n := 15131, F := 15130, R := 1, a := 2, factors := [2, 5, 17, 89], residues := [(2, 7565), (5, 12344), (17, 7324), (89, 9054)] },
    { n := 15137, F := 15136, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 11, 43], residues := [(2, 7568), (11, 4734), (43, 2214)] },
    { n := 15139, F := 15138, R := 1, a := 2, factors := [2, 3, 3, 29, 29], residues := [(2, 7569), (3, 13255), (29, 7360)] },
    { n := 15149, F := 15148, R := 1, a := 2, factors := [2, 2, 7, 541], residues := [(2, 7574), (7, 7916), (541, 13733)] },
    { n := 15161, F := 15160, R := 1, a := 3, factors := [2, 2, 2, 5, 379], residues := [(2, 7580), (5, 13883), (379, 15016)] },
    { n := 15173, F := 15172, R := 1, a := 2, factors := [2, 2, 3793], residues := [(2, 7586), (3793, 13150)] },
    { n := 15187, F := 15186, R := 1, a := 2, factors := [2, 3, 2531], residues := [(2, 7593), (3, 4741), (2531, 11330)] },
    { n := 15193, F := 15192, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 211], residues := [(2, 7596), (3, 6594), (211, 644)] },
    { n := 15199, F := 15198, R := 1, a := 6, factors := [2, 3, 17, 149], residues := [(2, 7599), (3, 6804), (17, 14255), (149, 13016)] },
    { n := 15217, F := 15216, R := 1, a := 10, factors := [2, 2, 2, 2, 3, 317], residues := [(2, 7608), (3, 10432), (317, 1785)] },
    { n := 15227, F := 15226, R := 1, a := 2, factors := [2, 23, 331], residues := [(2, 7613), (23, 8670), (331, 3267)] },
    { n := 15233, F := 15232, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 7, 17], residues := [(2, 7616), (7, 7806), (17, 3855)] },
    { n := 15241, F := 15240, R := 1, a := 11, factors := [2, 2, 2, 3, 5, 127], residues := [(2, 7620), (3, 8031), (5, 11917), (127, 14000)] },
    { n := 15259, F := 15258, R := 1, a := 2, factors := [2, 3, 2543], residues := [(2, 7629), (3, 8463), (2543, 7024)] },
    { n := 15263, F := 15262, R := 1, a := 5, factors := [2, 13, 587], residues := [(2, 7631), (13, 12773), (587, 2628)] },
    { n := 15269, F := 15268, R := 1, a := 2, factors := [2, 2, 11, 347], residues := [(2, 7634), (11, 13311), (347, 10324)] },
    { n := 15271, F := 15270, R := 1, a := 11, factors := [2, 3, 5, 509], residues := [(2, 7635), (3, 4080), (5, 1964), (509, 2101)] },
    { n := 15277, F := 15276, R := 1, a := 6, factors := [2, 2, 3, 19, 67], residues := [(2, 7638), (3, 5362), (19, 8071), (67, 3265)] },
    { n := 15287, F := 15286, R := 1, a := 5, factors := [2, 7643], residues := [(2, 7643), (7643, 637)] },
    { n := 15289, F := 15288, R := 1, a := 11, factors := [2, 2, 2, 3, 7, 7, 13], residues := [(2, 7644), (3, 5818), (7, 8016), (13, 10824)] },
    { n := 15299, F := 15298, R := 1, a := 2, factors := [2, 7649], residues := [(2, 7649), (7649, 5100)] },
    { n := 15307, F := 15306, R := 1, a := 3, factors := [2, 3, 2551], residues := [(2, 7653), (3, 11720), (2551, 12889)] },
    { n := 15313, F := 15312, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 11, 29], residues := [(2, 7656), (3, 7935), (11, 3590), (29, 6014)] },
    { n := 15319, F := 15318, R := 1, a := 3, factors := [2, 3, 3, 23, 37], residues := [(2, 7659), (3, 10392), (23, 7685), (37, 4743)] },
    { n := 15329, F := 15328, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 479], residues := [(2, 7664), (479, 14492)] },
    { n := 15331, F := 15330, R := 1, a := 2, factors := [2, 3, 5, 7, 73], residues := [(2, 7665), (3, 1123), (5, 12329), (7, 7461), (73, 6453)] },
    { n := 15349, F := 15348, R := 1, a := 2, factors := [2, 2, 3, 1279], residues := [(2, 7674), (3, 2182), (1279, 4764)] },
    { n := 15359, F := 15358, R := 1, a := 11, factors := [2, 7, 1097], residues := [(2, 7679), (7, 416), (1097, 5947)] },
    { n := 15361, F := 15360, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5], residues := [(2, 7680), (3, 7809), (5, 11126)] },
    { n := 15373, F := 15372, R := 1, a := 2, factors := [2, 2, 3, 3, 7, 61], residues := [(2, 7686), (3, 4288), (7, 9504), (61, 1067)] },
    { n := 15377, F := 15376, R := 1, a := 3, factors := [2, 2, 2, 2, 31, 31], residues := [(2, 7688), (31, 15168)] },
    { n := 15383, F := 15382, R := 1, a := 5, factors := [2, 7691], residues := [(2, 7691), (7691, 641)] },
    { n := 15391, F := 15390, R := 1, a := 12, factors := [2, 3, 3, 3, 3, 5, 19], residues := [(2, 7695), (3, 6118), (5, 12871), (19, 13459)] },
    { n := 15401, F := 15400, R := 1, a := 6, factors := [2, 2, 2, 5, 5, 7, 11], residues := [(2, 7700), (5, 7536), (7, 2703), (11, 394)] },
    { n := 15413, F := 15412, R := 1, a := 2, factors := [2, 2, 3853], residues := [(2, 7706), (3853, 13358)] },
    { n := 15427, F := 15426, R := 1, a := 2, factors := [2, 3, 3, 857], residues := [(2, 7713), (3, 11363), (857, 15294)] },
    { n := 15439, F := 15438, R := 1, a := 3, factors := [2, 3, 31, 83], residues := [(2, 7719), (3, 12940), (31, 15220), (83, 6490)] },
    { n := 15443, F := 15442, R := 1, a := 2, factors := [2, 7, 1103], residues := [(2, 7721), (7, 13870), (1103, 15328)] },
    { n := 15451, F := 15450, R := 1, a := 3, factors := [2, 3, 5, 5, 103], residues := [(2, 7725), (3, 9781), (5, 5130), (103, 15399)] },
    { n := 15461, F := 15460, R := 1, a := 2, factors := [2, 2, 5, 773], residues := [(2, 7730), (5, 68), (773, 4059)] },
    { n := 15467, F := 15466, R := 1, a := 5, factors := [2, 11, 19, 37], residues := [(2, 7733), (11, 13562), (19, 5100), (37, 6493)] },
    { n := 15473, F := 15472, R := 1, a := 3, factors := [2, 2, 2, 2, 967], residues := [(2, 7736), (967, 3692)] },
    { n := 15493, F := 15492, R := 1, a := 5, factors := [2, 2, 3, 1291], residues := [(2, 7746), (3, 8053), (1291, 11985)] },
    { n := 15497, F := 15496, R := 1, a := 3, factors := [2, 2, 2, 13, 149], residues := [(2, 7748), (13, 2505), (149, 1322)] },
    { n := 15511, F := 15510, R := 1, a := 3, factors := [2, 3, 5, 11, 47], residues := [(2, 7755), (3, 12027), (5, 15035), (11, 12747), (47, 5002)] },
    { n := 15527, F := 15526, R := 1, a := 5, factors := [2, 7, 1109], residues := [(2, 7763), (7, 3347), (1109, 2631)] },
    { n := 15541, F := 15540, R := 1, a := 6, factors := [2, 2, 3, 5, 7, 37], residues := [(2, 7770), (3, 8843), (5, 10857), (7, 10993), (37, 13729)] },
    { n := 15551, F := 15550, R := 1, a := 7, factors := [2, 5, 5, 311], residues := [(2, 7775), (5, 13088), (311, 7712)] },
    { n := 15559, F := 15558, R := 1, a := 3, factors := [2, 3, 2593], residues := [(2, 7779), (3, 14347), (2593, 2928)] },
    { n := 15569, F := 15568, R := 1, a := 3, factors := [2, 2, 2, 2, 7, 139], residues := [(2, 7784), (7, 12258), (139, 9713)] },
    { n := 15581, F := 15580, R := 1, a := 2, factors := [2, 2, 5, 19, 41], residues := [(2, 7790), (5, 7002), (19, 348), (41, 5935)] },
    { n := 15583, F := 15582, R := 1, a := 5, factors := [2, 3, 7, 7, 53], residues := [(2, 7791), (3, 3217), (7, 11802), (53, 10548)] },
    { n := 15601, F := 15600, R := 1, a := 23, factors := [2, 2, 2, 2, 3, 5, 5, 13], residues := [(2, 7800), (3, 14481), (5, 15462), (13, 7994)] },
    { n := 15607, F := 15606, R := 1, a := 3, factors := [2, 3, 3, 3, 17, 17], residues := [(2, 7803), (3, 14544), (17, 1966)] },
    { n := 15619, F := 15618, R := 1, a := 7, factors := [2, 3, 19, 137], residues := [(2, 7809), (3, 1448), (19, 10349), (137, 14566)] },
    { n := 15629, F := 15628, R := 1, a := 2, factors := [2, 2, 3907], residues := [(2, 7814), (3907, 1042)] },
    { n := 15641, F := 15640, R := 1, a := 3, factors := [2, 2, 2, 5, 17, 23], residues := [(2, 7820), (5, 6903), (17, 13206), (23, 7100)] },
    { n := 15643, F := 15642, R := 1, a := 5, factors := [2, 3, 3, 11, 79], residues := [(2, 7821), (3, 12069), (11, 1403), (79, 13825)] },
    { n := 15647, F := 15646, R := 1, a := 5, factors := [2, 7823], residues := [(2, 7823), (7823, 652)] },
    { n := 15649, F := 15648, R := 1, a := 11, factors := [2, 2, 2, 2, 2, 3, 163], residues := [(2, 7824), (3, 8616), (163, 5213)] },
    { n := 15661, F := 15660, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 5, 29], residues := [(2, 7830), (3, 13386), (5, 5363), (29, 3919)] },
    { n := 15667, F := 15666, R := 1, a := 2, factors := [2, 3, 7, 373], residues := [(2, 7833), (3, 8259), (7, 13790), (373, 8447)] },
    { n := 15671, F := 15670, R := 1, a := 13, factors := [2, 5, 1567], residues := [(2, 7835), (5, 2029), (1567, 1400)] },
    { n := 15679, F := 15678, R := 1, a := 11, factors := [2, 3, 3, 13, 67], residues := [(2, 7839), (3, 4239), (13, 14607), (67, 15173)] },
    { n := 15683, F := 15682, R := 1, a := 2, factors := [2, 7841], residues := [(2, 7841), (7841, 5228)] },
    { n := 15727, F := 15726, R := 1, a := 3, factors := [2, 3, 2621], residues := [(2, 7863), (3, 13865), (2621, 11428)] },
    { n := 15731, F := 15730, R := 1, a := 2, factors := [2, 5, 11, 11, 13], residues := [(2, 7865), (5, 4097), (11, 3888), (13, 11175)] },
    { n := 15733, F := 15732, R := 1, a := 6, factors := [2, 2, 3, 3, 19, 23], residues := [(2, 7866), (3, 15292), (19, 8699), (23, 5611)] },
    { n := 15737, F := 15736, R := 1, a := 3, factors := [2, 2, 2, 7, 281], residues := [(2, 7868), (7, 13272), (281, 14919)] },
    { n := 15739, F := 15738, R := 1, a := 2, factors := [2, 3, 43, 61], residues := [(2, 7869), (3, 8821), (43, 8607), (61, 7795)] },
    { n := 15749, F := 15748, R := 1, a := 2, factors := [2, 2, 31, 127], residues := [(2, 7874), (31, 12802), (127, 5208)] },
    { n := 15761, F := 15760, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 197], residues := [(2, 7880), (5, 5370), (197, 6417)] },
    { n := 15767, F := 15766, R := 1, a := 5, factors := [2, 7883], residues := [(2, 7883), (7883, 657)] },
    { n := 15773, F := 15772, R := 1, a := 2, factors := [2, 2, 3943], residues := [(2, 7886), (3943, 13670)] },
    { n := 15787, F := 15786, R := 1, a := 2, factors := [2, 3, 3, 877], residues := [(2, 7893), (3, 1509), (877, 1162)] },
    { n := 15791, F := 15790, R := 1, a := 29, factors := [2, 5, 1579], residues := [(2, 7895), (5, 11459), (1579, 12936)] },
    { n := 15797, F := 15796, R := 1, a := 2, factors := [2, 2, 11, 359], residues := [(2, 7898), (11, 6976), (359, 3973)] },
    { n := 15803, F := 15802, R := 1, a := 2, factors := [2, 7901], residues := [(2, 7901), (7901, 5268)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData15_valid : PocklingtonRow.Valid lowPocklingtonData15 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPrime_15013 : Nat.Prime 15013 := by
  let d := lowPocklingtonData15.get ⟨0, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15017 : Nat.Prime 15017 := by
  let d := lowPocklingtonData15.get ⟨1, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15031 : Nat.Prime 15031 := by
  let d := lowPocklingtonData15.get ⟨2, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15053 : Nat.Prime 15053 := by
  let d := lowPocklingtonData15.get ⟨3, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15061 : Nat.Prime 15061 := by
  let d := lowPocklingtonData15.get ⟨4, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15073 : Nat.Prime 15073 := by
  let d := lowPocklingtonData15.get ⟨5, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15077 : Nat.Prime 15077 := by
  let d := lowPocklingtonData15.get ⟨6, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15083 : Nat.Prime 15083 := by
  let d := lowPocklingtonData15.get ⟨7, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15091 : Nat.Prime 15091 := by
  let d := lowPocklingtonData15.get ⟨8, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15101 : Nat.Prime 15101 := by
  let d := lowPocklingtonData15.get ⟨9, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15107 : Nat.Prime 15107 := by
  let d := lowPocklingtonData15.get ⟨10, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15121 : Nat.Prime 15121 := by
  let d := lowPocklingtonData15.get ⟨11, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15131 : Nat.Prime 15131 := by
  let d := lowPocklingtonData15.get ⟨12, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15137 : Nat.Prime 15137 := by
  let d := lowPocklingtonData15.get ⟨13, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15139 : Nat.Prime 15139 := by
  let d := lowPocklingtonData15.get ⟨14, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15149 : Nat.Prime 15149 := by
  let d := lowPocklingtonData15.get ⟨15, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15161 : Nat.Prime 15161 := by
  let d := lowPocklingtonData15.get ⟨16, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15173 : Nat.Prime 15173 := by
  let d := lowPocklingtonData15.get ⟨17, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15187 : Nat.Prime 15187 := by
  let d := lowPocklingtonData15.get ⟨18, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15193 : Nat.Prime 15193 := by
  let d := lowPocklingtonData15.get ⟨19, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15199 : Nat.Prime 15199 := by
  let d := lowPocklingtonData15.get ⟨20, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15217 : Nat.Prime 15217 := by
  let d := lowPocklingtonData15.get ⟨21, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15227 : Nat.Prime 15227 := by
  let d := lowPocklingtonData15.get ⟨22, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15233 : Nat.Prime 15233 := by
  let d := lowPocklingtonData15.get ⟨23, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15241 : Nat.Prime 15241 := by
  let d := lowPocklingtonData15.get ⟨24, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15259 : Nat.Prime 15259 := by
  let d := lowPocklingtonData15.get ⟨25, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15263 : Nat.Prime 15263 := by
  let d := lowPocklingtonData15.get ⟨26, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15269 : Nat.Prime 15269 := by
  let d := lowPocklingtonData15.get ⟨27, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15271 : Nat.Prime 15271 := by
  let d := lowPocklingtonData15.get ⟨28, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15277 : Nat.Prime 15277 := by
  let d := lowPocklingtonData15.get ⟨29, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15287 : Nat.Prime 15287 := by
  let d := lowPocklingtonData15.get ⟨30, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15289 : Nat.Prime 15289 := by
  let d := lowPocklingtonData15.get ⟨31, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15299 : Nat.Prime 15299 := by
  let d := lowPocklingtonData15.get ⟨32, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15307 : Nat.Prime 15307 := by
  let d := lowPocklingtonData15.get ⟨33, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15313 : Nat.Prime 15313 := by
  let d := lowPocklingtonData15.get ⟨34, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15319 : Nat.Prime 15319 := by
  let d := lowPocklingtonData15.get ⟨35, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15329 : Nat.Prime 15329 := by
  let d := lowPocklingtonData15.get ⟨36, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15331 : Nat.Prime 15331 := by
  let d := lowPocklingtonData15.get ⟨37, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15349 : Nat.Prime 15349 := by
  let d := lowPocklingtonData15.get ⟨38, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15359 : Nat.Prime 15359 := by
  let d := lowPocklingtonData15.get ⟨39, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15361 : Nat.Prime 15361 := by
  let d := lowPocklingtonData15.get ⟨40, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15373 : Nat.Prime 15373 := by
  let d := lowPocklingtonData15.get ⟨41, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15377 : Nat.Prime 15377 := by
  let d := lowPocklingtonData15.get ⟨42, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15383 : Nat.Prime 15383 := by
  let d := lowPocklingtonData15.get ⟨43, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15391 : Nat.Prime 15391 := by
  let d := lowPocklingtonData15.get ⟨44, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15401 : Nat.Prime 15401 := by
  let d := lowPocklingtonData15.get ⟨45, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15413 : Nat.Prime 15413 := by
  let d := lowPocklingtonData15.get ⟨46, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15427 : Nat.Prime 15427 := by
  let d := lowPocklingtonData15.get ⟨47, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15439 : Nat.Prime 15439 := by
  let d := lowPocklingtonData15.get ⟨48, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15443 : Nat.Prime 15443 := by
  let d := lowPocklingtonData15.get ⟨49, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15451 : Nat.Prime 15451 := by
  let d := lowPocklingtonData15.get ⟨50, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15461 : Nat.Prime 15461 := by
  let d := lowPocklingtonData15.get ⟨51, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15467 : Nat.Prime 15467 := by
  let d := lowPocklingtonData15.get ⟨52, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15473 : Nat.Prime 15473 := by
  let d := lowPocklingtonData15.get ⟨53, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15493 : Nat.Prime 15493 := by
  let d := lowPocklingtonData15.get ⟨54, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15497 : Nat.Prime 15497 := by
  let d := lowPocklingtonData15.get ⟨55, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15511 : Nat.Prime 15511 := by
  let d := lowPocklingtonData15.get ⟨56, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15527 : Nat.Prime 15527 := by
  let d := lowPocklingtonData15.get ⟨57, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15541 : Nat.Prime 15541 := by
  let d := lowPocklingtonData15.get ⟨58, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15551 : Nat.Prime 15551 := by
  let d := lowPocklingtonData15.get ⟨59, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15559 : Nat.Prime 15559 := by
  let d := lowPocklingtonData15.get ⟨60, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15569 : Nat.Prime 15569 := by
  let d := lowPocklingtonData15.get ⟨61, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15581 : Nat.Prime 15581 := by
  let d := lowPocklingtonData15.get ⟨62, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15583 : Nat.Prime 15583 := by
  let d := lowPocklingtonData15.get ⟨63, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15601 : Nat.Prime 15601 := by
  let d := lowPocklingtonData15.get ⟨64, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15607 : Nat.Prime 15607 := by
  let d := lowPocklingtonData15.get ⟨65, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15619 : Nat.Prime 15619 := by
  let d := lowPocklingtonData15.get ⟨66, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15629 : Nat.Prime 15629 := by
  let d := lowPocklingtonData15.get ⟨67, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15641 : Nat.Prime 15641 := by
  let d := lowPocklingtonData15.get ⟨68, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15643 : Nat.Prime 15643 := by
  let d := lowPocklingtonData15.get ⟨69, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15647 : Nat.Prime 15647 := by
  let d := lowPocklingtonData15.get ⟨70, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15649 : Nat.Prime 15649 := by
  let d := lowPocklingtonData15.get ⟨71, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15661 : Nat.Prime 15661 := by
  let d := lowPocklingtonData15.get ⟨72, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15667 : Nat.Prime 15667 := by
  let d := lowPocklingtonData15.get ⟨73, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15671 : Nat.Prime 15671 := by
  let d := lowPocklingtonData15.get ⟨74, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15679 : Nat.Prime 15679 := by
  let d := lowPocklingtonData15.get ⟨75, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15683 : Nat.Prime 15683 := by
  let d := lowPocklingtonData15.get ⟨76, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15727 : Nat.Prime 15727 := by
  let d := lowPocklingtonData15.get ⟨77, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15731 : Nat.Prime 15731 := by
  let d := lowPocklingtonData15.get ⟨78, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15733 : Nat.Prime 15733 := by
  let d := lowPocklingtonData15.get ⟨79, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15737 : Nat.Prime 15737 := by
  let d := lowPocklingtonData15.get ⟨80, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15739 : Nat.Prime 15739 := by
  let d := lowPocklingtonData15.get ⟨81, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15749 : Nat.Prime 15749 := by
  let d := lowPocklingtonData15.get ⟨82, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15761 : Nat.Prime 15761 := by
  let d := lowPocklingtonData15.get ⟨83, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15767 : Nat.Prime 15767 := by
  let d := lowPocklingtonData15.get ⟨84, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15773 : Nat.Prime 15773 := by
  let d := lowPocklingtonData15.get ⟨85, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15787 : Nat.Prime 15787 := by
  let d := lowPocklingtonData15.get ⟨86, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15791 : Nat.Prime 15791 := by
  let d := lowPocklingtonData15.get ⟨87, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15797 : Nat.Prime 15797 := by
  let d := lowPocklingtonData15.get ⟨88, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp

theorem lowPrime_15803 : Nat.Prime 15803 := by
  let d := lowPocklingtonData15.get ⟨89, by simp [lowPocklingtonData15]⟩
  have hd : d ∈ lowPocklingtonData15 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData15_valid hd
  simpa [d, lowPocklingtonData15] using hp
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 14983) (q := 15013) (by exact lowPrime_15013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15013) (q := 15017) (by exact lowPrime_15017) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15017) (q := 15031) (by exact lowPrime_15031) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15031) (q := 15053) (by exact lowPrime_15053) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15053) (q := 15061) (by exact lowPrime_15061) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15061) (q := 15073) (by exact lowPrime_15073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15073) (q := 15077) (by exact lowPrime_15077) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15077) (q := 15083) (by exact lowPrime_15083) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part04_chain :
    DusartPrimeRowsChain 14983 15082 dusartPrimeRows_14767_15526_part04 := by
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
def dusartPrimeRows_14767_15526_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15083) (q := 15091) (by exact lowPrime_15091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15091) (q := 15101) (by exact lowPrime_15101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15101) (q := 15107) (by exact lowPrime_15107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15107) (q := 15121) (by exact lowPrime_15121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15121) (q := 15131) (by exact lowPrime_15131) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15131) (q := 15137) (by exact lowPrime_15137) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15137) (q := 15139) (by exact lowPrime_15139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15139) (q := 15149) (by exact lowPrime_15149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part05_chain :
    DusartPrimeRowsChain 15083 15148 dusartPrimeRows_14767_15526_part05 := by
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
def dusartPrimeRows_14767_15526_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15149) (q := 15161) (by exact lowPrime_15161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15161) (q := 15173) (by exact lowPrime_15173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15173) (q := 15187) (by exact lowPrime_15187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15187) (q := 15193) (by exact lowPrime_15193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15193) (q := 15199) (by exact lowPrime_15199) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15199) (q := 15217) (by exact lowPrime_15217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15217) (q := 15227) (by exact lowPrime_15227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15227) (q := 15233) (by exact lowPrime_15233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part06_chain :
    DusartPrimeRowsChain 15149 15232 dusartPrimeRows_14767_15526_part06 := by
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
def dusartPrimeRows_14767_15526_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15233) (q := 15241) (by exact lowPrime_15241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15241) (q := 15259) (by exact lowPrime_15259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15259) (q := 15263) (by exact lowPrime_15263) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15263) (q := 15269) (by exact lowPrime_15269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15269) (q := 15271) (by exact lowPrime_15271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15271) (q := 15277) (by exact lowPrime_15277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15277) (q := 15287) (by exact lowPrime_15287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15287) (q := 15289) (by exact lowPrime_15289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part07_chain :
    DusartPrimeRowsChain 15233 15288 dusartPrimeRows_14767_15526_part07 := by
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
def dusartPrimeRows_14767_15526_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15289) (q := 15299) (by exact lowPrime_15299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15299) (q := 15307) (by exact lowPrime_15307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15307) (q := 15313) (by exact lowPrime_15313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15313) (q := 15319) (by exact lowPrime_15319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15319) (q := 15329) (by exact lowPrime_15329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15329) (q := 15331) (by exact lowPrime_15331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15331) (q := 15349) (by exact lowPrime_15349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15349) (q := 15359) (by exact lowPrime_15359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part08_chain :
    DusartPrimeRowsChain 15289 15358 dusartPrimeRows_14767_15526_part08 := by
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
def dusartPrimeRows_14767_15526_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15359) (q := 15361) (by exact lowPrime_15361) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15361) (q := 15373) (by exact lowPrime_15373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15373) (q := 15377) (by exact lowPrime_15377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15377) (q := 15383) (by exact lowPrime_15383) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15383) (q := 15391) (by exact lowPrime_15391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15391) (q := 15401) (by exact lowPrime_15401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15401) (q := 15413) (by exact lowPrime_15413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15413) (q := 15427) (by exact lowPrime_15427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part09_chain :
    DusartPrimeRowsChain 15359 15426 dusartPrimeRows_14767_15526_part09 := by
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
def dusartPrimeRows_14767_15526_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15427) (q := 15439) (by exact lowPrime_15439) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15439) (q := 15443) (by exact lowPrime_15443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15443) (q := 15451) (by exact lowPrime_15451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15451) (q := 15461) (by exact lowPrime_15461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15461) (q := 15467) (by exact lowPrime_15467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15467) (q := 15473) (by exact lowPrime_15473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15473) (q := 15493) (by exact lowPrime_15493) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15493) (q := 15497) (by exact lowPrime_15497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part10_chain :
    DusartPrimeRowsChain 15427 15496 dusartPrimeRows_14767_15526_part10 := by
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
def dusartPrimeRows_14767_15526_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15497) (q := 15511) (by exact lowPrime_15511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15511) (q := 15527) (by exact lowPrime_15527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part11_chain :
    DusartPrimeRowsChain 15497 15526 dusartPrimeRows_14767_15526_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_15521, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15527) (q := 15541) (by exact lowPrime_15541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15541) (q := 15551) (by exact lowPrime_15551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15551) (q := 15559) (by exact lowPrime_15559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15559) (q := 15569) (by exact lowPrime_15569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15569) (q := 15581) (by exact lowPrime_15581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15581) (q := 15583) (by exact lowPrime_15583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15583) (q := 15601) (by exact lowPrime_15601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15601) (q := 15607) (by exact lowPrime_15607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part01_chain :
    DusartPrimeRowsChain 15527 15606 dusartPrimeRows_15527_16318_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_16317, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15607) (q := 15619) (by exact lowPrime_15619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15619) (q := 15629) (by exact lowPrime_15629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15629) (q := 15641) (by exact lowPrime_15641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15641) (q := 15643) (by exact lowPrime_15643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15643) (q := 15647) (by exact lowPrime_15647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15647) (q := 15649) (by exact lowPrime_15649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15649) (q := 15661) (by exact lowPrime_15661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15661) (q := 15667) (by exact lowPrime_15667) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part02_chain :
    DusartPrimeRowsChain 15607 15666 dusartPrimeRows_15527_16318_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_16317, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15667) (q := 15671) (by exact lowPrime_15671) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15671) (q := 15679) (by exact lowPrime_15679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15679) (q := 15683) (by exact lowPrime_15683) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15683) (q := 15727) (by exact lowPrime_15727) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15727) (q := 15731) (by exact lowPrime_15731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15731) (q := 15733) (by exact lowPrime_15733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15733) (q := 15737) (by exact lowPrime_15737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15737) (q := 15739) (by exact lowPrime_15739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part03_chain :
    DusartPrimeRowsChain 15667 15738 dusartPrimeRows_15527_16318_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_16317, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15739) (q := 15749) (by exact lowPrime_15749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15749) (q := 15761) (by exact lowPrime_15761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15761) (q := 15767) (by exact lowPrime_15767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15767) (q := 15773) (by exact lowPrime_15773) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15773) (q := 15787) (by exact lowPrime_15787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15787) (q := 15791) (by exact lowPrime_15791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15791) (q := 15797) (by exact lowPrime_15797) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15797) (q := 15803) (by exact lowPrime_15803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part04_chain :
    DusartPrimeRowsChain 15739 15802 dusartPrimeRows_15527_16318_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_16317, dusartPrimeRow_of_explicit_right]
