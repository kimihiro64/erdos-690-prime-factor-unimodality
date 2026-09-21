import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 16 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData16 : List PocklingtonData := [
    { n := 15809, F := 15808, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 13, 19], residues := [(2, 7904), (13, 4754), (19, 10322)] },
    { n := 15817, F := 15816, R := 1, a := 5, factors := [2, 2, 2, 3, 659], residues := [(2, 7908), (3, 9553), (659, 6734)] },
    { n := 15823, F := 15822, R := 1, a := 3, factors := [2, 3, 3, 3, 293], residues := [(2, 7911), (3, 3035), (293, 12775)] },
    { n := 15859, F := 15858, R := 1, a := 2, factors := [2, 3, 3, 881], residues := [(2, 7929), (3, 838), (881, 5185)] },
    { n := 15877, F := 15876, R := 1, a := 5, factors := [2, 2, 3, 3, 3, 3, 7, 7], residues := [(2, 7938), (3, 2846), (7, 4620)] },
    { n := 15881, F := 15880, R := 1, a := 3, factors := [2, 2, 2, 5, 397], residues := [(2, 7940), (5, 9416), (397, 3090)] },
    { n := 15887, F := 15886, R := 1, a := 5, factors := [2, 13, 13, 47], residues := [(2, 7943), (13, 9880), (47, 11667)] },
    { n := 15889, F := 15888, R := 1, a := 21, factors := [2, 2, 2, 2, 3, 331], residues := [(2, 7944), (3, 10481), (331, 2207)] },
    { n := 15901, F := 15900, R := 1, a := 10, factors := [2, 2, 3, 5, 5, 53], residues := [(2, 7950), (3, 15206), (5, 10249), (53, 8540)] },
    { n := 15907, F := 15906, R := 1, a := 2, factors := [2, 3, 11, 241], residues := [(2, 7953), (3, 6534), (11, 7818), (241, 3401)] },
    { n := 15913, F := 15912, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 13, 17], residues := [(2, 7956), (3, 4604), (13, 5535), (17, 3382)] },
    { n := 15919, F := 15918, R := 1, a := 6, factors := [2, 3, 7, 379], residues := [(2, 7959), (3, 13445), (7, 61), (379, 10184)] },
    { n := 15923, F := 15922, R := 1, a := 2, factors := [2, 19, 419], residues := [(2, 7961), (19, 4099), (419, 3566)] },
    { n := 15937, F := 15936, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 3, 83], residues := [(2, 7968), (3, 13336), (83, 14811)] },
    { n := 15959, F := 15958, R := 1, a := 11, factors := [2, 79, 101], residues := [(2, 7979), (79, 15838), (101, 15186)] },
    { n := 15971, F := 15970, R := 1, a := 2, factors := [2, 5, 1597], residues := [(2, 7985), (5, 541), (1597, 1046)] },
    { n := 15973, F := 15972, R := 1, a := 7, factors := [2, 2, 3, 11, 11, 11], residues := [(2, 7986), (3, 4979), (11, 621)] },
    { n := 15991, F := 15990, R := 1, a := 12, factors := [2, 3, 5, 13, 41], residues := [(2, 7995), (3, 12011), (5, 4639), (13, 7159), (41, 11434)] },
    { n := 16001, F := 16000, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 5, 5, 5], residues := [(2, 8000), (5, 9893)] },
    { n := 16007, F := 16006, R := 1, a := 5, factors := [2, 53, 151], residues := [(2, 8003), (53, 8953), (151, 13550)] },
    { n := 16033, F := 16032, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 3, 167], residues := [(2, 8016), (3, 7656), (167, 9045)] },
    { n := 16057, F := 16056, R := 1, a := 7, factors := [2, 2, 2, 3, 3, 223], residues := [(2, 8028), (3, 3789), (223, 7414)] },
    { n := 16061, F := 16060, R := 1, a := 12, factors := [2, 2, 5, 11, 73], residues := [(2, 8030), (5, 7846), (11, 13647), (73, 10402)] },
    { n := 16063, F := 16062, R := 1, a := 5, factors := [2, 3, 2677], residues := [(2, 8031), (3, 9523), (2677, 12404)] },
    { n := 16067, F := 16066, R := 1, a := 2, factors := [2, 29, 277], residues := [(2, 8033), (29, 2389), (277, 13292)] },
    { n := 16069, F := 16068, R := 1, a := 2, factors := [2, 2, 3, 13, 103], residues := [(2, 8034), (3, 650), (13, 12259), (103, 8098)] },
    { n := 16073, F := 16072, R := 1, a := 3, factors := [2, 2, 2, 7, 7, 41], residues := [(2, 8036), (7, 2262), (41, 4583)] },
    { n := 16087, F := 16086, R := 1, a := 5, factors := [2, 3, 7, 383], residues := [(2, 8043), (3, 8851), (7, 3958), (383, 8199)] },
    { n := 16091, F := 16090, R := 1, a := 6, factors := [2, 5, 1609], residues := [(2, 8045), (5, 4503), (1609, 897)] },
    { n := 16097, F := 16096, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 503], residues := [(2, 8048), (503, 5528)] },
    { n := 16103, F := 16102, R := 1, a := 5, factors := [2, 83, 97], residues := [(2, 8051), (83, 10766), (97, 2401)] },
    { n := 16111, F := 16110, R := 1, a := 7, factors := [2, 3, 3, 5, 179], residues := [(2, 8055), (3, 12629), (5, 1480), (179, 6744)] },
    { n := 16127, F := 16126, R := 1, a := 5, factors := [2, 11, 733], residues := [(2, 8063), (11, 13280), (733, 14734)] },
    { n := 16139, F := 16138, R := 1, a := 2, factors := [2, 8069], residues := [(2, 8069), (8069, 5380)] },
    { n := 16141, F := 16140, R := 1, a := 6, factors := [2, 2, 3, 5, 269], residues := [(2, 8070), (3, 14806), (5, 5663), (269, 10953)] },
    { n := 16183, F := 16182, R := 1, a := 3, factors := [2, 3, 3, 29, 31], residues := [(2, 8091), (3, 1736), (29, 13883), (31, 10512)] },
    { n := 16187, F := 16186, R := 1, a := 2, factors := [2, 8093], residues := [(2, 8093), (8093, 5396)] },
    { n := 16189, F := 16188, R := 1, a := 2, factors := [2, 2, 3, 19, 71], residues := [(2, 8094), (3, 1972), (19, 2237), (71, 15594)] },
    { n := 16193, F := 16192, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 11, 23], residues := [(2, 8096), (11, 6866), (23, 3036)] },
    { n := 16217, F := 16216, R := 1, a := 3, factors := [2, 2, 2, 2027], residues := [(2, 8108), (2027, 15641)] },
    { n := 16223, F := 16222, R := 1, a := 5, factors := [2, 8111], residues := [(2, 8111), (8111, 676)] },
    { n := 16229, F := 16228, R := 1, a := 2, factors := [2, 2, 4057], residues := [(2, 8114), (4057, 1082)] },
    { n := 16231, F := 16230, R := 1, a := 3, factors := [2, 3, 5, 541], residues := [(2, 8115), (3, 12835), (5, 5001), (541, 1376)] },
    { n := 16249, F := 16248, R := 1, a := 17, factors := [2, 2, 2, 3, 677], residues := [(2, 8124), (3, 13743), (677, 15902)] },
    { n := 16253, F := 16252, R := 1, a := 2, factors := [2, 2, 17, 239], residues := [(2, 8126), (17, 13171), (239, 6135)] },
    { n := 16267, F := 16266, R := 1, a := 3, factors := [2, 3, 2711], residues := [(2, 8133), (3, 265), (2711, 648)] },
    { n := 16273, F := 16272, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 3, 113], residues := [(2, 8136), (3, 9133), (113, 1231)] },
    { n := 16301, F := 16300, R := 1, a := 2, factors := [2, 2, 5, 5, 163], residues := [(2, 8150), (5, 12873), (163, 10036)] },
    { n := 16319, F := 16318, R := 1, a := 7, factors := [2, 41, 199], residues := [(2, 8159), (41, 5651), (199, 10146)] },
    { n := 16333, F := 16332, R := 1, a := 2, factors := [2, 2, 3, 1361], residues := [(2, 8166), (3, 516), (1361, 13553)] },
    { n := 16339, F := 16338, R := 1, a := 2, factors := [2, 3, 7, 389], residues := [(2, 8169), (3, 7817), (7, 5072), (389, 14445)] },
    { n := 16349, F := 16348, R := 1, a := 2, factors := [2, 2, 61, 67], residues := [(2, 8174), (61, 14761), (67, 9546)] },
    { n := 16361, F := 16360, R := 1, a := 3, factors := [2, 2, 2, 5, 409], residues := [(2, 8180), (5, 1618), (409, 10344)] },
    { n := 16363, F := 16362, R := 1, a := 2, factors := [2, 3, 3, 3, 3, 101], residues := [(2, 8181), (3, 14396), (101, 16018)] },
    { n := 16369, F := 16368, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 11, 31], residues := [(2, 8184), (3, 5343), (11, 11983), (31, 4497)] },
    { n := 16381, F := 16380, R := 1, a := 2, factors := [2, 2, 3, 3, 5, 7, 13], residues := [(2, 8190), (3, 9789), (5, 6241), (7, 14329), (13, 5786)] },
    { n := 16411, F := 16410, R := 1, a := 3, factors := [2, 3, 5, 547], residues := [(2, 8205), (3, 11859), (5, 2569), (547, 16311)] },
    { n := 16417, F := 16416, R := 1, a := 10, factors := [2, 2, 2, 2, 2, 3, 3, 3, 19], residues := [(2, 8208), (3, 10758), (19, 5313)] },
    { n := 16421, F := 16420, R := 1, a := 2, factors := [2, 2, 5, 821], residues := [(2, 8210), (5, 6948), (821, 7805)] },
    { n := 16427, F := 16426, R := 1, a := 2, factors := [2, 43, 191], residues := [(2, 8213), (43, 12855), (191, 488)] },
    { n := 16433, F := 16432, R := 1, a := 3, factors := [2, 2, 2, 2, 13, 79], residues := [(2, 8216), (13, 12054), (79, 14052)] },
    { n := 16447, F := 16446, R := 1, a := 3, factors := [2, 3, 2741], residues := [(2, 8223), (3, 6899), (2741, 4541)] },
    { n := 16451, F := 16450, R := 1, a := 7, factors := [2, 5, 5, 7, 47], residues := [(2, 8225), (5, 14319), (7, 4706), (47, 9899)] },
    { n := 16453, F := 16452, R := 1, a := 2, factors := [2, 2, 3, 3, 457], residues := [(2, 8226), (3, 4928), (457, 10676)] },
    { n := 16477, F := 16476, R := 1, a := 2, factors := [2, 2, 3, 1373], residues := [(2, 8238), (3, 12951), (1373, 6285)] },
    { n := 16481, F := 16480, R := 1, a := 6, factors := [2, 2, 2, 2, 2, 5, 103], residues := [(2, 8240), (5, 16210), (103, 9751)] },
    { n := 16487, F := 16486, R := 1, a := 5, factors := [2, 8243], residues := [(2, 8243), (8243, 687)] },
    { n := 16493, F := 16492, R := 1, a := 2, factors := [2, 2, 7, 19, 31], residues := [(2, 8246), (7, 4947), (19, 15673), (31, 14885)] },
    { n := 16519, F := 16518, R := 1, a := 3, factors := [2, 3, 2753], residues := [(2, 8259), (3, 9191), (2753, 15271)] },
    { n := 16529, F := 16528, R := 1, a := 3, factors := [2, 2, 2, 2, 1033], residues := [(2, 8264), (1033, 721)] },
    { n := 16547, F := 16546, R := 1, a := 2, factors := [2, 8273], residues := [(2, 8273), (8273, 5516)] },
    { n := 16553, F := 16552, R := 1, a := 3, factors := [2, 2, 2, 2069], residues := [(2, 8276), (2069, 9142)] },
    { n := 16561, F := 16560, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 3, 5, 23], residues := [(2, 8280), (3, 12192), (5, 9424), (23, 11263)] },
    { n := 16567, F := 16566, R := 1, a := 3, factors := [2, 3, 11, 251], residues := [(2, 8283), (3, 7194), (11, 12033), (251, 15681)] },
    { n := 16573, F := 16572, R := 1, a := 2, factors := [2, 2, 3, 1381], residues := [(2, 8286), (3, 2450), (1381, 1975)] },
    { n := 16603, F := 16602, R := 1, a := 2, factors := [2, 3, 2767], residues := [(2, 8301), (3, 14083), (2767, 13177)] },
    { n := 16607, F := 16606, R := 1, a := 5, factors := [2, 19, 19, 23], residues := [(2, 8303), (19, 4192), (23, 10715)] },
    { n := 16619, F := 16618, R := 1, a := 2, factors := [2, 7, 1187], residues := [(2, 8309), (7, 10300), (1187, 2183)] },
    { n := 16631, F := 16630, R := 1, a := 19, factors := [2, 5, 1663], residues := [(2, 8315), (5, 15757), (1663, 14761)] },
    { n := 16633, F := 16632, R := 1, a := 15, factors := [2, 2, 2, 3, 3, 3, 7, 11], residues := [(2, 8316), (3, 4207), (7, 1523), (11, 10764)] },
    { n := 16649, F := 16648, R := 1, a := 3, factors := [2, 2, 2, 2081], residues := [(2, 8324), (2081, 4647)] },
    { n := 16651, F := 16650, R := 1, a := 2, factors := [2, 3, 3, 5, 5, 37], residues := [(2, 8325), (3, 16576), (5, 7823), (37, 7201)] },
    { n := 16657, F := 16656, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 347], residues := [(2, 8328), (3, 13340), (347, 13230)] },
    { n := 16661, F := 16660, R := 1, a := 10, factors := [2, 2, 5, 7, 7, 17], residues := [(2, 8330), (5, 4536), (7, 7229), (17, 13012)] },
    { n := 16673, F := 16672, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 521], residues := [(2, 8336), (521, 5471)] },
    { n := 16691, F := 16690, R := 1, a := 6, factors := [2, 5, 1669], residues := [(2, 8345), (5, 145), (1669, 7768)] },
    { n := 16693, F := 16692, R := 1, a := 2, factors := [2, 2, 3, 13, 107], residues := [(2, 8346), (3, 3846), (13, 2840), (107, 15373)] },
    { n := 16699, F := 16698, R := 1, a := 3, factors := [2, 3, 11, 11, 23], residues := [(2, 8349), (3, 4107), (11, 8096), (23, 5182)] },
    { n := 16703, F := 16702, R := 1, a := 5, factors := [2, 7, 1193], residues := [(2, 8351), (7, 4805), (1193, 10488)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData16_valid : PocklingtonRow.Valid lowPocklingtonData16 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime16 (i : Fin lowPocklingtonData16.length) :
    Nat.Prime (lowPocklingtonData16.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData16_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15803) (q := 15809) (by
      have hp := lowPocklingtonPrime16 ⟨0, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15809) (q := 15817) (by
      have hp := lowPocklingtonPrime16 ⟨1, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15817) (q := 15823) (by
      have hp := lowPocklingtonPrime16 ⟨2, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15823) (q := 15859) (by
      have hp := lowPocklingtonPrime16 ⟨3, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15859) (q := 15877) (by
      have hp := lowPocklingtonPrime16 ⟨4, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15877) (q := 15881) (by
      have hp := lowPocklingtonPrime16 ⟨5, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15881) (q := 15887) (by
      have hp := lowPocklingtonPrime16 ⟨6, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15887) (q := 15889) (by
      have hp := lowPocklingtonPrime16 ⟨7, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part05_chain :
    DusartPrimeRowsChain 15803 15888 dusartPrimeRows_15527_16318_part05 := by
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
def dusartPrimeRows_15527_16318_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15889) (q := 15901) (by
      have hp := lowPocklingtonPrime16 ⟨8, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15901) (q := 15907) (by
      have hp := lowPocklingtonPrime16 ⟨9, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15907) (q := 15913) (by
      have hp := lowPocklingtonPrime16 ⟨10, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15913) (q := 15919) (by
      have hp := lowPocklingtonPrime16 ⟨11, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15919) (q := 15923) (by
      have hp := lowPocklingtonPrime16 ⟨12, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15923) (q := 15937) (by
      have hp := lowPocklingtonPrime16 ⟨13, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15937) (q := 15959) (by
      have hp := lowPocklingtonPrime16 ⟨14, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15959) (q := 15971) (by
      have hp := lowPocklingtonPrime16 ⟨15, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part06_chain :
    DusartPrimeRowsChain 15889 15970 dusartPrimeRows_15527_16318_part06 := by
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
def dusartPrimeRows_15527_16318_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15971) (q := 15973) (by
      have hp := lowPocklingtonPrime16 ⟨16, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15973) (q := 15991) (by
      have hp := lowPocklingtonPrime16 ⟨17, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15991) (q := 16001) (by
      have hp := lowPocklingtonPrime16 ⟨18, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16001) (q := 16007) (by
      have hp := lowPocklingtonPrime16 ⟨19, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16007) (q := 16033) (by
      have hp := lowPocklingtonPrime16 ⟨20, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16033) (q := 16057) (by
      have hp := lowPocklingtonPrime16 ⟨21, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16057) (q := 16061) (by
      have hp := lowPocklingtonPrime16 ⟨22, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16061) (q := 16063) (by
      have hp := lowPocklingtonPrime16 ⟨23, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part07_chain :
    DusartPrimeRowsChain 15971 16062 dusartPrimeRows_15527_16318_part07 := by
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
def dusartPrimeRows_15527_16318_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16063) (q := 16067) (by
      have hp := lowPocklingtonPrime16 ⟨24, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16067) (q := 16069) (by
      have hp := lowPocklingtonPrime16 ⟨25, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16069) (q := 16073) (by
      have hp := lowPocklingtonPrime16 ⟨26, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16073) (q := 16087) (by
      have hp := lowPocklingtonPrime16 ⟨27, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16087) (q := 16091) (by
      have hp := lowPocklingtonPrime16 ⟨28, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16091) (q := 16097) (by
      have hp := lowPocklingtonPrime16 ⟨29, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16097) (q := 16103) (by
      have hp := lowPocklingtonPrime16 ⟨30, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16103) (q := 16111) (by
      have hp := lowPocklingtonPrime16 ⟨31, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part08_chain :
    DusartPrimeRowsChain 16063 16110 dusartPrimeRows_15527_16318_part08 := by
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
def dusartPrimeRows_15527_16318_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16111) (q := 16127) (by
      have hp := lowPocklingtonPrime16 ⟨32, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16127) (q := 16139) (by
      have hp := lowPocklingtonPrime16 ⟨33, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16139) (q := 16141) (by
      have hp := lowPocklingtonPrime16 ⟨34, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16141) (q := 16183) (by
      have hp := lowPocklingtonPrime16 ⟨35, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16183) (q := 16187) (by
      have hp := lowPocklingtonPrime16 ⟨36, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16187) (q := 16189) (by
      have hp := lowPocklingtonPrime16 ⟨37, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16189) (q := 16193) (by
      have hp := lowPocklingtonPrime16 ⟨38, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16193) (q := 16217) (by
      have hp := lowPocklingtonPrime16 ⟨39, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part09_chain :
    DusartPrimeRowsChain 16111 16216 dusartPrimeRows_15527_16318_part09 := by
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
def dusartPrimeRows_15527_16318_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16217) (q := 16223) (by
      have hp := lowPocklingtonPrime16 ⟨40, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16223) (q := 16229) (by
      have hp := lowPocklingtonPrime16 ⟨41, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16229) (q := 16231) (by
      have hp := lowPocklingtonPrime16 ⟨42, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16231) (q := 16249) (by
      have hp := lowPocklingtonPrime16 ⟨43, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16249) (q := 16253) (by
      have hp := lowPocklingtonPrime16 ⟨44, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16253) (q := 16267) (by
      have hp := lowPocklingtonPrime16 ⟨45, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16267) (q := 16273) (by
      have hp := lowPocklingtonPrime16 ⟨46, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16273) (q := 16301) (by
      have hp := lowPocklingtonPrime16 ⟨47, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part10_chain :
    DusartPrimeRowsChain 16217 16300 dusartPrimeRows_15527_16318_part10 := by
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
def dusartPrimeRows_15527_16318_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16301) (q := 16319) (by
      have hp := lowPocklingtonPrime16 ⟨48, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part11_chain :
    DusartPrimeRowsChain 16301 16318 dusartPrimeRows_15527_16318_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_16317, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16319) (q := 16333) (by
      have hp := lowPocklingtonPrime16 ⟨49, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16333) (q := 16339) (by
      have hp := lowPocklingtonPrime16 ⟨50, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16339) (q := 16349) (by
      have hp := lowPocklingtonPrime16 ⟨51, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16349) (q := 16361) (by
      have hp := lowPocklingtonPrime16 ⟨52, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16361) (q := 16363) (by
      have hp := lowPocklingtonPrime16 ⟨53, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16363) (q := 16369) (by
      have hp := lowPocklingtonPrime16 ⟨54, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16369) (q := 16381) (by
      have hp := lowPocklingtonPrime16 ⟨55, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16381) (q := 16411) (by
      have hp := lowPocklingtonPrime16 ⟨56, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part01_chain :
    DusartPrimeRowsChain 16319 16410 dusartPrimeRows_16319_17158_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_17154, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16411) (q := 16417) (by
      have hp := lowPocklingtonPrime16 ⟨57, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16417) (q := 16421) (by
      have hp := lowPocklingtonPrime16 ⟨58, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16421) (q := 16427) (by
      have hp := lowPocklingtonPrime16 ⟨59, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16427) (q := 16433) (by
      have hp := lowPocklingtonPrime16 ⟨60, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16433) (q := 16447) (by
      have hp := lowPocklingtonPrime16 ⟨61, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16447) (q := 16451) (by
      have hp := lowPocklingtonPrime16 ⟨62, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16451) (q := 16453) (by
      have hp := lowPocklingtonPrime16 ⟨63, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16453) (q := 16477) (by
      have hp := lowPocklingtonPrime16 ⟨64, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part02_chain :
    DusartPrimeRowsChain 16411 16476 dusartPrimeRows_16319_17158_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_17154, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16477) (q := 16481) (by
      have hp := lowPocklingtonPrime16 ⟨65, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16481) (q := 16487) (by
      have hp := lowPocklingtonPrime16 ⟨66, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16487) (q := 16493) (by
      have hp := lowPocklingtonPrime16 ⟨67, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16493) (q := 16519) (by
      have hp := lowPocklingtonPrime16 ⟨68, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16519) (q := 16529) (by
      have hp := lowPocklingtonPrime16 ⟨69, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16529) (q := 16547) (by
      have hp := lowPocklingtonPrime16 ⟨70, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16547) (q := 16553) (by
      have hp := lowPocklingtonPrime16 ⟨71, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16553) (q := 16561) (by
      have hp := lowPocklingtonPrime16 ⟨72, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part03_chain :
    DusartPrimeRowsChain 16477 16560 dusartPrimeRows_16319_17158_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_17154, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16561) (q := 16567) (by
      have hp := lowPocklingtonPrime16 ⟨73, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16567) (q := 16573) (by
      have hp := lowPocklingtonPrime16 ⟨74, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16573) (q := 16603) (by
      have hp := lowPocklingtonPrime16 ⟨75, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16603) (q := 16607) (by
      have hp := lowPocklingtonPrime16 ⟨76, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16607) (q := 16619) (by
      have hp := lowPocklingtonPrime16 ⟨77, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16619) (q := 16631) (by
      have hp := lowPocklingtonPrime16 ⟨78, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16631) (q := 16633) (by
      have hp := lowPocklingtonPrime16 ⟨79, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16633) (q := 16649) (by
      have hp := lowPocklingtonPrime16 ⟨80, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part04_chain :
    DusartPrimeRowsChain 16561 16648 dusartPrimeRows_16319_17158_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_17154, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16649) (q := 16651) (by
      have hp := lowPocklingtonPrime16 ⟨81, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16651) (q := 16657) (by
      have hp := lowPocklingtonPrime16 ⟨82, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16657) (q := 16661) (by
      have hp := lowPocklingtonPrime16 ⟨83, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16661) (q := 16673) (by
      have hp := lowPocklingtonPrime16 ⟨84, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16673) (q := 16691) (by
      have hp := lowPocklingtonPrime16 ⟨85, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16691) (q := 16693) (by
      have hp := lowPocklingtonPrime16 ⟨86, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16693) (q := 16699) (by
      have hp := lowPocklingtonPrime16 ⟨87, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16699) (q := 16703) (by
      have hp := lowPocklingtonPrime16 ⟨88, by simp [lowPocklingtonData16]⟩
      simpa [lowPocklingtonData16] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part05_chain :
    DusartPrimeRowsChain 16649 16702 dusartPrimeRows_16319_17158_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_17154, dusartPrimeRow_of_explicit_right]
