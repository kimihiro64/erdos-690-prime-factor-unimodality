import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart18


set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 19 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData19 : List PocklingtonData := [
    { n := 19949, F := 19948, R := 1, a := 2, factors := [2, 2, 4987], residues := [(2, 9974), (4987, 1330)] },
    { n := 19961, F := 19960, R := 1, a := 6, factors := [2, 2, 2, 5, 499], residues := [(2, 9980), (5, 18593), (499, 12847)] },
    { n := 19963, F := 19962, R := 1, a := 2, factors := [2, 3, 3, 1109], residues := [(2, 9981), (3, 11193), (1109, 19575)] },
    { n := 19973, F := 19972, R := 1, a := 2, factors := [2, 2, 4993], residues := [(2, 9986), (4993, 17310)] },
    { n := 19979, F := 19978, R := 1, a := 2, factors := [2, 7, 1427], residues := [(2, 9989), (7, 7432), (1427, 16351)] },
    { n := 19991, F := 19990, R := 1, a := 11, factors := [2, 5, 1999], residues := [(2, 9995), (5, 10094), (1999, 401)] },
    { n := 19993, F := 19992, R := 1, a := 10, factors := [2, 2, 2, 3, 7, 7, 17], residues := [(2, 9996), (3, 15315), (7, 3406), (17, 3057)] },
    { n := 19997, F := 19996, R := 1, a := 2, factors := [2, 2, 4999], residues := [(2, 9998), (4999, 9332)] },
    { n := 21187, F := 21186, R := 1, a := 2, factors := [2, 3, 3, 11, 107], residues := [(2, 10593), (3, 15814), (11, 14840), (107, 12367)] },
    { n := 21191, F := 21190, R := 1, a := 7, factors := [2, 5, 13, 163], residues := [(2, 10595), (5, 15486), (13, 20064), (163, 19743)] },
    { n := 21193, F := 21192, R := 1, a := 11, factors := [2, 2, 2, 3, 883], residues := [(2, 10596), (3, 6349), (883, 12932)] },
    { n := 21211, F := 21210, R := 1, a := 2, factors := [2, 3, 5, 7, 101], residues := [(2, 10605), (3, 9761), (5, 6205), (7, 391), (101, 19429)] },
    { n := 21221, F := 21220, R := 1, a := 2, factors := [2, 2, 5, 1061], residues := [(2, 10610), (5, 2914), (1061, 15405)] },
    { n := 21227, F := 21226, R := 1, a := 2, factors := [2, 10613], residues := [(2, 10613), (10613, 7076)] },
    { n := 21247, F := 21246, R := 1, a := 3, factors := [2, 3, 3541], residues := [(2, 10623), (3, 10249), (3541, 16840)] },
    { n := 21269, F := 21268, R := 1, a := 2, factors := [2, 2, 13, 409], residues := [(2, 10634), (13, 1668), (409, 7840)] },
    { n := 21277, F := 21276, R := 1, a := 6, factors := [2, 2, 3, 3, 3, 197], residues := [(2, 10638), (3, 11411), (197, 17493)] },
    { n := 21283, F := 21282, R := 1, a := 11, factors := [2, 3, 3547], residues := [(2, 10641), (3, 17823), (3547, 19323)] },
    { n := 21313, F := 21312, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 3, 3, 37], residues := [(2, 10656), (3, 16040), (37, 8113)] },
    { n := 21317, F := 21316, R := 1, a := 2, factors := [2, 2, 73, 73], residues := [(2, 10658), (73, 4052)] },
    { n := 21319, F := 21318, R := 1, a := 14, factors := [2, 3, 11, 17, 19], residues := [(2, 10659), (3, 17741), (11, 428), (17, 13796), (19, 14593)] },
    { n := 21323, F := 21322, R := 1, a := 5, factors := [2, 7, 1523], residues := [(2, 10661), (7, 12616), (1523, 7854)] },
    { n := 21341, F := 21340, R := 1, a := 2, factors := [2, 2, 5, 11, 97], residues := [(2, 10670), (5, 177), (11, 7465), (97, 8649)] },
    { n := 21347, F := 21346, R := 1, a := 2, factors := [2, 13, 821], residues := [(2, 10673), (13, 747), (821, 10413)] },
    { n := 21377, F := 21376, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 167], residues := [(2, 10688), (167, 17256)] },
    { n := 21379, F := 21378, R := 1, a := 2, factors := [2, 3, 7, 509], residues := [(2, 10689), (3, 19885), (7, 13349), (509, 1728)] },
    { n := 21383, F := 21382, R := 1, a := 5, factors := [2, 10691], residues := [(2, 10691), (10691, 891)] },
    { n := 21391, F := 21390, R := 1, a := 6, factors := [2, 3, 5, 23, 31], residues := [(2, 10695), (3, 7838), (5, 7379), (23, 15527), (31, 18913)] },
    { n := 21397, F := 21396, R := 1, a := 2, factors := [2, 2, 3, 1783], residues := [(2, 10698), (3, 21092), (1783, 18821)] },
    { n := 21401, F := 21400, R := 1, a := 3, factors := [2, 2, 2, 5, 5, 107], residues := [(2, 10700), (5, 19026), (107, 8897)] },
    { n := 21407, F := 21406, R := 1, a := 5, factors := [2, 7, 11, 139], residues := [(2, 10703), (7, 20311), (11, 4887), (139, 20612)] },
    { n := 21419, F := 21418, R := 1, a := 2, factors := [2, 10709], residues := [(2, 10709), (10709, 7140)] },
    { n := 21433, F := 21432, R := 1, a := 5, factors := [2, 2, 2, 3, 19, 47], residues := [(2, 10716), (3, 9173), (19, 14244), (47, 19404)] },
    { n := 21467, F := 21466, R := 1, a := 2, factors := [2, 10733], residues := [(2, 10733), (10733, 7156)] },
    { n := 21481, F := 21480, R := 1, a := 13, factors := [2, 2, 2, 3, 5, 179], residues := [(2, 10740), (3, 5718), (5, 21406), (179, 17671)] },
    { n := 21487, F := 21486, R := 1, a := 3, factors := [2, 3, 3581], residues := [(2, 10743), (3, 11424), (3581, 974)] },
    { n := 21491, F := 21490, R := 1, a := 2, factors := [2, 5, 7, 307], residues := [(2, 10745), (5, 17394), (7, 2984), (307, 10695)] },
    { n := 21493, F := 21492, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 199], residues := [(2, 10746), (3, 6316), (199, 19339)] },
    { n := 21499, F := 21498, R := 1, a := 3, factors := [2, 3, 3583], residues := [(2, 10749), (3, 2054), (3583, 7944)] },
    { n := 21503, F := 21502, R := 1, a := 5, factors := [2, 13, 827], residues := [(2, 10751), (13, 15718), (827, 15910)] },
    { n := 21517, F := 21516, R := 1, a := 5, factors := [2, 2, 3, 11, 163], residues := [(2, 10758), (3, 13614), (11, 11203), (163, 11816)] },
    { n := 21521, F := 21520, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 269], residues := [(2, 10760), (5, 9195), (269, 12060)] },
    { n := 21523, F := 21522, R := 1, a := 2, factors := [2, 3, 17, 211], residues := [(2, 10761), (3, 10357), (17, 10195), (211, 1610)] },
    { n := 21529, F := 21528, R := 1, a := 11, factors := [2, 2, 2, 3, 3, 13, 23], residues := [(2, 10764), (3, 13028), (13, 20321), (23, 4011)] },
    { n := 21557, F := 21556, R := 1, a := 2, factors := [2, 2, 17, 317], residues := [(2, 10778), (17, 18082), (317, 16310)] },
    { n := 21559, F := 21558, R := 1, a := 15, factors := [2, 3, 3593], residues := [(2, 10779), (3, 1993), (3593, 20754)] },
    { n := 21563, F := 21562, R := 1, a := 2, factors := [2, 10781], residues := [(2, 10781), (10781, 7188)] },
    { n := 21569, F := 21568, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 337], residues := [(2, 10784), (337, 15354)] },
    { n := 21577, F := 21576, R := 1, a := 5, factors := [2, 2, 2, 3, 29, 31], residues := [(2, 10788), (3, 12086), (29, 5426), (31, 10815)] },
    { n := 21587, F := 21586, R := 1, a := 2, factors := [2, 43, 251], residues := [(2, 10793), (43, 14498), (251, 19534)] },
    { n := 21589, F := 21588, R := 1, a := 2, factors := [2, 2, 3, 7, 257], residues := [(2, 10794), (3, 19378), (7, 9916), (257, 628)] },
    { n := 21599, F := 21598, R := 1, a := 7, factors := [2, 10799], residues := [(2, 10799), (10799, 450)] },
    { n := 21601, F := 21600, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 3, 3, 3, 5, 5], residues := [(2, 10800), (3, 13005), (5, 11701)] },
    { n := 21611, F := 21610, R := 1, a := 2, factors := [2, 5, 2161], residues := [(2, 10805), (5, 15909), (2161, 21442)] },
    { n := 21613, F := 21612, R := 1, a := 2, factors := [2, 2, 3, 1801], residues := [(2, 10806), (3, 7974), (1801, 19201)] },
    { n := 21617, F := 21616, R := 1, a := 3, factors := [2, 2, 2, 2, 7, 193], residues := [(2, 10808), (7, 3158), (193, 13459)] },
    { n := 21647, F := 21646, R := 1, a := 5, factors := [2, 79, 137], residues := [(2, 10823), (79, 9293), (137, 15464)] },
    { n := 21649, F := 21648, R := 1, a := 14, factors := [2, 2, 2, 2, 3, 11, 41], residues := [(2, 10824), (3, 2346), (11, 20718), (41, 9133)] },
    { n := 21661, F := 21660, R := 1, a := 2, factors := [2, 2, 3, 5, 19, 19], residues := [(2, 10830), (3, 19567), (5, 21184), (19, 21572)] },
    { n := 21673, F := 21672, R := 1, a := 10, factors := [2, 2, 2, 3, 3, 7, 43], residues := [(2, 10836), (3, 7094), (7, 12047), (43, 14017)] },
    { n := 21683, F := 21682, R := 1, a := 2, factors := [2, 37, 293], residues := [(2, 10841), (37, 20284), (293, 14982)] },
    { n := 21701, F := 21700, R := 1, a := 2, factors := [2, 2, 5, 5, 7, 31], residues := [(2, 10850), (5, 15281), (7, 10822), (31, 15946)] },
    { n := 21713, F := 21712, R := 1, a := 3, factors := [2, 2, 2, 2, 23, 59], residues := [(2, 10856), (23, 6167), (59, 3827)] },
    { n := 21727, F := 21726, R := 1, a := 3, factors := [2, 3, 3, 17, 71], residues := [(2, 10863), (3, 2485), (17, 18663), (71, 19845)] },
    { n := 21737, F := 21736, R := 1, a := 6, factors := [2, 2, 2, 11, 13, 19], residues := [(2, 10868), (11, 7760), (13, 13561), (19, 5733)] },
    { n := 21739, F := 21738, R := 1, a := 2, factors := [2, 3, 3623], residues := [(2, 10869), (3, 12233), (3623, 16218)] },
    { n := 21751, F := 21750, R := 1, a := 3, factors := [2, 3, 5, 5, 5, 29], residues := [(2, 10875), (3, 19070), (5, 18854), (29, 20340)] },
    { n := 21757, F := 21756, R := 1, a := 5, factors := [2, 2, 3, 7, 7, 37], residues := [(2, 10878), (3, 14455), (7, 11136), (37, 10797)] },
    { n := 21767, F := 21766, R := 1, a := 5, factors := [2, 10883], residues := [(2, 10883), (10883, 907)] },
    { n := 21773, F := 21772, R := 1, a := 2, factors := [2, 2, 5443], residues := [(2, 10886), (5443, 18870)] },
    { n := 21787, F := 21786, R := 1, a := 23, factors := [2, 3, 3631], residues := [(2, 10893), (3, 20308), (3631, 823)] },
    { n := 21799, F := 21798, R := 1, a := 7, factors := [2, 3, 3, 7, 173], residues := [(2, 10899), (3, 1659), (7, 12191), (173, 15652)] },
    { n := 21803, F := 21802, R := 1, a := 2, factors := [2, 11, 991], residues := [(2, 10901), (11, 5777), (991, 10208)] },
    { n := 21817, F := 21816, R := 1, a := 7, factors := [2, 2, 2, 3, 3, 3, 101], residues := [(2, 10908), (3, 21003), (101, 2906)] },
    { n := 21821, F := 21820, R := 1, a := 2, factors := [2, 2, 5, 1091], residues := [(2, 10910), (5, 7500), (1091, 14940)] },
    { n := 21839, F := 21838, R := 1, a := 11, factors := [2, 61, 179], residues := [(2, 10919), (61, 7033), (179, 8208)] },
    { n := 21841, F := 21840, R := 1, a := 11, factors := [2, 2, 2, 2, 3, 5, 7, 13], residues := [(2, 10920), (3, 11717), (5, 7116), (7, 6835), (13, 5776)] },
    { n := 21851, F := 21850, R := 1, a := 6, factors := [2, 5, 5, 19, 23], residues := [(2, 10925), (5, 16804), (19, 3402), (23, 2445)] },
    { n := 21859, F := 21858, R := 1, a := 2, factors := [2, 3, 3643], residues := [(2, 10929), (3, 19322), (3643, 11103)] },
    { n := 21863, F := 21862, R := 1, a := 5, factors := [2, 17, 643], residues := [(2, 10931), (17, 8620), (643, 4355)] },
    { n := 21871, F := 21870, R := 1, a := 6, factors := [2, 3, 3, 3, 3, 3, 3, 3, 5], residues := [(2, 10935), (3, 17968), (5, 12548)] },
    { n := 21881, F := 21880, R := 1, a := 3, factors := [2, 2, 2, 5, 547], residues := [(2, 10940), (5, 387), (547, 598)] },
    { n := 21893, F := 21892, R := 1, a := 2, factors := [2, 2, 13, 421], residues := [(2, 10946), (13, 9950), (421, 17863)] },
    { n := 21911, F := 21910, R := 1, a := 13, factors := [2, 5, 7, 313], residues := [(2, 10955), (5, 2413), (7, 6172), (313, 5511)] },
    { n := 21929, F := 21928, R := 1, a := 3, factors := [2, 2, 2, 2741], residues := [(2, 10964), (2741, 8795)] },
    { n := 21937, F := 21936, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 457], residues := [(2, 10968), (3, 4404), (457, 20011)] },
    { n := 21943, F := 21942, R := 1, a := 5, factors := [2, 3, 3, 23, 53], residues := [(2, 10971), (3, 3122), (23, 4650), (53, 15752)] },
    { n := 21961, F := 21960, R := 1, a := 17, factors := [2, 2, 2, 3, 3, 5, 61], residues := [(2, 10980), (3, 9974), (5, 13413), (61, 17855)] },
    { n := 21977, F := 21976, R := 1, a := 3, factors := [2, 2, 2, 41, 67], residues := [(2, 10988), (41, 7023), (67, 12528)] },
    { n := 21991, F := 21990, R := 1, a := 3, factors := [2, 3, 5, 733], residues := [(2, 10995), (3, 10016), (5, 2477), (733, 11053)] },
    { n := 21997, F := 21996, R := 1, a := 7, factors := [2, 2, 3, 3, 13, 47], residues := [(2, 10998), (3, 18128), (13, 1430), (47, 8780)] },
    { n := 22003, F := 22002, R := 1, a := 2, factors := [2, 3, 19, 193], residues := [(2, 11001), (3, 15526), (19, 290), (193, 18761)] },
    { n := 22013, F := 22012, R := 1, a := 2, factors := [2, 2, 5503], residues := [(2, 11006), (5503, 19078)] },
    { n := 22027, F := 22026, R := 1, a := 3, factors := [2, 3, 3671], residues := [(2, 11013), (3, 8885), (3671, 3298)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData19_valid : PocklingtonRow.Valid lowPocklingtonData19 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime19 (i : Fin lowPocklingtonData19.length) :
    Nat.Prime (lowPocklingtonData19.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData19_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21179) (q := 21187) (by
      have hp := lowPocklingtonPrime19 ⟨8, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21187) (q := 21191) (by
      have hp := lowPocklingtonPrime19 ⟨9, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21191) (q := 21193) (by
      have hp := lowPocklingtonPrime19 ⟨10, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21193) (q := 21211) (by
      have hp := lowPocklingtonPrime19 ⟨11, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21211) (q := 21221) (by
      have hp := lowPocklingtonPrime19 ⟨12, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21221) (q := 21227) (by
      have hp := lowPocklingtonPrime19 ⟨13, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21227) (q := 21247) (by
      have hp := lowPocklingtonPrime19 ⟨14, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21247) (q := 21269) (by
      have hp := lowPocklingtonPrime19 ⟨15, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part04_chain :
    DusartPrimeRowsChain 21179 21268 dusartPrimeRows_20959_22026_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21269) (q := 21277) (by
      have hp := lowPocklingtonPrime19 ⟨16, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21277) (q := 21283) (by
      have hp := lowPocklingtonPrime19 ⟨17, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21283) (q := 21313) (by
      have hp := lowPocklingtonPrime19 ⟨18, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21313) (q := 21317) (by
      have hp := lowPocklingtonPrime19 ⟨19, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21317) (q := 21319) (by
      have hp := lowPocklingtonPrime19 ⟨20, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21319) (q := 21323) (by
      have hp := lowPocklingtonPrime19 ⟨21, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21323) (q := 21341) (by
      have hp := lowPocklingtonPrime19 ⟨22, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21341) (q := 21347) (by
      have hp := lowPocklingtonPrime19 ⟨23, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part05_chain :
    DusartPrimeRowsChain 21269 21346 dusartPrimeRows_20959_22026_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21347) (q := 21377) (by
      have hp := lowPocklingtonPrime19 ⟨24, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21377) (q := 21379) (by
      have hp := lowPocklingtonPrime19 ⟨25, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21379) (q := 21383) (by
      have hp := lowPocklingtonPrime19 ⟨26, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21383) (q := 21391) (by
      have hp := lowPocklingtonPrime19 ⟨27, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21391) (q := 21397) (by
      have hp := lowPocklingtonPrime19 ⟨28, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21397) (q := 21401) (by
      have hp := lowPocklingtonPrime19 ⟨29, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21401) (q := 21407) (by
      have hp := lowPocklingtonPrime19 ⟨30, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21407) (q := 21419) (by
      have hp := lowPocklingtonPrime19 ⟨31, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part06_chain :
    DusartPrimeRowsChain 21347 21418 dusartPrimeRows_20959_22026_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21419) (q := 21433) (by
      have hp := lowPocklingtonPrime19 ⟨32, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21433) (q := 21467) (by
      have hp := lowPocklingtonPrime19 ⟨33, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21467) (q := 21481) (by
      have hp := lowPocklingtonPrime19 ⟨34, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21481) (q := 21487) (by
      have hp := lowPocklingtonPrime19 ⟨35, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21487) (q := 21491) (by
      have hp := lowPocklingtonPrime19 ⟨36, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21491) (q := 21493) (by
      have hp := lowPocklingtonPrime19 ⟨37, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21493) (q := 21499) (by
      have hp := lowPocklingtonPrime19 ⟨38, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21499) (q := 21503) (by
      have hp := lowPocklingtonPrime19 ⟨39, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part07_chain :
    DusartPrimeRowsChain 21419 21502 dusartPrimeRows_20959_22026_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21503) (q := 21517) (by
      have hp := lowPocklingtonPrime19 ⟨40, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21517) (q := 21521) (by
      have hp := lowPocklingtonPrime19 ⟨41, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21521) (q := 21523) (by
      have hp := lowPocklingtonPrime19 ⟨42, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21523) (q := 21529) (by
      have hp := lowPocklingtonPrime19 ⟨43, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21529) (q := 21557) (by
      have hp := lowPocklingtonPrime19 ⟨44, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21557) (q := 21559) (by
      have hp := lowPocklingtonPrime19 ⟨45, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21559) (q := 21563) (by
      have hp := lowPocklingtonPrime19 ⟨46, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21563) (q := 21569) (by
      have hp := lowPocklingtonPrime19 ⟨47, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part08_chain :
    DusartPrimeRowsChain 21503 21568 dusartPrimeRows_20959_22026_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21569) (q := 21577) (by
      have hp := lowPocklingtonPrime19 ⟨48, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21577) (q := 21587) (by
      have hp := lowPocklingtonPrime19 ⟨49, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21587) (q := 21589) (by
      have hp := lowPocklingtonPrime19 ⟨50, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21589) (q := 21599) (by
      have hp := lowPocklingtonPrime19 ⟨51, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21599) (q := 21601) (by
      have hp := lowPocklingtonPrime19 ⟨52, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21601) (q := 21611) (by
      have hp := lowPocklingtonPrime19 ⟨53, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21611) (q := 21613) (by
      have hp := lowPocklingtonPrime19 ⟨54, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21613) (q := 21617) (by
      have hp := lowPocklingtonPrime19 ⟨55, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part09_chain :
    DusartPrimeRowsChain 21569 21616 dusartPrimeRows_20959_22026_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21617) (q := 21647) (by
      have hp := lowPocklingtonPrime19 ⟨56, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21647) (q := 21649) (by
      have hp := lowPocklingtonPrime19 ⟨57, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21649) (q := 21661) (by
      have hp := lowPocklingtonPrime19 ⟨58, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21661) (q := 21673) (by
      have hp := lowPocklingtonPrime19 ⟨59, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21673) (q := 21683) (by
      have hp := lowPocklingtonPrime19 ⟨60, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21683) (q := 21701) (by
      have hp := lowPocklingtonPrime19 ⟨61, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21701) (q := 21713) (by
      have hp := lowPocklingtonPrime19 ⟨62, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21713) (q := 21727) (by
      have hp := lowPocklingtonPrime19 ⟨63, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part10_chain :
    DusartPrimeRowsChain 21617 21726 dusartPrimeRows_20959_22026_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21727) (q := 21737) (by
      have hp := lowPocklingtonPrime19 ⟨64, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21737) (q := 21739) (by
      have hp := lowPocklingtonPrime19 ⟨65, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21739) (q := 21751) (by
      have hp := lowPocklingtonPrime19 ⟨66, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21751) (q := 21757) (by
      have hp := lowPocklingtonPrime19 ⟨67, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21757) (q := 21767) (by
      have hp := lowPocklingtonPrime19 ⟨68, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21767) (q := 21773) (by
      have hp := lowPocklingtonPrime19 ⟨69, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21773) (q := 21787) (by
      have hp := lowPocklingtonPrime19 ⟨70, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21787) (q := 21799) (by
      have hp := lowPocklingtonPrime19 ⟨71, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part11_chain :
    DusartPrimeRowsChain 21727 21798 dusartPrimeRows_20959_22026_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21799) (q := 21803) (by
      have hp := lowPocklingtonPrime19 ⟨72, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21803) (q := 21817) (by
      have hp := lowPocklingtonPrime19 ⟨73, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21817) (q := 21821) (by
      have hp := lowPocklingtonPrime19 ⟨74, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21821) (q := 21839) (by
      have hp := lowPocklingtonPrime19 ⟨75, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21839) (q := 21841) (by
      have hp := lowPocklingtonPrime19 ⟨76, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21841) (q := 21851) (by
      have hp := lowPocklingtonPrime19 ⟨77, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21851) (q := 21859) (by
      have hp := lowPocklingtonPrime19 ⟨78, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21859) (q := 21863) (by
      have hp := lowPocklingtonPrime19 ⟨79, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part12_chain :
    DusartPrimeRowsChain 21799 21862 dusartPrimeRows_20959_22026_part12 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21863) (q := 21871) (by
      have hp := lowPocklingtonPrime19 ⟨80, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21871) (q := 21881) (by
      have hp := lowPocklingtonPrime19 ⟨81, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21881) (q := 21893) (by
      have hp := lowPocklingtonPrime19 ⟨82, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21893) (q := 21911) (by
      have hp := lowPocklingtonPrime19 ⟨83, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21911) (q := 21929) (by
      have hp := lowPocklingtonPrime19 ⟨84, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21929) (q := 21937) (by
      have hp := lowPocklingtonPrime19 ⟨85, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21937) (q := 21943) (by
      have hp := lowPocklingtonPrime19 ⟨86, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21943) (q := 21961) (by
      have hp := lowPocklingtonPrime19 ⟨87, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part13_chain :
    DusartPrimeRowsChain 21863 21960 dusartPrimeRows_20959_22026_part13 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part14 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21961) (q := 21977) (by
      have hp := lowPocklingtonPrime19 ⟨88, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21977) (q := 21991) (by
      have hp := lowPocklingtonPrime19 ⟨89, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21991) (q := 21997) (by
      have hp := lowPocklingtonPrime19 ⟨90, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21997) (q := 22003) (by
      have hp := lowPocklingtonPrime19 ⟨91, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 22003) (q := 22013) (by
      have hp := lowPocklingtonPrime19 ⟨92, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 22013) (q := 22027) (by
      have hp := lowPocklingtonPrime19 ⟨93, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part14_chain :
    DusartPrimeRowsChain 21961 22026 dusartPrimeRows_20959_22026_part14 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 19937) (q := 19949) (by
      have hp := lowPocklingtonPrime19 ⟨0, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19949) (q := 19961) (by
      have hp := lowPocklingtonPrime19 ⟨1, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19961) (q := 19963) (by
      have hp := lowPocklingtonPrime19 ⟨2, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19963) (q := 19973) (by
      have hp := lowPocklingtonPrime19 ⟨3, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19973) (q := 19979) (by
      have hp := lowPocklingtonPrime19 ⟨4, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19979) (q := 19991) (by
      have hp := lowPocklingtonPrime19 ⟨5, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19991) (q := 19993) (by
      have hp := lowPocklingtonPrime19 ⟨6, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19993) (q := 19997) (by
      have hp := lowPocklingtonPrime19 ⟨7, by simp [lowPocklingtonData19]⟩
      simpa [lowPocklingtonData19] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part01_chain :
    DusartPrimeRowsChain 19937 19996 dusartPrimeRows_19937_20958_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_20952, dusartPrimeRow_of_explicit_right]
