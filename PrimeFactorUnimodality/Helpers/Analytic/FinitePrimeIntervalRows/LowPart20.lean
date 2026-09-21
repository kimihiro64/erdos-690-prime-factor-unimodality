import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart19


set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 20 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData20 : List PocklingtonData := [
    { n := 20011, F := 20010, R := 1, a := 12, factors := [2, 3, 5, 23, 29], residues := [(2, 10005), (3, 10183), (5, 4048), (23, 6463), (29, 3840)] },
    { n := 20021, F := 20020, R := 1, a := 3, factors := [2, 2, 5, 7, 11, 13], residues := [(2, 10010), (5, 1923), (7, 3469), (11, 8566), (13, 6039)] },
    { n := 20023, F := 20022, R := 1, a := 3, factors := [2, 3, 47, 71], residues := [(2, 10011), (3, 6721), (47, 5232), (71, 8693)] },
    { n := 20029, F := 20028, R := 1, a := 2, factors := [2, 2, 3, 1669], residues := [(2, 10014), (3, 11111), (1669, 494)] },
    { n := 20047, F := 20046, R := 1, a := 3, factors := [2, 3, 13, 257], residues := [(2, 10023), (3, 13194), (13, 9866), (257, 16647)] },
    { n := 20051, F := 20050, R := 1, a := 2, factors := [2, 5, 5, 401], residues := [(2, 10025), (5, 4472), (401, 13793)] },
    { n := 20063, F := 20062, R := 1, a := 5, factors := [2, 7, 1433], residues := [(2, 10031), (7, 5916), (1433, 4856)] },
    { n := 20071, F := 20070, R := 1, a := 3, factors := [2, 3, 3, 5, 223], residues := [(2, 10035), (3, 8285), (5, 3700), (223, 17940)] },
    { n := 20089, F := 20088, R := 1, a := 7, factors := [2, 2, 2, 3, 3, 3, 3, 31], residues := [(2, 10044), (3, 3974), (31, 6817)] },
    { n := 20101, F := 20100, R := 1, a := 6, factors := [2, 2, 3, 5, 5, 67], residues := [(2, 10050), (3, 17996), (5, 9511), (67, 3422)] },
    { n := 20107, F := 20106, R := 1, a := 2, factors := [2, 3, 3, 1117], residues := [(2, 10053), (3, 4380), (1117, 10615)] },
    { n := 20113, F := 20112, R := 1, a := 10, factors := [2, 2, 2, 2, 3, 419], residues := [(2, 10056), (3, 11584), (419, 9731)] },
    { n := 20117, F := 20116, R := 1, a := 2, factors := [2, 2, 47, 107], residues := [(2, 10058), (47, 6602), (107, 14613)] },
    { n := 20123, F := 20122, R := 1, a := 2, factors := [2, 10061], residues := [(2, 10061), (10061, 6708)] },
    { n := 20129, F := 20128, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 17, 37], residues := [(2, 10064), (17, 15787), (37, 11635)] },
    { n := 20143, F := 20142, R := 1, a := 5, factors := [2, 3, 3, 3, 373], residues := [(2, 10071), (3, 6839), (373, 7643)] },
    { n := 20147, F := 20146, R := 1, a := 6, factors := [2, 7, 1439], residues := [(2, 10073), (7, 1299), (1439, 12371)] },
    { n := 20149, F := 20148, R := 1, a := 2, factors := [2, 2, 3, 23, 73], residues := [(2, 10074), (3, 4129), (23, 10732), (73, 4443)] },
    { n := 20161, F := 20160, R := 1, a := 13, factors := [2, 2, 2, 2, 2, 2, 3, 3, 5, 7], residues := [(2, 10080), (3, 8778), (5, 4369), (7, 7310)] },
    { n := 20173, F := 20172, R := 1, a := 2, factors := [2, 2, 3, 41, 41], residues := [(2, 10086), (3, 10045), (41, 5767)] },
    { n := 20177, F := 20176, R := 1, a := 3, factors := [2, 2, 2, 2, 13, 97], residues := [(2, 10088), (13, 6366), (97, 1102)] },
    { n := 20183, F := 20182, R := 1, a := 5, factors := [2, 10091], residues := [(2, 10091), (10091, 841)] },
    { n := 20201, F := 20200, R := 1, a := 6, factors := [2, 2, 2, 5, 5, 101], residues := [(2, 10100), (5, 9752), (101, 4621)] },
    { n := 20219, F := 20218, R := 1, a := 2, factors := [2, 11, 919], residues := [(2, 10109), (11, 16500), (919, 14541)] },
    { n := 20231, F := 20230, R := 1, a := 29, factors := [2, 5, 7, 17, 17], residues := [(2, 10115), (5, 1399), (7, 17148), (17, 5337)] },
    { n := 20233, F := 20232, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 281], residues := [(2, 10116), (3, 19074), (281, 18809)] },
    { n := 20249, F := 20248, R := 1, a := 3, factors := [2, 2, 2, 2531], residues := [(2, 10124), (2531, 4911)] },
    { n := 20261, F := 20260, R := 1, a := 2, factors := [2, 2, 5, 1013], residues := [(2, 10130), (5, 2364), (1013, 10984)] },
    { n := 20269, F := 20268, R := 1, a := 2, factors := [2, 2, 3, 3, 563], residues := [(2, 10134), (3, 4932), (563, 1169)] },
    { n := 20287, F := 20286, R := 1, a := 5, factors := [2, 3, 3, 7, 7, 23], residues := [(2, 10143), (3, 16027), (7, 8350), (23, 16878)] },
    { n := 20297, F := 20296, R := 1, a := 3, factors := [2, 2, 2, 43, 59], residues := [(2, 10148), (43, 8084), (59, 10825)] },
    { n := 20323, F := 20322, R := 1, a := 2, factors := [2, 3, 3, 1129], residues := [(2, 10161), (3, 3301), (1129, 3430)] },
    { n := 20327, F := 20326, R := 1, a := 5, factors := [2, 10163], residues := [(2, 10163), (10163, 847)] },
    { n := 20333, F := 20332, R := 1, a := 3, factors := [2, 2, 13, 17, 23], residues := [(2, 10166), (13, 2081), (17, 5054), (23, 16253)] },
    { n := 20341, F := 20340, R := 1, a := 2, factors := [2, 2, 3, 3, 5, 113], residues := [(2, 10170), (3, 19555), (5, 9816), (113, 8869)] },
    { n := 20347, F := 20346, R := 1, a := 3, factors := [2, 3, 3391], residues := [(2, 10173), (3, 13897), (3391, 18698)] },
    { n := 20353, F := 20352, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 2, 3, 53], residues := [(2, 10176), (3, 19058), (53, 3547)] },
    { n := 20357, F := 20356, R := 1, a := 2, factors := [2, 2, 7, 727], residues := [(2, 10178), (7, 75), (727, 17546)] },
    { n := 20359, F := 20358, R := 1, a := 11, factors := [2, 3, 3, 3, 13, 29], residues := [(2, 10179), (3, 9006), (13, 2012), (29, 11143)] },
    { n := 20369, F := 20368, R := 1, a := 3, factors := [2, 2, 2, 2, 19, 67], residues := [(2, 10184), (19, 18587), (67, 12271)] },
    { n := 20389, F := 20388, R := 1, a := 6, factors := [2, 2, 3, 1699], residues := [(2, 10194), (3, 7588), (1699, 9215)] },
    { n := 20393, F := 20392, R := 1, a := 3, factors := [2, 2, 2, 2549], residues := [(2, 10196), (2549, 10268)] },
    { n := 20399, F := 20398, R := 1, a := 7, factors := [2, 7, 31, 47], residues := [(2, 10199), (7, 10839), (31, 18124), (47, 11188)] },
    { n := 20407, F := 20406, R := 1, a := 5, factors := [2, 3, 19, 179], residues := [(2, 10203), (3, 11712), (19, 17961), (179, 14218)] },
    { n := 20411, F := 20410, R := 1, a := 6, factors := [2, 5, 13, 157], residues := [(2, 10205), (5, 4446), (13, 9910), (157, 12686)] },
    { n := 20431, F := 20430, R := 1, a := 3, factors := [2, 3, 3, 5, 227], residues := [(2, 10215), (3, 2930), (5, 1686), (227, 2635)] },
    { n := 20441, F := 20440, R := 1, a := 3, factors := [2, 2, 2, 5, 7, 73], residues := [(2, 10220), (5, 16809), (7, 432), (73, 13826)] },
    { n := 20443, F := 20442, R := 1, a := 2, factors := [2, 3, 3407], residues := [(2, 10221), (3, 19114), (3407, 649)] },
    { n := 20477, F := 20476, R := 1, a := 2, factors := [2, 2, 5119], residues := [(2, 10238), (5119, 9556)] },
    { n := 20479, F := 20478, R := 1, a := 3, factors := [2, 3, 3413], residues := [(2, 10239), (3, 4355), (3413, 19832)] },
    { n := 20483, F := 20482, R := 1, a := 5, factors := [2, 7, 7, 11, 19], residues := [(2, 10241), (7, 3178), (11, 13475), (19, 13169)] },
    { n := 20507, F := 20506, R := 1, a := 2, factors := [2, 10253], residues := [(2, 10253), (10253, 6836)] },
    { n := 20509, F := 20508, R := 1, a := 2, factors := [2, 2, 3, 1709], residues := [(2, 10254), (3, 2154), (1709, 15080)] },
    { n := 20521, F := 20520, R := 1, a := 11, factors := [2, 2, 2, 3, 3, 3, 5, 19], residues := [(2, 10260), (3, 7012), (5, 15971), (19, 11290)] },
    { n := 20533, F := 20532, R := 1, a := 2, factors := [2, 2, 3, 29, 59], residues := [(2, 10266), (3, 19990), (29, 11583), (59, 7719)] },
    { n := 20543, F := 20542, R := 1, a := 5, factors := [2, 10271], residues := [(2, 10271), (10271, 856)] },
    { n := 20549, F := 20548, R := 1, a := 2, factors := [2, 2, 11, 467], residues := [(2, 10274), (11, 5660), (467, 13173)] },
    { n := 20551, F := 20550, R := 1, a := 3, factors := [2, 3, 5, 5, 137], residues := [(2, 10275), (3, 3570), (5, 7891), (137, 14162)] },
    { n := 20563, F := 20562, R := 1, a := 3, factors := [2, 3, 23, 149], residues := [(2, 10281), (3, 5832), (23, 8692), (149, 11353)] },
    { n := 20593, F := 20592, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 3, 11, 13], residues := [(2, 10296), (3, 6816), (11, 1301), (13, 1862)] },
    { n := 20599, F := 20598, R := 1, a := 3, factors := [2, 3, 3433], residues := [(2, 10299), (3, 4593), (3433, 5461)] },
    { n := 20611, F := 20610, R := 1, a := 2, factors := [2, 3, 3, 5, 229], residues := [(2, 10305), (3, 1364), (5, 19094), (229, 13083)] },
    { n := 20627, F := 20626, R := 1, a := 2, factors := [2, 10313], residues := [(2, 10313), (10313, 6876)] },
    { n := 20639, F := 20638, R := 1, a := 11, factors := [2, 17, 607], residues := [(2, 10319), (17, 20403), (607, 8230)] },
    { n := 20641, F := 20640, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 3, 5, 43], residues := [(2, 10320), (3, 9887), (5, 17671), (43, 18608)] },
    { n := 20663, F := 20662, R := 1, a := 5, factors := [2, 10331], residues := [(2, 10331), (10331, 861)] },
    { n := 20681, F := 20680, R := 1, a := 3, factors := [2, 2, 2, 5, 11, 47], residues := [(2, 10340), (5, 269), (11, 2471), (47, 16157)] },
    { n := 20693, F := 20692, R := 1, a := 2, factors := [2, 2, 7, 739], residues := [(2, 10346), (7, 17693), (739, 3606)] },
    { n := 20707, F := 20706, R := 1, a := 5, factors := [2, 3, 7, 17, 29], residues := [(2, 10353), (3, 8734), (7, 10766), (17, 14122), (29, 8678)] },
    { n := 20717, F := 20716, R := 1, a := 2, factors := [2, 2, 5179], residues := [(2, 10358), (5179, 9668)] },
    { n := 20719, F := 20718, R := 1, a := 3, factors := [2, 3, 3, 1151], residues := [(2, 10359), (3, 5847), (1151, 2855)] },
    { n := 20731, F := 20730, R := 1, a := 2, factors := [2, 3, 5, 691], residues := [(2, 10365), (3, 1290), (5, 18705), (691, 14091)] },
    { n := 20743, F := 20742, R := 1, a := 5, factors := [2, 3, 3457], residues := [(2, 10371), (3, 10261), (3457, 2253)] },
    { n := 20747, F := 20746, R := 1, a := 5, factors := [2, 11, 23, 41], residues := [(2, 10373), (11, 18178), (23, 12531), (41, 16397)] },
    { n := 20749, F := 20748, R := 1, a := 2, factors := [2, 2, 3, 7, 13, 19], residues := [(2, 10374), (3, 5876), (7, 13870), (13, 1786), (19, 19932)] },
    { n := 20753, F := 20752, R := 1, a := 3, factors := [2, 2, 2, 2, 1297], residues := [(2, 10376), (1297, 7254)] },
    { n := 20759, F := 20758, R := 1, a := 7, factors := [2, 97, 107], residues := [(2, 10379), (97, 15464), (107, 1218)] },
    { n := 20771, F := 20770, R := 1, a := 2, factors := [2, 5, 31, 67], residues := [(2, 10385), (5, 13327), (31, 17947), (67, 7321)] },
    { n := 20773, F := 20772, R := 1, a := 2, factors := [2, 2, 3, 3, 577], residues := [(2, 10386), (3, 7397), (577, 449)] },
    { n := 20789, F := 20788, R := 1, a := 2, factors := [2, 2, 5197], residues := [(2, 10394), (5197, 1386)] },
    { n := 20807, F := 20806, R := 1, a := 5, factors := [2, 101, 103], residues := [(2, 10403), (101, 12422), (103, 10913)] },
    { n := 20809, F := 20808, R := 1, a := 7, factors := [2, 2, 2, 3, 3, 17, 17], residues := [(2, 10404), (3, 14283), (17, 4492)] },
    { n := 20849, F := 20848, R := 1, a := 3, factors := [2, 2, 2, 2, 1303], residues := [(2, 10424), (1303, 17508)] },
    { n := 20857, F := 20856, R := 1, a := 10, factors := [2, 2, 2, 3, 11, 79], residues := [(2, 10428), (3, 20174), (11, 19492), (79, 6199)] },
    { n := 20873, F := 20872, R := 1, a := 3, factors := [2, 2, 2, 2609], residues := [(2, 10436), (2609, 6946)] },
    { n := 20879, F := 20878, R := 1, a := 11, factors := [2, 11, 13, 73], residues := [(2, 10439), (11, 5284), (13, 12983), (73, 13333)] },
    { n := 20887, F := 20886, R := 1, a := 3, factors := [2, 3, 59, 59], residues := [(2, 10443), (3, 4625), (59, 16729)] },
    { n := 20897, F := 20896, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 653], residues := [(2, 10448), (653, 4574)] },
    { n := 20899, F := 20898, R := 1, a := 2, factors := [2, 3, 3, 3, 3, 3, 43], residues := [(2, 10449), (3, 9762), (43, 17050)] },
    { n := 20903, F := 20902, R := 1, a := 5, factors := [2, 7, 1493], residues := [(2, 10451), (7, 2666), (1493, 7744)] },
    { n := 20921, F := 20920, R := 1, a := 3, factors := [2, 2, 2, 5, 523], residues := [(2, 10460), (5, 20657), (523, 13366)] },
    { n := 20929, F := 20928, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 3, 109], residues := [(2, 10464), (3, 8981), (109, 12666)] },
    { n := 20939, F := 20938, R := 1, a := 2, factors := [2, 19, 19, 29], residues := [(2, 10469), (19, 18401), (29, 14100)] },
    { n := 20947, F := 20946, R := 1, a := 3, factors := [2, 3, 3491], residues := [(2, 10473), (3, 7609), (3491, 18789)] },
    { n := 20959, F := 20958, R := 1, a := 7, factors := [2, 3, 7, 499], residues := [(2, 10479), (3, 6442), (7, 3993), (499, 14799)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData20_valid : PocklingtonRow.Valid lowPocklingtonData20 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime20 (i : Fin lowPocklingtonData20.length) :
    Nat.Prime (lowPocklingtonData20.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData20_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 19997) (q := 20011) (by
      have hp := lowPocklingtonPrime20 ⟨0, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20011) (q := 20021) (by
      have hp := lowPocklingtonPrime20 ⟨1, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20021) (q := 20023) (by
      have hp := lowPocklingtonPrime20 ⟨2, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20023) (q := 20029) (by
      have hp := lowPocklingtonPrime20 ⟨3, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20029) (q := 20047) (by
      have hp := lowPocklingtonPrime20 ⟨4, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20047) (q := 20051) (by
      have hp := lowPocklingtonPrime20 ⟨5, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20051) (q := 20063) (by
      have hp := lowPocklingtonPrime20 ⟨6, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20063) (q := 20071) (by
      have hp := lowPocklingtonPrime20 ⟨7, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part02_chain :
    DusartPrimeRowsChain 19997 20070 dusartPrimeRows_19937_20958_part02 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20071) (q := 20089) (by
      have hp := lowPocklingtonPrime20 ⟨8, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20089) (q := 20101) (by
      have hp := lowPocklingtonPrime20 ⟨9, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20101) (q := 20107) (by
      have hp := lowPocklingtonPrime20 ⟨10, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20107) (q := 20113) (by
      have hp := lowPocklingtonPrime20 ⟨11, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20113) (q := 20117) (by
      have hp := lowPocklingtonPrime20 ⟨12, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20117) (q := 20123) (by
      have hp := lowPocklingtonPrime20 ⟨13, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20123) (q := 20129) (by
      have hp := lowPocklingtonPrime20 ⟨14, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20129) (q := 20143) (by
      have hp := lowPocklingtonPrime20 ⟨15, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part03_chain :
    DusartPrimeRowsChain 20071 20142 dusartPrimeRows_19937_20958_part03 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20143) (q := 20147) (by
      have hp := lowPocklingtonPrime20 ⟨16, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20147) (q := 20149) (by
      have hp := lowPocklingtonPrime20 ⟨17, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20149) (q := 20161) (by
      have hp := lowPocklingtonPrime20 ⟨18, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20161) (q := 20173) (by
      have hp := lowPocklingtonPrime20 ⟨19, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20173) (q := 20177) (by
      have hp := lowPocklingtonPrime20 ⟨20, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20177) (q := 20183) (by
      have hp := lowPocklingtonPrime20 ⟨21, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20183) (q := 20201) (by
      have hp := lowPocklingtonPrime20 ⟨22, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20201) (q := 20219) (by
      have hp := lowPocklingtonPrime20 ⟨23, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part04_chain :
    DusartPrimeRowsChain 20143 20218 dusartPrimeRows_19937_20958_part04 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20219) (q := 20231) (by
      have hp := lowPocklingtonPrime20 ⟨24, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20231) (q := 20233) (by
      have hp := lowPocklingtonPrime20 ⟨25, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20233) (q := 20249) (by
      have hp := lowPocklingtonPrime20 ⟨26, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20249) (q := 20261) (by
      have hp := lowPocklingtonPrime20 ⟨27, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20261) (q := 20269) (by
      have hp := lowPocklingtonPrime20 ⟨28, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20269) (q := 20287) (by
      have hp := lowPocklingtonPrime20 ⟨29, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20287) (q := 20297) (by
      have hp := lowPocklingtonPrime20 ⟨30, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20297) (q := 20323) (by
      have hp := lowPocklingtonPrime20 ⟨31, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part05_chain :
    DusartPrimeRowsChain 20219 20322 dusartPrimeRows_19937_20958_part05 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20323) (q := 20327) (by
      have hp := lowPocklingtonPrime20 ⟨32, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20327) (q := 20333) (by
      have hp := lowPocklingtonPrime20 ⟨33, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20333) (q := 20341) (by
      have hp := lowPocklingtonPrime20 ⟨34, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20341) (q := 20347) (by
      have hp := lowPocklingtonPrime20 ⟨35, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20347) (q := 20353) (by
      have hp := lowPocklingtonPrime20 ⟨36, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20353) (q := 20357) (by
      have hp := lowPocklingtonPrime20 ⟨37, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20357) (q := 20359) (by
      have hp := lowPocklingtonPrime20 ⟨38, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20359) (q := 20369) (by
      have hp := lowPocklingtonPrime20 ⟨39, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part06_chain :
    DusartPrimeRowsChain 20323 20368 dusartPrimeRows_19937_20958_part06 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20369) (q := 20389) (by
      have hp := lowPocklingtonPrime20 ⟨40, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20389) (q := 20393) (by
      have hp := lowPocklingtonPrime20 ⟨41, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20393) (q := 20399) (by
      have hp := lowPocklingtonPrime20 ⟨42, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20399) (q := 20407) (by
      have hp := lowPocklingtonPrime20 ⟨43, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20407) (q := 20411) (by
      have hp := lowPocklingtonPrime20 ⟨44, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20411) (q := 20431) (by
      have hp := lowPocklingtonPrime20 ⟨45, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20431) (q := 20441) (by
      have hp := lowPocklingtonPrime20 ⟨46, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20441) (q := 20443) (by
      have hp := lowPocklingtonPrime20 ⟨47, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part07_chain :
    DusartPrimeRowsChain 20369 20442 dusartPrimeRows_19937_20958_part07 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20443) (q := 20477) (by
      have hp := lowPocklingtonPrime20 ⟨48, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20477) (q := 20479) (by
      have hp := lowPocklingtonPrime20 ⟨49, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20479) (q := 20483) (by
      have hp := lowPocklingtonPrime20 ⟨50, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20483) (q := 20507) (by
      have hp := lowPocklingtonPrime20 ⟨51, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20507) (q := 20509) (by
      have hp := lowPocklingtonPrime20 ⟨52, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20509) (q := 20521) (by
      have hp := lowPocklingtonPrime20 ⟨53, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20521) (q := 20533) (by
      have hp := lowPocklingtonPrime20 ⟨54, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20533) (q := 20543) (by
      have hp := lowPocklingtonPrime20 ⟨55, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part08_chain :
    DusartPrimeRowsChain 20443 20542 dusartPrimeRows_19937_20958_part08 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20543) (q := 20549) (by
      have hp := lowPocklingtonPrime20 ⟨56, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20549) (q := 20551) (by
      have hp := lowPocklingtonPrime20 ⟨57, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20551) (q := 20563) (by
      have hp := lowPocklingtonPrime20 ⟨58, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20563) (q := 20593) (by
      have hp := lowPocklingtonPrime20 ⟨59, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20593) (q := 20599) (by
      have hp := lowPocklingtonPrime20 ⟨60, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20599) (q := 20611) (by
      have hp := lowPocklingtonPrime20 ⟨61, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20611) (q := 20627) (by
      have hp := lowPocklingtonPrime20 ⟨62, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20627) (q := 20639) (by
      have hp := lowPocklingtonPrime20 ⟨63, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part09_chain :
    DusartPrimeRowsChain 20543 20638 dusartPrimeRows_19937_20958_part09 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20639) (q := 20641) (by
      have hp := lowPocklingtonPrime20 ⟨64, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20641) (q := 20663) (by
      have hp := lowPocklingtonPrime20 ⟨65, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20663) (q := 20681) (by
      have hp := lowPocklingtonPrime20 ⟨66, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20681) (q := 20693) (by
      have hp := lowPocklingtonPrime20 ⟨67, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20693) (q := 20707) (by
      have hp := lowPocklingtonPrime20 ⟨68, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20707) (q := 20717) (by
      have hp := lowPocklingtonPrime20 ⟨69, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20717) (q := 20719) (by
      have hp := lowPocklingtonPrime20 ⟨70, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20719) (q := 20731) (by
      have hp := lowPocklingtonPrime20 ⟨71, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part10_chain :
    DusartPrimeRowsChain 20639 20730 dusartPrimeRows_19937_20958_part10 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20731) (q := 20743) (by
      have hp := lowPocklingtonPrime20 ⟨72, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20743) (q := 20747) (by
      have hp := lowPocklingtonPrime20 ⟨73, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20747) (q := 20749) (by
      have hp := lowPocklingtonPrime20 ⟨74, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20749) (q := 20753) (by
      have hp := lowPocklingtonPrime20 ⟨75, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20753) (q := 20759) (by
      have hp := lowPocklingtonPrime20 ⟨76, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20759) (q := 20771) (by
      have hp := lowPocklingtonPrime20 ⟨77, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20771) (q := 20773) (by
      have hp := lowPocklingtonPrime20 ⟨78, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20773) (q := 20789) (by
      have hp := lowPocklingtonPrime20 ⟨79, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part11_chain :
    DusartPrimeRowsChain 20731 20788 dusartPrimeRows_19937_20958_part11 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20789) (q := 20807) (by
      have hp := lowPocklingtonPrime20 ⟨80, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20807) (q := 20809) (by
      have hp := lowPocklingtonPrime20 ⟨81, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20809) (q := 20849) (by
      have hp := lowPocklingtonPrime20 ⟨82, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20849) (q := 20857) (by
      have hp := lowPocklingtonPrime20 ⟨83, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20857) (q := 20873) (by
      have hp := lowPocklingtonPrime20 ⟨84, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20873) (q := 20879) (by
      have hp := lowPocklingtonPrime20 ⟨85, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20879) (q := 20887) (by
      have hp := lowPocklingtonPrime20 ⟨86, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20887) (q := 20897) (by
      have hp := lowPocklingtonPrime20 ⟨87, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part12_chain :
    DusartPrimeRowsChain 20789 20896 dusartPrimeRows_19937_20958_part12 := by
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

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20897) (q := 20899) (by
      have hp := lowPocklingtonPrime20 ⟨88, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20899) (q := 20903) (by
      have hp := lowPocklingtonPrime20 ⟨89, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20903) (q := 20921) (by
      have hp := lowPocklingtonPrime20 ⟨90, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20921) (q := 20929) (by
      have hp := lowPocklingtonPrime20 ⟨91, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20929) (q := 20939) (by
      have hp := lowPocklingtonPrime20 ⟨92, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20939) (q := 20947) (by
      have hp := lowPocklingtonPrime20 ⟨93, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20947) (q := 20959) (by
      have hp := lowPocklingtonPrime20 ⟨94, by simp [lowPocklingtonData20]⟩
      simpa [lowPocklingtonData20] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part13_chain :
    DusartPrimeRowsChain 20897 20958 dusartPrimeRows_19937_20958_part13 := by
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
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_20952, dusartPrimeRow_of_explicit_right]
