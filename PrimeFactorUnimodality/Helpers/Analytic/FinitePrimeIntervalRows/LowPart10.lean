import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 10 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData10 : List PocklingtonData := [
    { n := 10657, F := 10656, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 3, 3, 37], residues := [(2, 5328), (3, 8432), (37, 3738)] },
    { n := 10663, F := 10662, R := 1, a := 3, factors := [2, 3, 1777], residues := [(2, 5331), (3, 7377), (1777, 249)] },
    { n := 10667, F := 10666, R := 1, a := 2, factors := [2, 5333], residues := [(2, 5333), (5333, 3556)] },
    { n := 10687, F := 10686, R := 1, a := 5, factors := [2, 3, 13, 137], residues := [(2, 5343), (3, 8342), (13, 6726), (137, 5794)] },
    { n := 10691, F := 10690, R := 1, a := 2, factors := [2, 5, 1069], residues := [(2, 5345), (5, 5213), (1069, 6563)] },
    { n := 10709, F := 10708, R := 1, a := 2, factors := [2, 2, 2677], residues := [(2, 5354), (2677, 714)] },
    { n := 10711, F := 10710, R := 1, a := 3, factors := [2, 3, 3, 5, 7, 17], residues := [(2, 5355), (3, 5640), (5, 10234), (7, 8233), (17, 2620)] },
    { n := 10723, F := 10722, R := 1, a := 2, factors := [2, 3, 1787], residues := [(2, 5361), (3, 10304), (1787, 4936)] },
    { n := 10729, F := 10728, R := 1, a := 7, factors := [2, 2, 2, 3, 3, 149], residues := [(2, 5364), (3, 7733), (149, 8551)] },
    { n := 10733, F := 10732, R := 1, a := 2, factors := [2, 2, 2683], residues := [(2, 5366), (2683, 9302)] },
    { n := 10739, F := 10738, R := 1, a := 6, factors := [2, 7, 13, 59], residues := [(2, 5369), (7, 6302), (13, 5058), (59, 324)] },
    { n := 10753, F := 10752, R := 1, a := 11, factors := [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 7], residues := [(2, 5376), (3, 1867), (7, 1268)] },
    { n := 10771, F := 10770, R := 1, a := 3, factors := [2, 3, 5, 359], residues := [(2, 5385), (3, 5889), (5, 549), (359, 240)] },
    { n := 10781, F := 10780, R := 1, a := 10, factors := [2, 2, 5, 7, 7, 11], residues := [(2, 5390), (5, 2787), (7, 834), (11, 2941)] },
    { n := 10789, F := 10788, R := 1, a := 2, factors := [2, 2, 3, 29, 31], residues := [(2, 5394), (3, 4753), (29, 5037), (31, 9889)] },
    { n := 10799, F := 10798, R := 1, a := 19, factors := [2, 5399], residues := [(2, 5399), (5399, 30)] },
    { n := 10831, F := 10830, R := 1, a := 7, factors := [2, 3, 5, 19, 19], residues := [(2, 5415), (3, 9708), (5, 2005), (19, 3346)] },
    { n := 10837, F := 10836, R := 1, a := 2, factors := [2, 2, 3, 3, 7, 43], residues := [(2, 5418), (3, 1374), (7, 3536), (43, 5164)] },
    { n := 10847, F := 10846, R := 1, a := 5, factors := [2, 11, 17, 29], residues := [(2, 5423), (11, 6321), (17, 10307), (29, 1699)] },
    { n := 10853, F := 10852, R := 1, a := 2, factors := [2, 2, 2713], residues := [(2, 5426), (2713, 9406)] },
    { n := 10859, F := 10858, R := 1, a := 2, factors := [2, 61, 89], residues := [(2, 5429), (61, 1495), (89, 8212)] },
    { n := 10861, F := 10860, R := 1, a := 2, factors := [2, 2, 3, 5, 181], residues := [(2, 5430), (3, 1399), (5, 7733), (181, 3891)] },
    { n := 10867, F := 10866, R := 1, a := 2, factors := [2, 3, 1811], residues := [(2, 5433), (3, 2662), (1811, 345)] },
    { n := 10883, F := 10882, R := 1, a := 2, factors := [2, 5441], residues := [(2, 5441), (5441, 3628)] },
    { n := 10889, F := 10888, R := 1, a := 3, factors := [2, 2, 2, 1361], residues := [(2, 5444), (1361, 8351)] },
    { n := 10891, F := 10890, R := 1, a := 2, factors := [2, 3, 3, 5, 11, 11], residues := [(2, 5445), (3, 366), (5, 623), (11, 7029)] },
    { n := 10903, F := 10902, R := 1, a := 3, factors := [2, 3, 23, 79], residues := [(2, 5451), (3, 10743), (23, 680), (79, 3815)] },
    { n := 10909, F := 10908, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 101], residues := [(2, 5454), (3, 4183), (101, 10287)] },
    { n := 10937, F := 10936, R := 1, a := 3, factors := [2, 2, 2, 1367], residues := [(2, 5468), (1367, 8948)] },
    { n := 10939, F := 10938, R := 1, a := 3, factors := [2, 3, 1823], residues := [(2, 5469), (3, 1465), (1823, 9211)] },
    { n := 10949, F := 10948, R := 1, a := 2, factors := [2, 2, 7, 17, 23], residues := [(2, 5474), (7, 7577), (17, 5820), (23, 10813)] },
    { n := 10957, F := 10956, R := 1, a := 5, factors := [2, 2, 3, 11, 83], residues := [(2, 5478), (3, 9908), (11, 7368), (83, 2635)] },
    { n := 10973, F := 10972, R := 1, a := 2, factors := [2, 2, 13, 211], residues := [(2, 5486), (13, 1173), (211, 1598)] },
    { n := 10979, F := 10978, R := 1, a := 2, factors := [2, 11, 499], residues := [(2, 5489), (11, 5502), (499, 6959)] },
    { n := 10987, F := 10986, R := 1, a := 2, factors := [2, 3, 1831], residues := [(2, 5493), (3, 8777), (1831, 872)] },
    { n := 10993, F := 10992, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 229], residues := [(2, 5496), (3, 7843), (229, 5526)] },
    { n := 11003, F := 11002, R := 1, a := 2, factors := [2, 5501], residues := [(2, 5501), (5501, 3668)] },
    { n := 11027, F := 11026, R := 1, a := 2, factors := [2, 37, 149], residues := [(2, 5513), (37, 10487), (149, 1519)] },
    { n := 11047, F := 11046, R := 1, a := 3, factors := [2, 3, 7, 263], residues := [(2, 5523), (3, 7928), (7, 4502), (263, 9845)] },
    { n := 11057, F := 11056, R := 1, a := 3, factors := [2, 2, 2, 2, 691], residues := [(2, 5528), (691, 1933)] },
    { n := 11059, F := 11058, R := 1, a := 10, factors := [2, 3, 19, 97], residues := [(2, 5529), (3, 1435), (19, 4334), (97, 6582)] },
    { n := 11069, F := 11068, R := 1, a := 2, factors := [2, 2, 2767], residues := [(2, 5534), (2767, 738)] },
    { n := 11071, F := 11070, R := 1, a := 3, factors := [2, 3, 3, 3, 5, 41], residues := [(2, 5535), (3, 10491), (5, 8769), (41, 3795)] },
    { n := 11083, F := 11082, R := 1, a := 2, factors := [2, 3, 1847], residues := [(2, 5541), (3, 5153), (1847, 6685)] },
    { n := 11087, F := 11086, R := 1, a := 5, factors := [2, 23, 241], residues := [(2, 5543), (23, 1844), (241, 4718)] },
    { n := 11093, F := 11092, R := 1, a := 2, factors := [2, 2, 47, 59], residues := [(2, 5546), (47, 7494), (59, 8300)] },
    { n := 11113, F := 11112, R := 1, a := 13, factors := [2, 2, 2, 3, 463], residues := [(2, 5556), (3, 8694), (463, 6622)] },
    { n := 11117, F := 11116, R := 1, a := 3, factors := [2, 2, 7, 397], residues := [(2, 5558), (7, 10199), (397, 3453)] },
    { n := 11119, F := 11118, R := 1, a := 3, factors := [2, 3, 17, 109], residues := [(2, 5559), (3, 4491), (17, 353), (109, 9542)] },
    { n := 11131, F := 11130, R := 1, a := 2, factors := [2, 3, 5, 7, 53], residues := [(2, 5565), (3, 7385), (5, 8646), (7, 5515), (53, 7635)] },
    { n := 11149, F := 11148, R := 1, a := 10, factors := [2, 2, 3, 929], residues := [(2, 5574), (3, 9669), (929, 3656)] },
    { n := 11159, F := 11158, R := 1, a := 7, factors := [2, 7, 797], residues := [(2, 5579), (7, 7029), (797, 8397)] },
    { n := 11161, F := 11160, R := 1, a := 7, factors := [2, 2, 2, 3, 3, 5, 31], residues := [(2, 5580), (3, 4991), (5, 67), (31, 10508)] },
    { n := 11171, F := 11170, R := 1, a := 2, factors := [2, 5, 1117], residues := [(2, 5585), (5, 10661), (1117, 2861)] },
    { n := 11173, F := 11172, R := 1, a := 5, factors := [2, 2, 3, 7, 7, 19], residues := [(2, 5586), (3, 8794), (7, 9650), (19, 10143)] },
    { n := 11177, F := 11176, R := 1, a := 3, factors := [2, 2, 2, 11, 127], residues := [(2, 5588), (11, 8554), (127, 2494)] },
    { n := 11197, F := 11196, R := 1, a := 2, factors := [2, 2, 3, 3, 311], residues := [(2, 5598), (3, 9729), (311, 858)] },
    { n := 11213, F := 11212, R := 1, a := 2, factors := [2, 2, 2803], residues := [(2, 5606), (2803, 9718)] },
    { n := 11239, F := 11238, R := 1, a := 3, factors := [2, 3, 1873], residues := [(2, 5619), (3, 1855), (1873, 1374)] },
    { n := 11243, F := 11242, R := 1, a := 5, factors := [2, 7, 11, 73], residues := [(2, 5621), (7, 2575), (11, 1875), (73, 4369)] },
    { n := 11251, F := 11250, R := 1, a := 13, factors := [2, 3, 3, 5, 5, 5, 5], residues := [(2, 5625), (3, 3391), (5, 9241)] },
    { n := 11257, F := 11256, R := 1, a := 10, factors := [2, 2, 2, 3, 7, 67], residues := [(2, 5628), (3, 1440), (7, 7209), (67, 5797)] },
    { n := 11261, F := 11260, R := 1, a := 2, factors := [2, 2, 5, 563], residues := [(2, 5630), (5, 7395), (563, 1306)] },
    { n := 11273, F := 11272, R := 1, a := 3, factors := [2, 2, 2, 1409], residues := [(2, 5636), (1409, 177)] },
    { n := 11279, F := 11278, R := 1, a := 7, factors := [2, 5639], residues := [(2, 5639), (5639, 235)] },
    { n := 11287, F := 11286, R := 1, a := 3, factors := [2, 3, 3, 3, 11, 19], residues := [(2, 5643), (3, 6125), (11, 6438), (19, 11248)] },
    { n := 11299, F := 11298, R := 1, a := 3, factors := [2, 3, 7, 269], residues := [(2, 5649), (3, 3266), (7, 2700), (269, 2206)] },
    { n := 11311, F := 11310, R := 1, a := 3, factors := [2, 3, 5, 13, 29], residues := [(2, 5655), (3, 373), (5, 2845), (13, 4907), (29, 3474)] },
    { n := 11317, F := 11316, R := 1, a := 2, factors := [2, 2, 3, 23, 41], residues := [(2, 5658), (3, 162), (23, 11176), (41, 8783)] },
    { n := 11321, F := 11320, R := 1, a := 3, factors := [2, 2, 2, 5, 283], residues := [(2, 5660), (5, 3925), (283, 6183)] },
    { n := 11329, F := 11328, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 3, 59], residues := [(2, 5664), (3, 7143), (59, 7509)] },
    { n := 11351, F := 11350, R := 1, a := 7, factors := [2, 5, 5, 227], residues := [(2, 5675), (5, 1332), (227, 1949)] },
    { n := 11353, F := 11352, R := 1, a := 7, factors := [2, 2, 2, 3, 11, 43], residues := [(2, 5676), (3, 6799), (11, 6163), (43, 5853)] },
    { n := 11369, F := 11368, R := 1, a := 3, factors := [2, 2, 2, 7, 7, 29], residues := [(2, 5684), (7, 4068), (29, 742)] },
    { n := 11383, F := 11382, R := 1, a := 5, factors := [2, 3, 7, 271], residues := [(2, 5691), (3, 11114), (7, 9056), (271, 1210)] },
    { n := 11393, F := 11392, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 89], residues := [(2, 5696), (89, 9239)] },
    { n := 11399, F := 11398, R := 1, a := 11, factors := [2, 41, 139], residues := [(2, 5699), (41, 5165), (139, 588)] },
    { n := 11411, F := 11410, R := 1, a := 7, factors := [2, 5, 7, 163], residues := [(2, 5705), (5, 3032), (7, 5665), (163, 1006)] },
    { n := 11423, F := 11422, R := 1, a := 5, factors := [2, 5711], residues := [(2, 5711), (5711, 476)] },
    { n := 11437, F := 11436, R := 1, a := 2, factors := [2, 2, 3, 953], residues := [(2, 5718), (3, 8430), (953, 2603)] },
    { n := 11443, F := 11442, R := 1, a := 2, factors := [2, 3, 1907], residues := [(2, 5721), (3, 4791), (1907, 1998)] },
    { n := 11447, F := 11446, R := 1, a := 5, factors := [2, 59, 97], residues := [(2, 5723), (59, 6951), (97, 3249)] },
    { n := 11467, F := 11466, R := 1, a := 5, factors := [2, 3, 3, 7, 7, 13], residues := [(2, 5733), (3, 8778), (7, 530), (13, 9817)] },
    { n := 11471, F := 11470, R := 1, a := 11, factors := [2, 5, 31, 37], residues := [(2, 5735), (5, 5662), (31, 7362), (37, 4372)] },
    { n := 11483, F := 11482, R := 1, a := 2, factors := [2, 5741], residues := [(2, 5741), (5741, 3828)] },
    { n := 11489, F := 11488, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 359], residues := [(2, 5744), (359, 1620)] },
    { n := 11491, F := 11490, R := 1, a := 3, factors := [2, 3, 5, 383], residues := [(2, 5745), (3, 3701), (5, 3078), (383, 6464)] },
    { n := 11497, F := 11496, R := 1, a := 7, factors := [2, 2, 2, 3, 479], residues := [(2, 5748), (3, 483), (479, 7895)] },
    { n := 11503, F := 11502, R := 1, a := 3, factors := [2, 3, 3, 3, 3, 71], residues := [(2, 5751), (3, 3678), (71, 6309)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData10_valid : PocklingtonRow.Valid lowPocklingtonData10 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPrime_10657 : Nat.Prime 10657 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10663 : Nat.Prime 10663 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10667 : Nat.Prime 10667 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10687 : Nat.Prime 10687 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10691 : Nat.Prime 10691 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10709 : Nat.Prime 10709 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10711 : Nat.Prime 10711 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10723 : Nat.Prime 10723 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10729 : Nat.Prime 10729 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10733 : Nat.Prime 10733 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10739 : Nat.Prime 10739 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10753 : Nat.Prime 10753 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10771 : Nat.Prime 10771 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10781 : Nat.Prime 10781 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10789 : Nat.Prime 10789 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10799 : Nat.Prime 10799 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10831 : Nat.Prime 10831 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10837 : Nat.Prime 10837 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10847 : Nat.Prime 10847 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10853 : Nat.Prime 10853 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10859 : Nat.Prime 10859 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10861 : Nat.Prime 10861 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10867 : Nat.Prime 10867 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10883 : Nat.Prime 10883 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10889 : Nat.Prime 10889 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10891 : Nat.Prime 10891 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10903 : Nat.Prime 10903 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10909 : Nat.Prime 10909 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10937 : Nat.Prime 10937 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10939 : Nat.Prime 10939 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10949 : Nat.Prime 10949 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10957 : Nat.Prime 10957 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10973 : Nat.Prime 10973 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10979 : Nat.Prime 10979 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10987 : Nat.Prime 10987 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_10993 : Nat.Prime 10993 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11003 : Nat.Prime 11003 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11027 : Nat.Prime 11027 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11047 : Nat.Prime 11047 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11057 : Nat.Prime 11057 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11059 : Nat.Prime 11059 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11069 : Nat.Prime 11069 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11071 : Nat.Prime 11071 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11083 : Nat.Prime 11083 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11087 : Nat.Prime 11087 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11093 : Nat.Prime 11093 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11113 : Nat.Prime 11113 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11117 : Nat.Prime 11117 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11119 : Nat.Prime 11119 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11131 : Nat.Prime 11131 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11149 : Nat.Prime 11149 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11159 : Nat.Prime 11159 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11161 : Nat.Prime 11161 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11171 : Nat.Prime 11171 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11173 : Nat.Prime 11173 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11177 : Nat.Prime 11177 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11197 : Nat.Prime 11197 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11213 : Nat.Prime 11213 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11239 : Nat.Prime 11239 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11243 : Nat.Prime 11243 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11251 : Nat.Prime 11251 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11257 : Nat.Prime 11257 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11261 : Nat.Prime 11261 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11273 : Nat.Prime 11273 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11279 : Nat.Prime 11279 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11287 : Nat.Prime 11287 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11299 : Nat.Prime 11299 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11311 : Nat.Prime 11311 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11317 : Nat.Prime 11317 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11321 : Nat.Prime 11321 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11329 : Nat.Prime 11329 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11351 : Nat.Prime 11351 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11353 : Nat.Prime 11353 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11369 : Nat.Prime 11369 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11383 : Nat.Prime 11383 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11393 : Nat.Prime 11393 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11399 : Nat.Prime 11399 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11411 : Nat.Prime 11411 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11423 : Nat.Prime 11423 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11437 : Nat.Prime 11437 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11443 : Nat.Prime 11443 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11447 : Nat.Prime 11447 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11467 : Nat.Prime 11467 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11471 : Nat.Prime 11471 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11483 : Nat.Prime 11483 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11489 : Nat.Prime 11489 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11491 : Nat.Prime 11491 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11497 : Nat.Prime 11497 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]

theorem lowPrime_11503 : Nat.Prime 11503 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData10_valid
  simp [lowPocklingtonData10]
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10651) (q := 10657) (by exact lowPrime_10657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10657) (q := 10663) (by exact lowPrime_10663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10663) (q := 10667) (by exact lowPrime_10667) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10667) (q := 10687) (by exact lowPrime_10687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10687) (q := 10691) (by exact lowPrime_10691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10691) (q := 10709) (by exact lowPrime_10709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10709) (q := 10711) (by exact lowPrime_10711) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10711) (q := 10723) (by exact lowPrime_10723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part04_chain :
    DusartPrimeRowsChain 10651 10722 dusartPrimeRows_10427_10938_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10938, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10723) (q := 10729) (by exact lowPrime_10729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10729) (q := 10733) (by exact lowPrime_10733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10733) (q := 10739) (by exact lowPrime_10739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10739) (q := 10753) (by exact lowPrime_10753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10753) (q := 10771) (by exact lowPrime_10771) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10771) (q := 10781) (by exact lowPrime_10781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10781) (q := 10789) (by exact lowPrime_10789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10789) (q := 10799) (by exact lowPrime_10799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part05_chain :
    DusartPrimeRowsChain 10723 10798 dusartPrimeRows_10427_10938_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10938, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10799) (q := 10831) (by exact lowPrime_10831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10831) (q := 10837) (by exact lowPrime_10837) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10837) (q := 10847) (by exact lowPrime_10847) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10847) (q := 10853) (by exact lowPrime_10853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10853) (q := 10859) (by exact lowPrime_10859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10859) (q := 10861) (by exact lowPrime_10861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10861) (q := 10867) (by exact lowPrime_10867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10867) (q := 10883) (by exact lowPrime_10883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part06_chain :
    DusartPrimeRowsChain 10799 10882 dusartPrimeRows_10427_10938_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10938, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10883) (q := 10889) (by exact lowPrime_10889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10889) (q := 10891) (by exact lowPrime_10891) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10891) (q := 10903) (by exact lowPrime_10903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10903) (q := 10909) (by exact lowPrime_10909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10909) (q := 10937) (by exact lowPrime_10937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10937) (q := 10939) (by exact lowPrime_10939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part07_chain :
    DusartPrimeRowsChain 10883 10938 dusartPrimeRows_10427_10938_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_10938, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 10939) (q := 10949) (by exact lowPrime_10949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10949) (q := 10957) (by exact lowPrime_10957) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10957) (q := 10973) (by exact lowPrime_10973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10973) (q := 10979) (by exact lowPrime_10979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10979) (q := 10987) (by exact lowPrime_10987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10987) (q := 10993) (by exact lowPrime_10993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 10993) (q := 11003) (by exact lowPrime_11003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11003) (q := 11027) (by exact lowPrime_11027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part01_chain :
    DusartPrimeRowsChain 10939 11026 dusartPrimeRows_10939_11502_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11027) (q := 11047) (by exact lowPrime_11047) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11047) (q := 11057) (by exact lowPrime_11057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11057) (q := 11059) (by exact lowPrime_11059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11059) (q := 11069) (by exact lowPrime_11069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11069) (q := 11071) (by exact lowPrime_11071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11071) (q := 11083) (by exact lowPrime_11083) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11083) (q := 11087) (by exact lowPrime_11087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11087) (q := 11093) (by exact lowPrime_11093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part02_chain :
    DusartPrimeRowsChain 11027 11092 dusartPrimeRows_10939_11502_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11093) (q := 11113) (by exact lowPrime_11113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11113) (q := 11117) (by exact lowPrime_11117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11117) (q := 11119) (by exact lowPrime_11119) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11119) (q := 11131) (by exact lowPrime_11131) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11131) (q := 11149) (by exact lowPrime_11149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11149) (q := 11159) (by exact lowPrime_11159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11159) (q := 11161) (by exact lowPrime_11161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11161) (q := 11171) (by exact lowPrime_11171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part03_chain :
    DusartPrimeRowsChain 11093 11170 dusartPrimeRows_10939_11502_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11171) (q := 11173) (by exact lowPrime_11173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11173) (q := 11177) (by exact lowPrime_11177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11177) (q := 11197) (by exact lowPrime_11197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11197) (q := 11213) (by exact lowPrime_11213) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11213) (q := 11239) (by exact lowPrime_11239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11239) (q := 11243) (by exact lowPrime_11243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11243) (q := 11251) (by exact lowPrime_11251) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11251) (q := 11257) (by exact lowPrime_11257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part04_chain :
    DusartPrimeRowsChain 11171 11256 dusartPrimeRows_10939_11502_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11257) (q := 11261) (by exact lowPrime_11261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11261) (q := 11273) (by exact lowPrime_11273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11273) (q := 11279) (by exact lowPrime_11279) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11279) (q := 11287) (by exact lowPrime_11287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11287) (q := 11299) (by exact lowPrime_11299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11299) (q := 11311) (by exact lowPrime_11311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11311) (q := 11317) (by exact lowPrime_11317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11317) (q := 11321) (by exact lowPrime_11321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part05_chain :
    DusartPrimeRowsChain 11257 11320 dusartPrimeRows_10939_11502_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11321) (q := 11329) (by exact lowPrime_11329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11329) (q := 11351) (by exact lowPrime_11351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11351) (q := 11353) (by exact lowPrime_11353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11353) (q := 11369) (by exact lowPrime_11369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11369) (q := 11383) (by exact lowPrime_11383) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11383) (q := 11393) (by exact lowPrime_11393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11393) (q := 11399) (by exact lowPrime_11399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11399) (q := 11411) (by exact lowPrime_11411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part06_chain :
    DusartPrimeRowsChain 11321 11410 dusartPrimeRows_10939_11502_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11411) (q := 11423) (by exact lowPrime_11423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11423) (q := 11437) (by exact lowPrime_11437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11437) (q := 11443) (by exact lowPrime_11443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11443) (q := 11447) (by exact lowPrime_11447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11447) (q := 11467) (by exact lowPrime_11467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11467) (q := 11471) (by exact lowPrime_11471) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11471) (q := 11483) (by exact lowPrime_11483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11483) (q := 11489) (by exact lowPrime_11489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part07_chain :
    DusartPrimeRowsChain 11411 11488 dusartPrimeRows_10939_11502_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11489) (q := 11491) (by exact lowPrime_11491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11491) (q := 11497) (by exact lowPrime_11497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11497) (q := 11503) (by exact lowPrime_11503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part08_chain :
    DusartPrimeRowsChain 11489 11502 dusartPrimeRows_10939_11502_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.empty
        norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]
