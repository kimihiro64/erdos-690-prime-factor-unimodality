import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 09 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData09 : List PocklingtonData := [
    { n := 9781, F := 9780, R := 1, a := 6, factors := [2, 2, 3, 5, 163], residues := [(2, 4890), (3, 1824), (5, 1602), (163, 1085)] },
    { n := 9787, F := 9786, R := 1, a := 3, factors := [2, 3, 7, 233], residues := [(2, 4893), (3, 1010), (7, 4852), (233, 2923)] },
    { n := 9791, F := 9790, R := 1, a := 11, factors := [2, 5, 11, 89], residues := [(2, 4895), (5, 2554), (11, 3431), (89, 1704)] },
    { n := 9803, F := 9802, R := 1, a := 2, factors := [2, 13, 13, 29], residues := [(2, 4901), (13, 2966), (29, 5594)] },
    { n := 9811, F := 9810, R := 1, a := 3, factors := [2, 3, 3, 5, 109], residues := [(2, 4905), (3, 6741), (5, 651), (109, 8430)] },
    { n := 9817, F := 9816, R := 1, a := 5, factors := [2, 2, 2, 3, 409], residues := [(2, 4908), (3, 318), (409, 7256)] },
    { n := 9829, F := 9828, R := 1, a := 10, factors := [2, 2, 3, 3, 3, 7, 13], residues := [(2, 4914), (3, 9579), (7, 7189), (13, 5419)] },
    { n := 9833, F := 9832, R := 1, a := 3, factors := [2, 2, 2, 1229], residues := [(2, 4916), (1229, 3512)] },
    { n := 9839, F := 9838, R := 1, a := 7, factors := [2, 4919], residues := [(2, 4919), (4919, 205)] },
    { n := 9851, F := 9850, R := 1, a := 2, factors := [2, 5, 5, 197], residues := [(2, 4925), (5, 8629), (197, 3882)] },
    { n := 9857, F := 9856, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 2, 7, 11], residues := [(2, 4928), (7, 19), (11, 1245)] },
    { n := 9859, F := 9858, R := 1, a := 2, factors := [2, 3, 31, 53], residues := [(2, 4929), (3, 1583), (31, 3176), (53, 534)] },
    { n := 9871, F := 9870, R := 1, a := 3, factors := [2, 3, 5, 7, 47], residues := [(2, 4935), (3, 3507), (5, 3318), (7, 6932), (47, 5909)] },
    { n := 9883, F := 9882, R := 1, a := 2, factors := [2, 3, 3, 3, 3, 61], residues := [(2, 4941), (3, 9037), (61, 6434)] },
    { n := 9887, F := 9886, R := 1, a := 5, factors := [2, 4943], residues := [(2, 4943), (4943, 412)] },
    { n := 9901, F := 9900, R := 1, a := 2, factors := [2, 2, 3, 3, 5, 5, 11], residues := [(2, 4950), (3, 6567), (5, 4084), (11, 4839)] },
    { n := 9907, F := 9906, R := 1, a := 2, factors := [2, 3, 13, 127], residues := [(2, 4953), (3, 2190), (13, 6085), (127, 8864)] },
    { n := 9923, F := 9922, R := 1, a := 2, factors := [2, 11, 11, 41], residues := [(2, 4961), (11, 236), (41, 5175)] },
    { n := 9929, F := 9928, R := 1, a := 3, factors := [2, 2, 2, 17, 73], residues := [(2, 4964), (17, 5034), (73, 9317)] },
    { n := 9931, F := 9930, R := 1, a := 10, factors := [2, 3, 5, 331], residues := [(2, 4965), (3, 8520), (5, 4557), (331, 8867)] },
    { n := 9941, F := 9940, R := 1, a := 2, factors := [2, 2, 5, 7, 71], residues := [(2, 4970), (5, 911), (7, 778), (71, 4064)] },
    { n := 9949, F := 9948, R := 1, a := 2, factors := [2, 2, 3, 829], residues := [(2, 4974), (3, 5421), (829, 1776)] },
    { n := 9967, F := 9966, R := 1, a := 3, factors := [2, 3, 11, 151], residues := [(2, 4983), (3, 152), (11, 9247), (151, 1834)] },
    { n := 9973, F := 9972, R := 1, a := 11, factors := [2, 2, 3, 3, 277], residues := [(2, 4986), (3, 6125), (277, 891)] },
    { n := 10007, F := 10006, R := 1, a := 5, factors := [2, 5003], residues := [(2, 5003), (5003, 417)] },
    { n := 10009, F := 10008, R := 1, a := 11, factors := [2, 2, 2, 3, 3, 139], residues := [(2, 5004), (3, 3684), (139, 578)] },
    { n := 10037, F := 10036, R := 1, a := 2, factors := [2, 2, 13, 193], residues := [(2, 5018), (13, 7013), (193, 8757)] },
    { n := 10039, F := 10038, R := 1, a := 3, factors := [2, 3, 7, 239], residues := [(2, 5019), (3, 2102), (7, 4557), (239, 468)] },
    { n := 10061, F := 10060, R := 1, a := 3, factors := [2, 2, 5, 503], residues := [(2, 5030), (5, 8053), (503, 9565)] },
    { n := 10067, F := 10066, R := 1, a := 2, factors := [2, 7, 719], residues := [(2, 5033), (7, 4295), (719, 3234)] },
    { n := 10069, F := 10068, R := 1, a := 2, factors := [2, 2, 3, 839], residues := [(2, 5034), (3, 8500), (839, 986)] },
    { n := 10079, F := 10078, R := 1, a := 11, factors := [2, 5039], residues := [(2, 5039), (5039, 84)] },
    { n := 10091, F := 10090, R := 1, a := 2, factors := [2, 5, 1009], residues := [(2, 5045), (5, 5246), (1009, 1815)] },
    { n := 10093, F := 10092, R := 1, a := 2, factors := [2, 2, 3, 29, 29], residues := [(2, 5046), (3, 5017), (29, 4299)] },
    { n := 10099, F := 10098, R := 1, a := 2, factors := [2, 3, 3, 3, 11, 17], residues := [(2, 5049), (3, 8048), (11, 5324), (17, 1770)] },
    { n := 10103, F := 10102, R := 1, a := 5, factors := [2, 5051], residues := [(2, 5051), (5051, 421)] },
    { n := 10111, F := 10110, R := 1, a := 12, factors := [2, 3, 5, 337], residues := [(2, 5055), (3, 5313), (5, 8110), (337, 2614)] },
    { n := 10133, F := 10132, R := 1, a := 2, factors := [2, 2, 17, 149], residues := [(2, 5066), (17, 9859), (149, 6347)] },
    { n := 10139, F := 10138, R := 1, a := 2, factors := [2, 37, 137], residues := [(2, 5069), (37, 9987), (137, 5073)] },
    { n := 10141, F := 10140, R := 1, a := 2, factors := [2, 2, 3, 5, 13, 13], residues := [(2, 5070), (3, 9412), (5, 7257), (13, 5274)] },
    { n := 10151, F := 10150, R := 1, a := 7, factors := [2, 5, 5, 7, 29], residues := [(2, 5075), (5, 757), (7, 3042), (29, 120)] },
    { n := 10159, F := 10158, R := 1, a := 3, factors := [2, 3, 1693], residues := [(2, 5079), (3, 4917), (1693, 4926)] },
    { n := 10163, F := 10162, R := 1, a := 2, factors := [2, 5081], residues := [(2, 5081), (5081, 3388)] },
    { n := 10169, F := 10168, R := 1, a := 3, factors := [2, 2, 2, 31, 41], residues := [(2, 5084), (31, 10036), (41, 8135)] },
    { n := 10177, F := 10176, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 3, 53], residues := [(2, 5088), (3, 5193), (53, 259)] },
    { n := 10181, F := 10180, R := 1, a := 2, factors := [2, 2, 5, 509], residues := [(2, 5090), (5, 7224), (509, 3743)] },
    { n := 10193, F := 10192, R := 1, a := 3, factors := [2, 2, 2, 2, 7, 7, 13], residues := [(2, 5096), (7, 2241), (13, 7140)] },
    { n := 10211, F := 10210, R := 1, a := 6, factors := [2, 5, 1021], residues := [(2, 5105), (5, 3206), (1021, 8076)] },
    { n := 10223, F := 10222, R := 1, a := 5, factors := [2, 19, 269], residues := [(2, 5111), (19, 7259), (269, 5490)] },
    { n := 10243, F := 10242, R := 1, a := 7, factors := [2, 3, 3, 569], residues := [(2, 5121), (3, 7016), (569, 1942)] },
    { n := 10247, F := 10246, R := 1, a := 5, factors := [2, 47, 109], residues := [(2, 5123), (47, 4336), (109, 7615)] },
    { n := 10253, F := 10252, R := 1, a := 2, factors := [2, 2, 11, 233], residues := [(2, 5126), (11, 2273), (233, 9846)] },
    { n := 10259, F := 10258, R := 1, a := 2, factors := [2, 23, 223], residues := [(2, 5129), (23, 844), (223, 3520)] },
    { n := 10267, F := 10266, R := 1, a := 2, factors := [2, 3, 29, 59], residues := [(2, 5133), (3, 58), (29, 2860), (59, 2107)] },
    { n := 10271, F := 10270, R := 1, a := 7, factors := [2, 5, 13, 79], residues := [(2, 5135), (5, 9601), (13, 2070), (79, 9855)] },
    { n := 10273, F := 10272, R := 1, a := 10, factors := [2, 2, 2, 2, 2, 3, 107], residues := [(2, 5136), (3, 6175), (107, 1401)] },
    { n := 10289, F := 10288, R := 1, a := 3, factors := [2, 2, 2, 2, 643], residues := [(2, 5144), (643, 8718)] },
    { n := 10301, F := 10300, R := 1, a := 2, factors := [2, 2, 5, 5, 103], residues := [(2, 5150), (5, 9185), (103, 8186)] },
    { n := 10303, F := 10302, R := 1, a := 3, factors := [2, 3, 17, 101], residues := [(2, 5151), (3, 3400), (17, 1290), (101, 4197)] },
    { n := 10313, F := 10312, R := 1, a := 3, factors := [2, 2, 2, 1289], residues := [(2, 5156), (1289, 665)] },
    { n := 10321, F := 10320, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 5, 43], residues := [(2, 5160), (3, 7575), (5, 2095), (43, 8568)] },
    { n := 10331, F := 10330, R := 1, a := 2, factors := [2, 5, 1033], residues := [(2, 5165), (5, 10168), (1033, 7160)] },
    { n := 10333, F := 10332, R := 1, a := 5, factors := [2, 2, 3, 3, 7, 41], residues := [(2, 5166), (3, 8077), (7, 6570), (41, 6858)] },
    { n := 10337, F := 10336, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 17, 19], residues := [(2, 5168), (17, 4136), (19, 8238)] },
    { n := 10343, F := 10342, R := 1, a := 5, factors := [2, 5171], residues := [(2, 5171), (5171, 431)] },
    { n := 10357, F := 10356, R := 1, a := 2, factors := [2, 2, 3, 863], residues := [(2, 5178), (3, 8173), (863, 650)] },
    { n := 10369, F := 10368, R := 1, a := 13, factors := [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3], residues := [(2, 5184), (3, 3178)] },
    { n := 10391, F := 10390, R := 1, a := 19, factors := [2, 5, 1039], residues := [(2, 5195), (5, 4826), (1039, 6067)] },
    { n := 10399, F := 10398, R := 1, a := 6, factors := [2, 3, 1733], residues := [(2, 5199), (3, 3614), (1733, 37)] },
    { n := 10427, F := 10426, R := 1, a := 2, factors := [2, 13, 401], residues := [(2, 5213), (13, 6444), (401, 1177)] },
    { n := 10429, F := 10428, R := 1, a := 7, factors := [2, 2, 3, 11, 79], residues := [(2, 5214), (3, 2671), (11, 1266), (79, 6072)] },
    { n := 10433, F := 10432, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 163], residues := [(2, 5216), (163, 10059)] },
    { n := 10453, F := 10452, R := 1, a := 5, factors := [2, 2, 3, 13, 67], residues := [(2, 5226), (3, 3574), (13, 2912), (67, 2197)] },
    { n := 10457, F := 10456, R := 1, a := 3, factors := [2, 2, 2, 1307], residues := [(2, 5228), (1307, 7025)] },
    { n := 10459, F := 10458, R := 1, a := 2, factors := [2, 3, 3, 7, 83], residues := [(2, 5229), (3, 3929), (7, 6060), (83, 7039)] },
    { n := 10463, F := 10462, R := 1, a := 5, factors := [2, 5231], residues := [(2, 5231), (5231, 436)] },
    { n := 10477, F := 10476, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 97], residues := [(2, 5238), (3, 3253), (97, 278)] },
    { n := 10487, F := 10486, R := 1, a := 5, factors := [2, 7, 7, 107], residues := [(2, 5243), (7, 7871), (107, 7201)] },
    { n := 10499, F := 10498, R := 1, a := 2, factors := [2, 29, 181], residues := [(2, 5249), (29, 1425), (181, 8138)] },
    { n := 10501, F := 10500, R := 1, a := 2, factors := [2, 2, 3, 5, 5, 5, 7], residues := [(2, 5250), (3, 1923), (5, 1149), (7, 1222)] },
    { n := 10513, F := 10512, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 3, 73], residues := [(2, 5256), (3, 1179), (73, 7656)] },
    { n := 10529, F := 10528, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 7, 47], residues := [(2, 5264), (7, 3668), (47, 5177)] },
    { n := 10531, F := 10530, R := 1, a := 3, factors := [2, 3, 3, 3, 3, 5, 13], residues := [(2, 5265), (3, 1693), (5, 142), (13, 5324)] },
    { n := 10559, F := 10558, R := 1, a := 23, factors := [2, 5279], residues := [(2, 5279), (5279, 20)] },
    { n := 10567, F := 10566, R := 1, a := 6, factors := [2, 3, 3, 587], residues := [(2, 5283), (3, 6649), (587, 3611)] },
    { n := 10589, F := 10588, R := 1, a := 2, factors := [2, 2, 2647], residues := [(2, 5294), (2647, 706)] },
    { n := 10597, F := 10596, R := 1, a := 5, factors := [2, 2, 3, 883], residues := [(2, 5298), (3, 8994), (883, 4434)] },
    { n := 10601, F := 10600, R := 1, a := 3, factors := [2, 2, 2, 5, 5, 53], residues := [(2, 5300), (5, 6830), (53, 8740)] },
    { n := 10607, F := 10606, R := 1, a := 5, factors := [2, 5303], residues := [(2, 5303), (5303, 442)] },
    { n := 10613, F := 10612, R := 1, a := 2, factors := [2, 2, 7, 379], residues := [(2, 5306), (7, 3495), (379, 8518)] },
    { n := 10627, F := 10626, R := 1, a := 5, factors := [2, 3, 7, 11, 23], residues := [(2, 5313), (3, 8513), (7, 6544), (11, 407), (23, 8102)] },
    { n := 10631, F := 10630, R := 1, a := 11, factors := [2, 5, 1063], residues := [(2, 5315), (5, 479), (1063, 4299)] },
    { n := 10639, F := 10638, R := 1, a := 6, factors := [2, 3, 3, 3, 197], residues := [(2, 5319), (3, 4177), (197, 5916)] },
    { n := 10651, F := 10650, R := 1, a := 7, factors := [2, 3, 5, 5, 71], residues := [(2, 5325), (3, 6772), (5, 395), (71, 10055)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData09_valid : PocklingtonRow.Valid lowPocklingtonData09 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPrime_9781 : Nat.Prime 9781 := by
  let d := lowPocklingtonData09.get ⟨0, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9787 : Nat.Prime 9787 := by
  let d := lowPocklingtonData09.get ⟨1, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9791 : Nat.Prime 9791 := by
  let d := lowPocklingtonData09.get ⟨2, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9803 : Nat.Prime 9803 := by
  let d := lowPocklingtonData09.get ⟨3, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9811 : Nat.Prime 9811 := by
  let d := lowPocklingtonData09.get ⟨4, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9817 : Nat.Prime 9817 := by
  let d := lowPocklingtonData09.get ⟨5, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9829 : Nat.Prime 9829 := by
  let d := lowPocklingtonData09.get ⟨6, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9833 : Nat.Prime 9833 := by
  let d := lowPocklingtonData09.get ⟨7, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9839 : Nat.Prime 9839 := by
  let d := lowPocklingtonData09.get ⟨8, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9851 : Nat.Prime 9851 := by
  let d := lowPocklingtonData09.get ⟨9, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9857 : Nat.Prime 9857 := by
  let d := lowPocklingtonData09.get ⟨10, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9859 : Nat.Prime 9859 := by
  let d := lowPocklingtonData09.get ⟨11, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9871 : Nat.Prime 9871 := by
  let d := lowPocklingtonData09.get ⟨12, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9883 : Nat.Prime 9883 := by
  let d := lowPocklingtonData09.get ⟨13, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9887 : Nat.Prime 9887 := by
  let d := lowPocklingtonData09.get ⟨14, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9901 : Nat.Prime 9901 := by
  let d := lowPocklingtonData09.get ⟨15, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9907 : Nat.Prime 9907 := by
  let d := lowPocklingtonData09.get ⟨16, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9923 : Nat.Prime 9923 := by
  let d := lowPocklingtonData09.get ⟨17, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9929 : Nat.Prime 9929 := by
  let d := lowPocklingtonData09.get ⟨18, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9931 : Nat.Prime 9931 := by
  let d := lowPocklingtonData09.get ⟨19, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9941 : Nat.Prime 9941 := by
  let d := lowPocklingtonData09.get ⟨20, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9949 : Nat.Prime 9949 := by
  let d := lowPocklingtonData09.get ⟨21, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9967 : Nat.Prime 9967 := by
  let d := lowPocklingtonData09.get ⟨22, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_9973 : Nat.Prime 9973 := by
  let d := lowPocklingtonData09.get ⟨23, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10007 : Nat.Prime 10007 := by
  let d := lowPocklingtonData09.get ⟨24, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10009 : Nat.Prime 10009 := by
  let d := lowPocklingtonData09.get ⟨25, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10037 : Nat.Prime 10037 := by
  let d := lowPocklingtonData09.get ⟨26, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10039 : Nat.Prime 10039 := by
  let d := lowPocklingtonData09.get ⟨27, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10061 : Nat.Prime 10061 := by
  let d := lowPocklingtonData09.get ⟨28, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10067 : Nat.Prime 10067 := by
  let d := lowPocklingtonData09.get ⟨29, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10069 : Nat.Prime 10069 := by
  let d := lowPocklingtonData09.get ⟨30, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10079 : Nat.Prime 10079 := by
  let d := lowPocklingtonData09.get ⟨31, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10091 : Nat.Prime 10091 := by
  let d := lowPocklingtonData09.get ⟨32, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10093 : Nat.Prime 10093 := by
  let d := lowPocklingtonData09.get ⟨33, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10099 : Nat.Prime 10099 := by
  let d := lowPocklingtonData09.get ⟨34, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10103 : Nat.Prime 10103 := by
  let d := lowPocklingtonData09.get ⟨35, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10111 : Nat.Prime 10111 := by
  let d := lowPocklingtonData09.get ⟨36, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10133 : Nat.Prime 10133 := by
  let d := lowPocklingtonData09.get ⟨37, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10139 : Nat.Prime 10139 := by
  let d := lowPocklingtonData09.get ⟨38, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10141 : Nat.Prime 10141 := by
  let d := lowPocklingtonData09.get ⟨39, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10151 : Nat.Prime 10151 := by
  let d := lowPocklingtonData09.get ⟨40, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10159 : Nat.Prime 10159 := by
  let d := lowPocklingtonData09.get ⟨41, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10163 : Nat.Prime 10163 := by
  let d := lowPocklingtonData09.get ⟨42, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10169 : Nat.Prime 10169 := by
  let d := lowPocklingtonData09.get ⟨43, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10177 : Nat.Prime 10177 := by
  let d := lowPocklingtonData09.get ⟨44, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10181 : Nat.Prime 10181 := by
  let d := lowPocklingtonData09.get ⟨45, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10193 : Nat.Prime 10193 := by
  let d := lowPocklingtonData09.get ⟨46, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10211 : Nat.Prime 10211 := by
  let d := lowPocklingtonData09.get ⟨47, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10223 : Nat.Prime 10223 := by
  let d := lowPocklingtonData09.get ⟨48, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10243 : Nat.Prime 10243 := by
  let d := lowPocklingtonData09.get ⟨49, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10247 : Nat.Prime 10247 := by
  let d := lowPocklingtonData09.get ⟨50, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10253 : Nat.Prime 10253 := by
  let d := lowPocklingtonData09.get ⟨51, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10259 : Nat.Prime 10259 := by
  let d := lowPocklingtonData09.get ⟨52, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10267 : Nat.Prime 10267 := by
  let d := lowPocklingtonData09.get ⟨53, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10271 : Nat.Prime 10271 := by
  let d := lowPocklingtonData09.get ⟨54, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10273 : Nat.Prime 10273 := by
  let d := lowPocklingtonData09.get ⟨55, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10289 : Nat.Prime 10289 := by
  let d := lowPocklingtonData09.get ⟨56, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10301 : Nat.Prime 10301 := by
  let d := lowPocklingtonData09.get ⟨57, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10303 : Nat.Prime 10303 := by
  let d := lowPocklingtonData09.get ⟨58, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10313 : Nat.Prime 10313 := by
  let d := lowPocklingtonData09.get ⟨59, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10321 : Nat.Prime 10321 := by
  let d := lowPocklingtonData09.get ⟨60, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10331 : Nat.Prime 10331 := by
  let d := lowPocklingtonData09.get ⟨61, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10333 : Nat.Prime 10333 := by
  let d := lowPocklingtonData09.get ⟨62, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10337 : Nat.Prime 10337 := by
  let d := lowPocklingtonData09.get ⟨63, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10343 : Nat.Prime 10343 := by
  let d := lowPocklingtonData09.get ⟨64, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10357 : Nat.Prime 10357 := by
  let d := lowPocklingtonData09.get ⟨65, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10369 : Nat.Prime 10369 := by
  let d := lowPocklingtonData09.get ⟨66, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10391 : Nat.Prime 10391 := by
  let d := lowPocklingtonData09.get ⟨67, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10399 : Nat.Prime 10399 := by
  let d := lowPocklingtonData09.get ⟨68, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10427 : Nat.Prime 10427 := by
  let d := lowPocklingtonData09.get ⟨69, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10429 : Nat.Prime 10429 := by
  let d := lowPocklingtonData09.get ⟨70, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10433 : Nat.Prime 10433 := by
  let d := lowPocklingtonData09.get ⟨71, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10453 : Nat.Prime 10453 := by
  let d := lowPocklingtonData09.get ⟨72, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10457 : Nat.Prime 10457 := by
  let d := lowPocklingtonData09.get ⟨73, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10459 : Nat.Prime 10459 := by
  let d := lowPocklingtonData09.get ⟨74, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10463 : Nat.Prime 10463 := by
  let d := lowPocklingtonData09.get ⟨75, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10477 : Nat.Prime 10477 := by
  let d := lowPocklingtonData09.get ⟨76, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10487 : Nat.Prime 10487 := by
  let d := lowPocklingtonData09.get ⟨77, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10499 : Nat.Prime 10499 := by
  let d := lowPocklingtonData09.get ⟨78, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10501 : Nat.Prime 10501 := by
  let d := lowPocklingtonData09.get ⟨79, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10513 : Nat.Prime 10513 := by
  let d := lowPocklingtonData09.get ⟨80, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10529 : Nat.Prime 10529 := by
  let d := lowPocklingtonData09.get ⟨81, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10531 : Nat.Prime 10531 := by
  let d := lowPocklingtonData09.get ⟨82, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10559 : Nat.Prime 10559 := by
  let d := lowPocklingtonData09.get ⟨83, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10567 : Nat.Prime 10567 := by
  let d := lowPocklingtonData09.get ⟨84, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10589 : Nat.Prime 10589 := by
  let d := lowPocklingtonData09.get ⟨85, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10597 : Nat.Prime 10597 := by
  let d := lowPocklingtonData09.get ⟨86, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10601 : Nat.Prime 10601 := by
  let d := lowPocklingtonData09.get ⟨87, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10607 : Nat.Prime 10607 := by
  let d := lowPocklingtonData09.get ⟨88, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10613 : Nat.Prime 10613 := by
  let d := lowPocklingtonData09.get ⟨89, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10627 : Nat.Prime 10627 := by
  let d := lowPocklingtonData09.get ⟨90, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10631 : Nat.Prime 10631 := by
  let d := lowPocklingtonData09.get ⟨91, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10639 : Nat.Prime 10639 := by
  let d := lowPocklingtonData09.get ⟨92, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp

theorem lowPrime_10651 : Nat.Prime 10651 := by
  let d := lowPocklingtonData09.get ⟨93, by simp [lowPocklingtonData09]⟩
  have hd : d ∈ lowPocklingtonData09 := List.get_mem _ _
  have hp := PocklingtonRow.prime_of_mem lowPocklingtonData09_valid hd
  simpa [d, lowPocklingtonData09] using hp
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9769) (q := 9781) (by exact lowPrime_9781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9781) (q := 9787) (by exact lowPrime_9787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9787) (q := 9791) (by exact lowPrime_9791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9791) (q := 9803) (by exact lowPrime_9803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9803) (q := 9811) (by exact lowPrime_9811) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9811) (q := 9817) (by exact lowPrime_9817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9817) (q := 9829) (by exact lowPrime_9829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9829) (q := 9833) (by exact lowPrime_9833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part06_chain :
    DusartPrimeRowsChain 9769 9832 dusartPrimeRows_9419_9900_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9897, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9833) (q := 9839) (by exact lowPrime_9839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9839) (q := 9851) (by exact lowPrime_9851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9851) (q := 9857) (by exact lowPrime_9857) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9857) (q := 9859) (by exact lowPrime_9859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9859) (q := 9871) (by exact lowPrime_9871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9871) (q := 9883) (by exact lowPrime_9883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9883) (q := 9887) (by exact lowPrime_9887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9887) (q := 9901) (by exact lowPrime_9901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part07_chain :
    DusartPrimeRowsChain 9833 9900 dusartPrimeRows_9419_9900_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9897, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 9901) (q := 9907) (by exact lowPrime_9907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9907) (q := 9923) (by exact lowPrime_9923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9923) (q := 9929) (by exact lowPrime_9929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9929) (q := 9931) (by exact lowPrime_9931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9931) (q := 9941) (by exact lowPrime_9941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9941) (q := 9949) (by exact lowPrime_9949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9949) (q := 9967) (by exact lowPrime_9967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9967) (q := 9973) (by exact lowPrime_9973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part01_chain :
    DusartPrimeRowsChain 9901 9972 dusartPrimeRows_9901_10426_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 9973) (q := 10007) (by exact lowPrime_10007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10007) (q := 10009) (by exact lowPrime_10009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10009) (q := 10037) (by exact lowPrime_10037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10037) (q := 10039) (by exact lowPrime_10039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10039) (q := 10061) (by exact lowPrime_10061) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10061) (q := 10067) (by exact lowPrime_10067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10067) (q := 10069) (by exact lowPrime_10069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10069) (q := 10079) (by exact lowPrime_10079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part02_chain :
    DusartPrimeRowsChain 9973 10078 dusartPrimeRows_9901_10426_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10079) (q := 10091) (by exact lowPrime_10091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10091) (q := 10093) (by exact lowPrime_10093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10093) (q := 10099) (by exact lowPrime_10099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10099) (q := 10103) (by exact lowPrime_10103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10103) (q := 10111) (by exact lowPrime_10111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10111) (q := 10133) (by exact lowPrime_10133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10133) (q := 10139) (by exact lowPrime_10139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10139) (q := 10141) (by exact lowPrime_10141) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part03_chain :
    DusartPrimeRowsChain 10079 10140 dusartPrimeRows_9901_10426_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10141) (q := 10151) (by exact lowPrime_10151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10151) (q := 10159) (by exact lowPrime_10159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10159) (q := 10163) (by exact lowPrime_10163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10163) (q := 10169) (by exact lowPrime_10169) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10169) (q := 10177) (by exact lowPrime_10177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10177) (q := 10181) (by exact lowPrime_10181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10181) (q := 10193) (by exact lowPrime_10193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10193) (q := 10211) (by exact lowPrime_10211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part04_chain :
    DusartPrimeRowsChain 10141 10210 dusartPrimeRows_9901_10426_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10211) (q := 10223) (by exact lowPrime_10223) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10223) (q := 10243) (by exact lowPrime_10243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10243) (q := 10247) (by exact lowPrime_10247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10247) (q := 10253) (by exact lowPrime_10253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10253) (q := 10259) (by exact lowPrime_10259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10259) (q := 10267) (by exact lowPrime_10267) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10267) (q := 10271) (by exact lowPrime_10271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10271) (q := 10273) (by exact lowPrime_10273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part05_chain :
    DusartPrimeRowsChain 10211 10272 dusartPrimeRows_9901_10426_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10273) (q := 10289) (by exact lowPrime_10289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10289) (q := 10301) (by exact lowPrime_10301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10301) (q := 10303) (by exact lowPrime_10303) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10303) (q := 10313) (by exact lowPrime_10313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10313) (q := 10321) (by exact lowPrime_10321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10321) (q := 10331) (by exact lowPrime_10331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10331) (q := 10333) (by exact lowPrime_10333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10333) (q := 10337) (by exact lowPrime_10337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part06_chain :
    DusartPrimeRowsChain 10273 10336 dusartPrimeRows_9901_10426_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10337) (q := 10343) (by exact lowPrime_10343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10343) (q := 10357) (by exact lowPrime_10357) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10357) (q := 10369) (by exact lowPrime_10369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10369) (q := 10391) (by exact lowPrime_10391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10391) (q := 10399) (by exact lowPrime_10399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10399) (q := 10427) (by exact lowPrime_10427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part07_chain :
    DusartPrimeRowsChain 10337 10426 dusartPrimeRows_9901_10426_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10427) (q := 10429) (by exact lowPrime_10429) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10429) (q := 10433) (by exact lowPrime_10433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10433) (q := 10453) (by exact lowPrime_10453) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10453) (q := 10457) (by exact lowPrime_10457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10457) (q := 10459) (by exact lowPrime_10459) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10459) (q := 10463) (by exact lowPrime_10463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10463) (q := 10477) (by exact lowPrime_10477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10477) (q := 10487) (by exact lowPrime_10487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part01_chain :
    DusartPrimeRowsChain 10427 10486 dusartPrimeRows_10427_10938_part01 := by
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
def dusartPrimeRows_10427_10938_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10487) (q := 10499) (by exact lowPrime_10499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10499) (q := 10501) (by exact lowPrime_10501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10501) (q := 10513) (by exact lowPrime_10513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10513) (q := 10529) (by exact lowPrime_10529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10529) (q := 10531) (by exact lowPrime_10531) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10531) (q := 10559) (by exact lowPrime_10559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10559) (q := 10567) (by exact lowPrime_10567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10567) (q := 10589) (by exact lowPrime_10589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part02_chain :
    DusartPrimeRowsChain 10487 10588 dusartPrimeRows_10427_10938_part02 := by
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
def dusartPrimeRows_10427_10938_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10589) (q := 10597) (by exact lowPrime_10597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10597) (q := 10601) (by exact lowPrime_10601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10601) (q := 10607) (by exact lowPrime_10607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10607) (q := 10613) (by exact lowPrime_10613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10613) (q := 10627) (by exact lowPrime_10627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10627) (q := 10631) (by exact lowPrime_10631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10631) (q := 10639) (by exact lowPrime_10639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10639) (q := 10651) (by exact lowPrime_10651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part03_chain :
    DusartPrimeRowsChain 10589 10650 dusartPrimeRows_10427_10938_part03 := by
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
