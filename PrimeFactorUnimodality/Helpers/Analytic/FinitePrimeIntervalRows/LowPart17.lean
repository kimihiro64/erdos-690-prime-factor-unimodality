import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 17 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData17 : List PocklingtonData := [
    { n := 16729, F := 16728, R := 1, a := 13, factors := [2, 2, 2, 3, 17, 41], residues := [(2, 8364), (3, 325), (17, 14273), (41, 1340)] },
    { n := 16741, F := 16740, R := 1, a := 6, factors := [2, 2, 3, 3, 3, 5, 31], residues := [(2, 8370), (3, 3520), (5, 13235), (31, 3682)] },
    { n := 16747, F := 16746, R := 1, a := 2, factors := [2, 3, 2791], residues := [(2, 8373), (3, 6345), (2791, 6114)] },
    { n := 16759, F := 16758, R := 1, a := 3, factors := [2, 3, 3, 7, 7, 19], residues := [(2, 8379), (3, 7486), (7, 10073), (19, 4462)] },
    { n := 16763, F := 16762, R := 1, a := 2, factors := [2, 17, 17, 29], residues := [(2, 8381), (17, 13910), (29, 11981)] },
    { n := 16787, F := 16786, R := 1, a := 2, factors := [2, 7, 11, 109], residues := [(2, 8393), (7, 5058), (11, 9470), (109, 14089)] },
    { n := 16811, F := 16810, R := 1, a := 7, factors := [2, 5, 41, 41], residues := [(2, 8405), (5, 797), (41, 3638)] },
    { n := 16823, F := 16822, R := 1, a := 5, factors := [2, 13, 647], residues := [(2, 8411), (13, 8826), (647, 14076)] },
    { n := 16829, F := 16828, R := 1, a := 2, factors := [2, 2, 7, 601], residues := [(2, 8414), (7, 5286), (601, 8719)] },
    { n := 16831, F := 16830, R := 1, a := 6, factors := [2, 3, 3, 5, 11, 17], residues := [(2, 8415), (3, 6238), (5, 14600), (11, 8242), (17, 12925)] },
    { n := 16843, F := 16842, R := 1, a := 2, factors := [2, 3, 7, 401], residues := [(2, 8421), (3, 3473), (7, 9970), (401, 13658)] },
    { n := 16871, F := 16870, R := 1, a := 17, factors := [2, 5, 7, 241], residues := [(2, 8435), (5, 12599), (7, 3606), (241, 15674)] },
    { n := 16879, F := 16878, R := 1, a := 3, factors := [2, 3, 29, 97], residues := [(2, 8439), (3, 12640), (29, 3130), (97, 954)] },
    { n := 16883, F := 16882, R := 1, a := 2, factors := [2, 23, 367], residues := [(2, 8441), (23, 212), (367, 10012)] },
    { n := 16889, F := 16888, R := 1, a := 3, factors := [2, 2, 2, 2111], residues := [(2, 8444), (2111, 10275)] },
    { n := 16901, F := 16900, R := 1, a := 2, factors := [2, 2, 5, 5, 13, 13], residues := [(2, 8450), (5, 9164), (13, 4377)] },
    { n := 16903, F := 16902, R := 1, a := 3, factors := [2, 3, 3, 3, 313], residues := [(2, 8451), (3, 14107), (313, 2649)] },
    { n := 16921, F := 16920, R := 1, a := 17, factors := [2, 2, 2, 3, 3, 5, 47], residues := [(2, 8460), (3, 7089), (5, 3900), (47, 8249)] },
    { n := 16927, F := 16926, R := 1, a := 6, factors := [2, 3, 7, 13, 31], residues := [(2, 8463), (3, 6575), (7, 9950), (13, 6954), (31, 12642)] },
    { n := 16931, F := 16930, R := 1, a := 2, factors := [2, 5, 1693], residues := [(2, 8465), (5, 6655), (1693, 14465)] },
    { n := 16937, F := 16936, R := 1, a := 3, factors := [2, 2, 2, 29, 73], residues := [(2, 8468), (29, 12706), (73, 8118)] },
    { n := 16943, F := 16942, R := 1, a := 5, factors := [2, 43, 197], residues := [(2, 8471), (43, 16517), (197, 13077)] },
    { n := 16963, F := 16962, R := 1, a := 2, factors := [2, 3, 11, 257], residues := [(2, 8481), (3, 16347), (11, 10137), (257, 1187)] },
    { n := 16979, F := 16978, R := 1, a := 2, factors := [2, 13, 653], residues := [(2, 8489), (13, 2205), (653, 4509)] },
    { n := 16981, F := 16980, R := 1, a := 2, factors := [2, 2, 3, 5, 283], residues := [(2, 8490), (3, 3171), (5, 7523), (283, 12875)] },
    { n := 16987, F := 16986, R := 1, a := 3, factors := [2, 3, 19, 149], residues := [(2, 8493), (3, 8329), (19, 10209), (149, 8619)] },
    { n := 16993, F := 16992, R := 1, a := 10, factors := [2, 2, 2, 2, 2, 3, 3, 59], residues := [(2, 8496), (3, 5968), (59, 16295)] },
    { n := 17011, F := 17010, R := 1, a := 2, factors := [2, 3, 3, 3, 3, 3, 5, 7], residues := [(2, 8505), (3, 3456), (5, 1151), (7, 2262)] },
    { n := 17021, F := 17020, R := 1, a := 2, factors := [2, 2, 5, 23, 37], residues := [(2, 8510), (5, 936), (23, 16062), (37, 4600)] },
    { n := 17027, F := 17026, R := 1, a := 2, factors := [2, 8513], residues := [(2, 8513), (8513, 5676)] },
    { n := 17029, F := 17028, R := 1, a := 10, factors := [2, 2, 3, 3, 11, 43], residues := [(2, 8514), (3, 3836), (11, 5398), (43, 13588)] },
    { n := 17033, F := 17032, R := 1, a := 3, factors := [2, 2, 2, 2129], residues := [(2, 8516), (2129, 16885)] },
    { n := 17041, F := 17040, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 5, 71], residues := [(2, 8520), (3, 6579), (5, 11879), (71, 11407)] },
    { n := 17047, F := 17046, R := 1, a := 3, factors := [2, 3, 3, 947], residues := [(2, 8523), (3, 15014), (947, 14845)] },
    { n := 17053, F := 17052, R := 1, a := 2, factors := [2, 2, 3, 7, 7, 29], residues := [(2, 8526), (3, 5799), (7, 2777), (29, 8183)] },
    { n := 17077, F := 17076, R := 1, a := 2, factors := [2, 2, 3, 1423], residues := [(2, 8538), (3, 6079), (1423, 196)] },
    { n := 17093, F := 17092, R := 1, a := 2, factors := [2, 2, 4273], residues := [(2, 8546), (4273, 14814)] },
    { n := 17099, F := 17098, R := 1, a := 2, factors := [2, 83, 103], residues := [(2, 8549), (83, 2890), (103, 10337)] },
    { n := 17107, F := 17106, R := 1, a := 3, factors := [2, 3, 2851], residues := [(2, 8553), (3, 13670), (2851, 8577)] },
    { n := 17117, F := 17116, R := 1, a := 3, factors := [2, 2, 11, 389], residues := [(2, 8558), (11, 10599), (389, 13612)] },
    { n := 17123, F := 17122, R := 1, a := 2, factors := [2, 7, 1223], residues := [(2, 8561), (7, 13933), (1223, 10806)] },
    { n := 17137, F := 17136, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 3, 7, 17], residues := [(2, 8568), (3, 7305), (7, 2426), (17, 3987)] },
    { n := 17159, F := 17158, R := 1, a := 7, factors := [2, 23, 373], residues := [(2, 8579), (23, 6315), (373, 2160)] },
    { n := 22031, F := 22030, R := 1, a := 7, factors := [2, 5, 2203], residues := [(2, 11015), (5, 12806), (2203, 9093)] },
    { n := 22037, F := 22036, R := 1, a := 2, factors := [2, 2, 7, 787], residues := [(2, 11018), (7, 23), (787, 16324)] },
    { n := 22039, F := 22038, R := 1, a := 6, factors := [2, 3, 3673], residues := [(2, 11019), (3, 6906), (3673, 13846)] },
    { n := 22051, F := 22050, R := 1, a := 3, factors := [2, 3, 3, 5, 5, 7, 7], residues := [(2, 11025), (3, 521), (5, 21079), (7, 2537)] },
    { n := 22063, F := 22062, R := 1, a := 5, factors := [2, 3, 3677], residues := [(2, 11031), (3, 2881), (3677, 14631)] },
    { n := 22067, F := 22066, R := 1, a := 2, factors := [2, 11, 17, 59], residues := [(2, 11033), (11, 8945), (17, 9097), (59, 3101)] },
    { n := 22073, F := 22072, R := 1, a := 3, factors := [2, 2, 2, 31, 89], residues := [(2, 11036), (31, 5739), (89, 14510)] },
    { n := 22079, F := 22078, R := 1, a := 7, factors := [2, 7, 19, 83], residues := [(2, 11039), (7, 1577), (19, 14255), (83, 10687)] },
    { n := 22091, F := 22090, R := 1, a := 2, factors := [2, 5, 47, 47], residues := [(2, 11045), (5, 13199), (47, 19591)] },
    { n := 22093, F := 22092, R := 1, a := 6, factors := [2, 2, 3, 7, 263], residues := [(2, 11046), (3, 12441), (7, 6467), (263, 4244)] },
    { n := 22109, F := 22108, R := 1, a := 2, factors := [2, 2, 5527], residues := [(2, 11054), (5527, 1474)] },
    { n := 22111, F := 22110, R := 1, a := 6, factors := [2, 3, 5, 11, 67], residues := [(2, 11055), (3, 19491), (5, 4495), (11, 11410), (67, 13421)] },
    { n := 22123, F := 22122, R := 1, a := 2, factors := [2, 3, 3, 1229], residues := [(2, 11061), (3, 19199), (1229, 6538)] },
    { n := 22129, F := 22128, R := 1, a := 19, factors := [2, 2, 2, 2, 3, 461], residues := [(2, 11064), (3, 13918), (461, 4478)] },
    { n := 22133, F := 22132, R := 1, a := 2, factors := [2, 2, 11, 503], residues := [(2, 11066), (11, 11868), (503, 15274)] },
    { n := 22147, F := 22146, R := 1, a := 5, factors := [2, 3, 3691], residues := [(2, 11073), (3, 11896), (3691, 8376)] },
    { n := 22153, F := 22152, R := 1, a := 5, factors := [2, 2, 2, 3, 13, 71], residues := [(2, 11076), (3, 18623), (13, 17802), (71, 10450)] },
    { n := 22157, F := 22156, R := 1, a := 2, factors := [2, 2, 29, 191], residues := [(2, 11078), (29, 13731), (191, 2913)] },
    { n := 22159, F := 22158, R := 1, a := 6, factors := [2, 3, 3, 1231], residues := [(2, 11079), (3, 8559), (1231, 19546)] },
    { n := 22171, F := 22170, R := 1, a := 2, factors := [2, 3, 5, 739], residues := [(2, 11085), (3, 6439), (5, 2686), (739, 10972)] },
    { n := 22189, F := 22188, R := 1, a := 2, factors := [2, 2, 3, 43, 43], residues := [(2, 11094), (3, 11137), (43, 7750)] },
    { n := 22193, F := 22192, R := 1, a := 3, factors := [2, 2, 2, 2, 19, 73], residues := [(2, 11096), (19, 9477), (73, 3123)] },
    { n := 22229, F := 22228, R := 1, a := 2, factors := [2, 2, 5557], residues := [(2, 11114), (5557, 1482)] },
    { n := 22247, F := 22246, R := 1, a := 5, factors := [2, 7, 7, 227], residues := [(2, 11123), (7, 2047), (227, 14598)] },
    { n := 22259, F := 22258, R := 1, a := 2, factors := [2, 31, 359], residues := [(2, 11129), (31, 13068), (359, 20668)] },
    { n := 22271, F := 22270, R := 1, a := 7, factors := [2, 5, 17, 131], residues := [(2, 11135), (5, 20357), (17, 16307), (131, 10649)] },
    { n := 22273, F := 22272, R := 1, a := 5, factors := [2, 2, 2, 2, 2, 2, 2, 2, 3, 29], residues := [(2, 11136), (3, 4211), (29, 527)] },
    { n := 22277, F := 22276, R := 1, a := 2, factors := [2, 2, 5569], residues := [(2, 11138), (5569, 10396)] },
    { n := 22279, F := 22278, R := 1, a := 3, factors := [2, 3, 47, 79], residues := [(2, 11139), (3, 11025), (47, 4178), (79, 246)] },
    { n := 22283, F := 22282, R := 1, a := 2, factors := [2, 13, 857], residues := [(2, 11141), (13, 15929), (857, 20097)] },
    { n := 22291, F := 22290, R := 1, a := 3, factors := [2, 3, 5, 743], residues := [(2, 11145), (3, 20400), (5, 8415), (743, 353)] },
    { n := 22303, F := 22302, R := 1, a := 6, factors := [2, 3, 3, 3, 7, 59], residues := [(2, 11151), (3, 14591), (7, 5281), (59, 3015)] },
    { n := 22307, F := 22306, R := 1, a := 2, factors := [2, 19, 587], residues := [(2, 11153), (19, 13889), (587, 4830)] },
    { n := 22343, F := 22342, R := 1, a := 5, factors := [2, 11171], residues := [(2, 11171), (11171, 931)] },
    { n := 22349, F := 22348, R := 1, a := 2, factors := [2, 2, 37, 151], residues := [(2, 11174), (37, 17575), (151, 8599)] },
    { n := 22367, F := 22366, R := 1, a := 5, factors := [2, 53, 211], residues := [(2, 11183), (53, 14036), (211, 4953)] },
    { n := 22369, F := 22368, R := 1, a := 11, factors := [2, 2, 2, 2, 2, 3, 233], residues := [(2, 11184), (3, 19376), (233, 5263)] },
    { n := 22381, F := 22380, R := 1, a := 10, factors := [2, 2, 3, 5, 373], residues := [(2, 11190), (3, 18332), (5, 20919), (373, 10765)] },
    { n := 22391, F := 22390, R := 1, a := 13, factors := [2, 5, 2239], residues := [(2, 11195), (5, 14692), (2239, 4166)] },
    { n := 22397, F := 22396, R := 1, a := 2, factors := [2, 2, 11, 509], residues := [(2, 11198), (11, 13246), (509, 14664)] },
    { n := 22409, F := 22408, R := 1, a := 3, factors := [2, 2, 2, 2801], residues := [(2, 11204), (2801, 13360)] },
    { n := 22433, F := 22432, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 701], residues := [(2, 11216), (701, 14039)] },
    { n := 22441, F := 22440, R := 1, a := 14, factors := [2, 2, 2, 3, 5, 11, 17], residues := [(2, 11220), (3, 675), (5, 21885), (11, 4262), (17, 2905)] },
    { n := 22447, F := 22446, R := 1, a := 3, factors := [2, 3, 3, 29, 43], residues := [(2, 11223), (3, 86), (29, 7450), (43, 4822)] },
    { n := 22453, F := 22452, R := 1, a := 5, factors := [2, 2, 3, 1871], residues := [(2, 11226), (3, 8998), (1871, 16562)] },
    { n := 22469, F := 22468, R := 1, a := 2, factors := [2, 2, 41, 137], residues := [(2, 11234), (41, 140), (137, 17659)] },
    { n := 22481, F := 22480, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 281], residues := [(2, 11240), (5, 16281), (281, 1593)] },
    { n := 22483, F := 22482, R := 1, a := 2, factors := [2, 3, 3, 1249], residues := [(2, 11241), (3, 11482), (1249, 9116)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData17_valid : PocklingtonRow.Valid lowPocklingtonData17 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime17 (i : Fin lowPocklingtonData17.length) :
    Nat.Prime (lowPocklingtonData17.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData17_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16703) (q := 16729) (by
      have hp := lowPocklingtonPrime17 ⟨0, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16729) (q := 16741) (by
      have hp := lowPocklingtonPrime17 ⟨1, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16741) (q := 16747) (by
      have hp := lowPocklingtonPrime17 ⟨2, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16747) (q := 16759) (by
      have hp := lowPocklingtonPrime17 ⟨3, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16759) (q := 16763) (by
      have hp := lowPocklingtonPrime17 ⟨4, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16763) (q := 16787) (by
      have hp := lowPocklingtonPrime17 ⟨5, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16787) (q := 16811) (by
      have hp := lowPocklingtonPrime17 ⟨6, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16811) (q := 16823) (by
      have hp := lowPocklingtonPrime17 ⟨7, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part06_chain :
    DusartPrimeRowsChain 16703 16822 dusartPrimeRows_16319_17158_part06 := by
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
def dusartPrimeRows_16319_17158_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16823) (q := 16829) (by
      have hp := lowPocklingtonPrime17 ⟨8, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16829) (q := 16831) (by
      have hp := lowPocklingtonPrime17 ⟨9, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16831) (q := 16843) (by
      have hp := lowPocklingtonPrime17 ⟨10, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16843) (q := 16871) (by
      have hp := lowPocklingtonPrime17 ⟨11, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16871) (q := 16879) (by
      have hp := lowPocklingtonPrime17 ⟨12, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16879) (q := 16883) (by
      have hp := lowPocklingtonPrime17 ⟨13, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16883) (q := 16889) (by
      have hp := lowPocklingtonPrime17 ⟨14, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16889) (q := 16901) (by
      have hp := lowPocklingtonPrime17 ⟨15, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part07_chain :
    DusartPrimeRowsChain 16823 16900 dusartPrimeRows_16319_17158_part07 := by
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
def dusartPrimeRows_16319_17158_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16901) (q := 16903) (by
      have hp := lowPocklingtonPrime17 ⟨16, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16903) (q := 16921) (by
      have hp := lowPocklingtonPrime17 ⟨17, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16921) (q := 16927) (by
      have hp := lowPocklingtonPrime17 ⟨18, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16927) (q := 16931) (by
      have hp := lowPocklingtonPrime17 ⟨19, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16931) (q := 16937) (by
      have hp := lowPocklingtonPrime17 ⟨20, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16937) (q := 16943) (by
      have hp := lowPocklingtonPrime17 ⟨21, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16943) (q := 16963) (by
      have hp := lowPocklingtonPrime17 ⟨22, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16963) (q := 16979) (by
      have hp := lowPocklingtonPrime17 ⟨23, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part08_chain :
    DusartPrimeRowsChain 16901 16978 dusartPrimeRows_16319_17158_part08 := by
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
def dusartPrimeRows_16319_17158_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16979) (q := 16981) (by
      have hp := lowPocklingtonPrime17 ⟨24, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16981) (q := 16987) (by
      have hp := lowPocklingtonPrime17 ⟨25, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16987) (q := 16993) (by
      have hp := lowPocklingtonPrime17 ⟨26, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16993) (q := 17011) (by
      have hp := lowPocklingtonPrime17 ⟨27, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17011) (q := 17021) (by
      have hp := lowPocklingtonPrime17 ⟨28, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17021) (q := 17027) (by
      have hp := lowPocklingtonPrime17 ⟨29, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17027) (q := 17029) (by
      have hp := lowPocklingtonPrime17 ⟨30, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17029) (q := 17033) (by
      have hp := lowPocklingtonPrime17 ⟨31, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part09_chain :
    DusartPrimeRowsChain 16979 17032 dusartPrimeRows_16319_17158_part09 := by
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
def dusartPrimeRows_16319_17158_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 17033) (q := 17041) (by
      have hp := lowPocklingtonPrime17 ⟨32, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17041) (q := 17047) (by
      have hp := lowPocklingtonPrime17 ⟨33, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17047) (q := 17053) (by
      have hp := lowPocklingtonPrime17 ⟨34, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17053) (q := 17077) (by
      have hp := lowPocklingtonPrime17 ⟨35, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17077) (q := 17093) (by
      have hp := lowPocklingtonPrime17 ⟨36, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17093) (q := 17099) (by
      have hp := lowPocklingtonPrime17 ⟨37, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17099) (q := 17107) (by
      have hp := lowPocklingtonPrime17 ⟨38, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17107) (q := 17117) (by
      have hp := lowPocklingtonPrime17 ⟨39, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part10_chain :
    DusartPrimeRowsChain 17033 17116 dusartPrimeRows_16319_17158_part10 := by
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
def dusartPrimeRows_16319_17158_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 17117) (q := 17123) (by
      have hp := lowPocklingtonPrime17 ⟨40, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17123) (q := 17137) (by
      have hp := lowPocklingtonPrime17 ⟨41, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17137) (q := 17159) (by
      have hp := lowPocklingtonPrime17 ⟨42, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part11_chain :
    DusartPrimeRowsChain 17117 17158 dusartPrimeRows_16319_17158_part11 := by
  apply DusartPrimeRowsChain.cons
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
def dusartPrimeRows_22027_23158_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22027) (q := 22031) (by
      have hp := lowPocklingtonPrime17 ⟨43, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22031) (q := 22037) (by
      have hp := lowPocklingtonPrime17 ⟨44, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22037) (q := 22039) (by
      have hp := lowPocklingtonPrime17 ⟨45, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22039) (q := 22051) (by
      have hp := lowPocklingtonPrime17 ⟨46, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22051) (q := 22063) (by
      have hp := lowPocklingtonPrime17 ⟨47, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22063) (q := 22067) (by
      have hp := lowPocklingtonPrime17 ⟨48, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22067) (q := 22073) (by
      have hp := lowPocklingtonPrime17 ⟨49, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22073) (q := 22079) (by
      have hp := lowPocklingtonPrime17 ⟨50, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part01_chain :
    DusartPrimeRowsChain 22027 22078 dusartPrimeRows_22027_23158_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22079) (q := 22091) (by
      have hp := lowPocklingtonPrime17 ⟨51, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22091) (q := 22093) (by
      have hp := lowPocklingtonPrime17 ⟨52, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22093) (q := 22109) (by
      have hp := lowPocklingtonPrime17 ⟨53, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22109) (q := 22111) (by
      have hp := lowPocklingtonPrime17 ⟨54, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22111) (q := 22123) (by
      have hp := lowPocklingtonPrime17 ⟨55, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22123) (q := 22129) (by
      have hp := lowPocklingtonPrime17 ⟨56, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22129) (q := 22133) (by
      have hp := lowPocklingtonPrime17 ⟨57, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22133) (q := 22147) (by
      have hp := lowPocklingtonPrime17 ⟨58, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part02_chain :
    DusartPrimeRowsChain 22079 22146 dusartPrimeRows_22027_23158_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22147) (q := 22153) (by
      have hp := lowPocklingtonPrime17 ⟨59, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22153) (q := 22157) (by
      have hp := lowPocklingtonPrime17 ⟨60, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22157) (q := 22159) (by
      have hp := lowPocklingtonPrime17 ⟨61, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22159) (q := 22171) (by
      have hp := lowPocklingtonPrime17 ⟨62, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22171) (q := 22189) (by
      have hp := lowPocklingtonPrime17 ⟨63, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22189) (q := 22193) (by
      have hp := lowPocklingtonPrime17 ⟨64, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22193) (q := 22229) (by
      have hp := lowPocklingtonPrime17 ⟨65, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22229) (q := 22247) (by
      have hp := lowPocklingtonPrime17 ⟨66, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part03_chain :
    DusartPrimeRowsChain 22147 22246 dusartPrimeRows_22027_23158_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22247) (q := 22259) (by
      have hp := lowPocklingtonPrime17 ⟨67, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22259) (q := 22271) (by
      have hp := lowPocklingtonPrime17 ⟨68, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22271) (q := 22273) (by
      have hp := lowPocklingtonPrime17 ⟨69, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22273) (q := 22277) (by
      have hp := lowPocklingtonPrime17 ⟨70, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22277) (q := 22279) (by
      have hp := lowPocklingtonPrime17 ⟨71, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22279) (q := 22283) (by
      have hp := lowPocklingtonPrime17 ⟨72, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22283) (q := 22291) (by
      have hp := lowPocklingtonPrime17 ⟨73, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22291) (q := 22303) (by
      have hp := lowPocklingtonPrime17 ⟨74, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part04_chain :
    DusartPrimeRowsChain 22247 22302 dusartPrimeRows_22027_23158_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22303) (q := 22307) (by
      have hp := lowPocklingtonPrime17 ⟨75, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22307) (q := 22343) (by
      have hp := lowPocklingtonPrime17 ⟨76, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22343) (q := 22349) (by
      have hp := lowPocklingtonPrime17 ⟨77, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22349) (q := 22367) (by
      have hp := lowPocklingtonPrime17 ⟨78, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22367) (q := 22369) (by
      have hp := lowPocklingtonPrime17 ⟨79, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22369) (q := 22381) (by
      have hp := lowPocklingtonPrime17 ⟨80, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22381) (q := 22391) (by
      have hp := lowPocklingtonPrime17 ⟨81, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22391) (q := 22397) (by
      have hp := lowPocklingtonPrime17 ⟨82, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part05_chain :
    DusartPrimeRowsChain 22303 22396 dusartPrimeRows_22027_23158_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22397) (q := 22409) (by
      have hp := lowPocklingtonPrime17 ⟨83, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22409) (q := 22433) (by
      have hp := lowPocklingtonPrime17 ⟨84, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22433) (q := 22441) (by
      have hp := lowPocklingtonPrime17 ⟨85, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22441) (q := 22447) (by
      have hp := lowPocklingtonPrime17 ⟨86, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22447) (q := 22453) (by
      have hp := lowPocklingtonPrime17 ⟨87, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22453) (q := 22469) (by
      have hp := lowPocklingtonPrime17 ⟨88, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22469) (q := 22481) (by
      have hp := lowPocklingtonPrime17 ⟨89, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22481) (q := 22483) (by
      have hp := lowPocklingtonPrime17 ⟨90, by simp [lowPocklingtonData17]⟩
      simpa [lowPocklingtonData17] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part06_chain :
    DusartPrimeRowsChain 22397 22482 dusartPrimeRows_22027_23158_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]
