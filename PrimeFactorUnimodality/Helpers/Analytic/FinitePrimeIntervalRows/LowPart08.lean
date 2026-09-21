import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase
import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowPart07


set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 08 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData08 : List PocklingtonData := [
    { n := 8969, F := 8968, R := 1, a := 3, factors := [2, 2, 2, 19, 59], residues := [(2, 4484), (19, 5749), (59, 5118)] },
    { n := 8971, F := 8970, R := 1, a := 2, factors := [2, 3, 5, 13, 23], residues := [(2, 4485), (3, 6094), (5, 8016), (13, 3263), (23, 6727)] },
    { n := 8999, F := 8998, R := 1, a := 7, factors := [2, 11, 409], residues := [(2, 4499), (11, 6640), (409, 1291)] },
    { n := 9001, F := 9000, R := 1, a := 7, factors := [2, 2, 2, 3, 3, 5, 5, 5], residues := [(2, 4500), (3, 4266), (5, 4608)] },
    { n := 9007, F := 9006, R := 1, a := 3, factors := [2, 3, 19, 79], residues := [(2, 4503), (3, 6369), (19, 5491), (79, 3381)] },
    { n := 9011, F := 9010, R := 1, a := 2, factors := [2, 5, 17, 53], residues := [(2, 4505), (5, 4931), (17, 5686), (53, 7138)] },
    { n := 9013, F := 9012, R := 1, a := 5, factors := [2, 2, 3, 751], residues := [(2, 4506), (3, 1108), (751, 402)] },
    { n := 9029, F := 9028, R := 1, a := 2, factors := [2, 2, 37, 61], residues := [(2, 4514), (37, 1906), (61, 1880)] },
    { n := 9041, F := 9040, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 113], residues := [(2, 4520), (5, 6185), (113, 2530)] },
    { n := 9043, F := 9042, R := 1, a := 3, factors := [2, 3, 11, 137], residues := [(2, 4521), (3, 7079), (11, 2545), (137, 4942)] },
    { n := 9049, F := 9048, R := 1, a := 7, factors := [2, 2, 2, 3, 13, 29], residues := [(2, 4524), (3, 2734), (13, 8631), (29, 8210)] },
    { n := 9059, F := 9058, R := 1, a := 2, factors := [2, 7, 647], residues := [(2, 4529), (7, 8032), (647, 3232)] },
    { n := 9067, F := 9066, R := 1, a := 3, factors := [2, 3, 1511], residues := [(2, 4533), (3, 8706), (1511, 8930)] },
    { n := 9091, F := 9090, R := 1, a := 3, factors := [2, 3, 3, 5, 101], residues := [(2, 4545), (3, 1129), (5, 3214), (101, 5371)] },
    { n := 9103, F := 9102, R := 1, a := 6, factors := [2, 3, 37, 41], residues := [(2, 4551), (3, 1574), (37, 8168), (41, 7338)] },
    { n := 9109, F := 9108, R := 1, a := 10, factors := [2, 2, 3, 3, 11, 23], residues := [(2, 4554), (3, 5032), (11, 2742), (23, 975)] },
    { n := 9127, F := 9126, R := 1, a := 3, factors := [2, 3, 3, 3, 13, 13], residues := [(2, 4563), (3, 8123), (13, 153)] },
    { n := 9133, F := 9132, R := 1, a := 6, factors := [2, 2, 3, 761], residues := [(2, 4566), (3, 7354), (761, 7856)] },
    { n := 9137, F := 9136, R := 1, a := 3, factors := [2, 2, 2, 2, 571], residues := [(2, 4568), (571, 4211)] },
    { n := 9151, F := 9150, R := 1, a := 3, factors := [2, 3, 5, 5, 61], residues := [(2, 4575), (3, 6492), (5, 8634), (61, 6104)] },
    { n := 9157, F := 9156, R := 1, a := 6, factors := [2, 2, 3, 7, 109], residues := [(2, 4578), (3, 8725), (7, 6761), (109, 7139)] },
    { n := 9161, F := 9160, R := 1, a := 3, factors := [2, 2, 2, 5, 229], residues := [(2, 4580), (5, 6445), (229, 6446)] },
    { n := 9173, F := 9172, R := 1, a := 2, factors := [2, 2, 2293], residues := [(2, 4586), (2293, 7950)] },
    { n := 9181, F := 9180, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 5, 17], residues := [(2, 4590), (3, 8844), (5, 2450), (17, 4952)] },
    { n := 9187, F := 9186, R := 1, a := 3, factors := [2, 3, 1531], residues := [(2, 4593), (3, 1688), (1531, 2587)] },
    { n := 9199, F := 9198, R := 1, a := 3, factors := [2, 3, 3, 7, 73], residues := [(2, 4599), (3, 7388), (7, 6854), (73, 4952)] },
    { n := 9203, F := 9202, R := 1, a := 2, factors := [2, 43, 107], residues := [(2, 4601), (43, 823), (107, 8760)] },
    { n := 9209, F := 9208, R := 1, a := 3, factors := [2, 2, 2, 1151], residues := [(2, 4604), (1151, 5378)] },
    { n := 9221, F := 9220, R := 1, a := 2, factors := [2, 2, 5, 461], residues := [(2, 4610), (5, 3946), (461, 6091)] },
    { n := 9227, F := 9226, R := 1, a := 2, factors := [2, 7, 659], residues := [(2, 4613), (7, 8015), (659, 3591)] },
    { n := 9239, F := 9238, R := 1, a := 19, factors := [2, 31, 149], residues := [(2, 4619), (31, 8339), (149, 2649)] },
    { n := 9241, F := 9240, R := 1, a := 13, factors := [2, 2, 2, 3, 5, 7, 11], residues := [(2, 4620), (3, 55), (5, 3810), (7, 7833), (11, 4937)] },
    { n := 9257, F := 9256, R := 1, a := 3, factors := [2, 2, 2, 13, 89], residues := [(2, 4628), (13, 9089), (89, 2232)] },
    { n := 9277, F := 9276, R := 1, a := 5, factors := [2, 2, 3, 773], residues := [(2, 4638), (3, 200), (773, 501)] },
    { n := 9281, F := 9280, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 5, 29], residues := [(2, 4640), (5, 5274), (29, 2969)] },
    { n := 9283, F := 9282, R := 1, a := 2, factors := [2, 3, 7, 13, 17], residues := [(2, 4641), (3, 7136), (7, 668), (13, 1880), (17, 5129)] },
    { n := 9293, F := 9292, R := 1, a := 2, factors := [2, 2, 23, 101], residues := [(2, 4646), (23, 7818), (101, 9230)] },
    { n := 9311, F := 9310, R := 1, a := 7, factors := [2, 5, 7, 7, 19], residues := [(2, 4655), (5, 2945), (7, 780), (19, 6720)] },
    { n := 9319, F := 9318, R := 1, a := 3, factors := [2, 3, 1553], residues := [(2, 4659), (3, 5166), (1553, 3085)] },
    { n := 9323, F := 9322, R := 1, a := 2, factors := [2, 59, 79], residues := [(2, 4661), (59, 330), (79, 5173)] },
    { n := 9337, F := 9336, R := 1, a := 5, factors := [2, 2, 2, 3, 389], residues := [(2, 4668), (3, 1466), (389, 6887)] },
    { n := 9341, F := 9340, R := 1, a := 2, factors := [2, 2, 5, 467], residues := [(2, 4670), (5, 1454), (467, 8314)] },
    { n := 9343, F := 9342, R := 1, a := 5, factors := [2, 3, 3, 3, 173], residues := [(2, 4671), (3, 2037), (173, 6134)] },
    { n := 9349, F := 9348, R := 1, a := 2, factors := [2, 2, 3, 19, 41], residues := [(2, 4674), (3, 4892), (19, 1444), (41, 7422)] },
    { n := 9371, F := 9370, R := 1, a := 2, factors := [2, 5, 937], residues := [(2, 4685), (5, 503), (937, 8171)] },
    { n := 9377, F := 9376, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 293], residues := [(2, 4688), (293, 6938)] },
    { n := 9391, F := 9390, R := 1, a := 3, factors := [2, 3, 5, 313], residues := [(2, 4695), (3, 2802), (5, 5086), (313, 3807)] },
    { n := 9397, F := 9396, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 3, 29], residues := [(2, 4698), (3, 7139), (29, 8974)] },
    { n := 9403, F := 9402, R := 1, a := 3, factors := [2, 3, 1567], residues := [(2, 4701), (3, 1997), (1567, 7091)] },
    { n := 9413, F := 9412, R := 1, a := 3, factors := [2, 2, 13, 181], residues := [(2, 4706), (13, 6022), (181, 8893)] },
    { n := 9419, F := 9418, R := 1, a := 2, factors := [2, 17, 277], residues := [(2, 4709), (17, 7868), (277, 2495)] },
    { n := 9421, F := 9420, R := 1, a := 2, factors := [2, 2, 3, 5, 157], residues := [(2, 4710), (3, 5487), (5, 1422), (157, 5882)] },
    { n := 9431, F := 9430, R := 1, a := 7, factors := [2, 5, 23, 41], residues := [(2, 4715), (5, 4550), (23, 7666), (41, 7711)] },
    { n := 9433, F := 9432, R := 1, a := 5, factors := [2, 2, 2, 3, 3, 131], residues := [(2, 4716), (3, 2835), (131, 6104)] },
    { n := 9437, F := 9436, R := 1, a := 2, factors := [2, 2, 7, 337], residues := [(2, 4718), (7, 5833), (337, 2831)] },
    { n := 9439, F := 9438, R := 1, a := 22, factors := [2, 3, 11, 11, 13], residues := [(2, 4719), (3, 9194), (11, 4151), (13, 1818)] },
    { n := 9461, F := 9460, R := 1, a := 3, factors := [2, 2, 5, 11, 43], residues := [(2, 4730), (5, 6536), (11, 9317), (43, 2783)] },
    { n := 9463, F := 9462, R := 1, a := 3, factors := [2, 3, 19, 83], residues := [(2, 4731), (3, 9260), (19, 6531), (83, 6606)] },
    { n := 9467, F := 9466, R := 1, a := 2, factors := [2, 4733], residues := [(2, 4733), (4733, 3156)] },
    { n := 9473, F := 9472, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 2, 37], residues := [(2, 4736), (37, 5958)] },
    { n := 9479, F := 9478, R := 1, a := 7, factors := [2, 7, 677], residues := [(2, 4739), (7, 1225), (677, 305)] },
    { n := 9491, F := 9490, R := 1, a := 2, factors := [2, 5, 13, 73], residues := [(2, 4745), (5, 9089), (13, 1309), (73, 632)] },
    { n := 9497, F := 9496, R := 1, a := 3, factors := [2, 2, 2, 1187], residues := [(2, 4748), (1187, 4527)] },
    { n := 9511, F := 9510, R := 1, a := 3, factors := [2, 3, 5, 317], residues := [(2, 4755), (3, 1163), (5, 786), (317, 6752)] },
    { n := 9521, F := 9520, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 7, 17], residues := [(2, 4760), (5, 9387), (7, 8547), (17, 8395)] },
    { n := 9533, F := 9532, R := 1, a := 2, factors := [2, 2, 2383], residues := [(2, 4766), (2383, 8262)] },
    { n := 9539, F := 9538, R := 1, a := 2, factors := [2, 19, 251], residues := [(2, 4769), (19, 4413), (251, 4660)] },
    { n := 9547, F := 9546, R := 1, a := 2, factors := [2, 3, 37, 43], residues := [(2, 4773), (3, 8457), (37, 1990), (43, 7471)] },
    { n := 9551, F := 9550, R := 1, a := 11, factors := [2, 5, 5, 191], residues := [(2, 4775), (5, 1234), (191, 6753)] },
    { n := 9587, F := 9586, R := 1, a := 2, factors := [2, 4793], residues := [(2, 4793), (4793, 3196)] },
    { n := 9601, F := 9600, R := 1, a := 13, factors := [2, 2, 2, 2, 2, 2, 2, 3, 5, 5], residues := [(2, 4800), (3, 4602), (5, 6151)] },
    { n := 9613, F := 9612, R := 1, a := 2, factors := [2, 2, 3, 3, 3, 89], residues := [(2, 4806), (3, 2175), (89, 7292)] },
    { n := 9619, F := 9618, R := 1, a := 2, factors := [2, 3, 7, 229], residues := [(2, 4809), (3, 1475), (7, 83), (229, 6054)] },
    { n := 9623, F := 9622, R := 1, a := 5, factors := [2, 17, 283], residues := [(2, 4811), (17, 3337), (283, 1)] },
    { n := 9629, F := 9628, R := 1, a := 2, factors := [2, 2, 29, 83], residues := [(2, 4814), (29, 3835), (83, 5865)] },
    { n := 9631, F := 9630, R := 1, a := 3, factors := [2, 3, 3, 5, 107], residues := [(2, 4815), (3, 540), (5, 7676), (107, 4692)] },
    { n := 9643, F := 9642, R := 1, a := 2, factors := [2, 3, 1607], residues := [(2, 4821), (3, 4896), (1607, 7194)] },
    { n := 9649, F := 9648, R := 1, a := 7, factors := [2, 2, 2, 2, 3, 3, 67], residues := [(2, 4824), (3, 1138), (67, 5118)] },
    { n := 9661, F := 9660, R := 1, a := 2, factors := [2, 2, 3, 5, 7, 23], residues := [(2, 4830), (3, 5889), (5, 8128), (7, 2986), (23, 1303)] },
    { n := 9677, F := 9676, R := 1, a := 2, factors := [2, 2, 41, 59], residues := [(2, 4838), (41, 1571), (59, 9626)] },
    { n := 9679, F := 9678, R := 1, a := 3, factors := [2, 3, 1613], residues := [(2, 4839), (3, 5481), (1613, 2566)] },
    { n := 9689, F := 9688, R := 1, a := 3, factors := [2, 2, 2, 7, 173], residues := [(2, 4844), (7, 4638), (173, 5970)] },
    { n := 9697, F := 9696, R := 1, a := 10, factors := [2, 2, 2, 2, 2, 3, 101], residues := [(2, 4848), (3, 7128), (101, 1400)] },
    { n := 9719, F := 9718, R := 1, a := 17, factors := [2, 43, 113], residues := [(2, 4859), (43, 3035), (113, 4374)] },
    { n := 9721, F := 9720, R := 1, a := 7, factors := [2, 2, 2, 3, 3, 3, 3, 3, 5], residues := [(2, 4860), (3, 641), (5, 4287)] },
    { n := 9733, F := 9732, R := 1, a := 2, factors := [2, 2, 3, 811], residues := [(2, 4866), (3, 7005), (811, 3299)] },
    { n := 9739, F := 9738, R := 1, a := 3, factors := [2, 3, 3, 541], residues := [(2, 4869), (3, 7415), (541, 2949)] },
    { n := 9743, F := 9742, R := 1, a := 5, factors := [2, 4871], residues := [(2, 4871), (4871, 406)] },
    { n := 9749, F := 9748, R := 1, a := 2, factors := [2, 2, 2437], residues := [(2, 4874), (2437, 650)] },
    { n := 9767, F := 9766, R := 1, a := 5, factors := [2, 19, 257], residues := [(2, 4883), (19, 9426), (257, 7210)] },
    { n := 9769, F := 9768, R := 1, a := 13, factors := [2, 2, 2, 3, 11, 37], residues := [(2, 4884), (3, 3343), (11, 740), (37, 7213)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData08_valid : PocklingtonRow.Valid lowPocklingtonData08 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPocklingtonPrime08 (i : Fin lowPocklingtonData08.length) :
    Nat.Prime (lowPocklingtonData08.get i).n := by
  exact PocklingtonRow.prime_of_mem lowPocklingtonData08_valid (List.get_mem _ _)
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 8963) (q := 8969) (by
      have hp := lowPocklingtonPrime08 ⟨0, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8969) (q := 8971) (by
      have hp := lowPocklingtonPrime08 ⟨1, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8971) (q := 8999) (by
      have hp := lowPocklingtonPrime08 ⟨2, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8999) (q := 9001) (by
      have hp := lowPocklingtonPrime08 ⟨3, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9001) (q := 9007) (by
      have hp := lowPocklingtonPrime08 ⟨4, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9007) (q := 9011) (by
      have hp := lowPocklingtonPrime08 ⟨5, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9011) (q := 9013) (by
      have hp := lowPocklingtonPrime08 ⟨6, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9013) (q := 9029) (by
      have hp := lowPocklingtonPrime08 ⟨7, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part01_chain :
    DusartPrimeRowsChain 8963 9028 dusartPrimeRows_8963_9418_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9414, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9029) (q := 9041) (by
      have hp := lowPocklingtonPrime08 ⟨8, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9041) (q := 9043) (by
      have hp := lowPocklingtonPrime08 ⟨9, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9043) (q := 9049) (by
      have hp := lowPocklingtonPrime08 ⟨10, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9049) (q := 9059) (by
      have hp := lowPocklingtonPrime08 ⟨11, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9059) (q := 9067) (by
      have hp := lowPocklingtonPrime08 ⟨12, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9067) (q := 9091) (by
      have hp := lowPocklingtonPrime08 ⟨13, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9091) (q := 9103) (by
      have hp := lowPocklingtonPrime08 ⟨14, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9103) (q := 9109) (by
      have hp := lowPocklingtonPrime08 ⟨15, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part02_chain :
    DusartPrimeRowsChain 9029 9108 dusartPrimeRows_8963_9418_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9414, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9109) (q := 9127) (by
      have hp := lowPocklingtonPrime08 ⟨16, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9127) (q := 9133) (by
      have hp := lowPocklingtonPrime08 ⟨17, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9133) (q := 9137) (by
      have hp := lowPocklingtonPrime08 ⟨18, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9137) (q := 9151) (by
      have hp := lowPocklingtonPrime08 ⟨19, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9151) (q := 9157) (by
      have hp := lowPocklingtonPrime08 ⟨20, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9157) (q := 9161) (by
      have hp := lowPocklingtonPrime08 ⟨21, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9161) (q := 9173) (by
      have hp := lowPocklingtonPrime08 ⟨22, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9173) (q := 9181) (by
      have hp := lowPocklingtonPrime08 ⟨23, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part03_chain :
    DusartPrimeRowsChain 9109 9180 dusartPrimeRows_8963_9418_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9414, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9181) (q := 9187) (by
      have hp := lowPocklingtonPrime08 ⟨24, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9187) (q := 9199) (by
      have hp := lowPocklingtonPrime08 ⟨25, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9199) (q := 9203) (by
      have hp := lowPocklingtonPrime08 ⟨26, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9203) (q := 9209) (by
      have hp := lowPocklingtonPrime08 ⟨27, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9209) (q := 9221) (by
      have hp := lowPocklingtonPrime08 ⟨28, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9221) (q := 9227) (by
      have hp := lowPocklingtonPrime08 ⟨29, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9227) (q := 9239) (by
      have hp := lowPocklingtonPrime08 ⟨30, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9239) (q := 9241) (by
      have hp := lowPocklingtonPrime08 ⟨31, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part04_chain :
    DusartPrimeRowsChain 9181 9240 dusartPrimeRows_8963_9418_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9414, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9241) (q := 9257) (by
      have hp := lowPocklingtonPrime08 ⟨32, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9257) (q := 9277) (by
      have hp := lowPocklingtonPrime08 ⟨33, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9277) (q := 9281) (by
      have hp := lowPocklingtonPrime08 ⟨34, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9281) (q := 9283) (by
      have hp := lowPocklingtonPrime08 ⟨35, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9283) (q := 9293) (by
      have hp := lowPocklingtonPrime08 ⟨36, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9293) (q := 9311) (by
      have hp := lowPocklingtonPrime08 ⟨37, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9311) (q := 9319) (by
      have hp := lowPocklingtonPrime08 ⟨38, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9319) (q := 9323) (by
      have hp := lowPocklingtonPrime08 ⟨39, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part05_chain :
    DusartPrimeRowsChain 9241 9322 dusartPrimeRows_8963_9418_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9414, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9323) (q := 9337) (by
      have hp := lowPocklingtonPrime08 ⟨40, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9337) (q := 9341) (by
      have hp := lowPocklingtonPrime08 ⟨41, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9341) (q := 9343) (by
      have hp := lowPocklingtonPrime08 ⟨42, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9343) (q := 9349) (by
      have hp := lowPocklingtonPrime08 ⟨43, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9349) (q := 9371) (by
      have hp := lowPocklingtonPrime08 ⟨44, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9371) (q := 9377) (by
      have hp := lowPocklingtonPrime08 ⟨45, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9377) (q := 9391) (by
      have hp := lowPocklingtonPrime08 ⟨46, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9391) (q := 9397) (by
      have hp := lowPocklingtonPrime08 ⟨47, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part06_chain :
    DusartPrimeRowsChain 9323 9396 dusartPrimeRows_8963_9418_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9414, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9397) (q := 9403) (by
      have hp := lowPocklingtonPrime08 ⟨48, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9403) (q := 9413) (by
      have hp := lowPocklingtonPrime08 ⟨49, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9413) (q := 9419) (by
      have hp := lowPocklingtonPrime08 ⟨50, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part07_chain :
    DusartPrimeRowsChain 9397 9418 dusartPrimeRows_8963_9418_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.empty
        norm_num [dusartPrimeRow_of_explicit_9414, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9419) (q := 9421) (by
      have hp := lowPocklingtonPrime08 ⟨51, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9421) (q := 9431) (by
      have hp := lowPocklingtonPrime08 ⟨52, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9431) (q := 9433) (by
      have hp := lowPocklingtonPrime08 ⟨53, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9433) (q := 9437) (by
      have hp := lowPocklingtonPrime08 ⟨54, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9437) (q := 9439) (by
      have hp := lowPocklingtonPrime08 ⟨55, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9439) (q := 9461) (by
      have hp := lowPocklingtonPrime08 ⟨56, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9461) (q := 9463) (by
      have hp := lowPocklingtonPrime08 ⟨57, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9463) (q := 9467) (by
      have hp := lowPocklingtonPrime08 ⟨58, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part01_chain :
    DusartPrimeRowsChain 9419 9466 dusartPrimeRows_9419_9900_part01 := by
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
def dusartPrimeRows_9419_9900_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9467) (q := 9473) (by
      have hp := lowPocklingtonPrime08 ⟨59, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9473) (q := 9479) (by
      have hp := lowPocklingtonPrime08 ⟨60, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9479) (q := 9491) (by
      have hp := lowPocklingtonPrime08 ⟨61, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9491) (q := 9497) (by
      have hp := lowPocklingtonPrime08 ⟨62, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9497) (q := 9511) (by
      have hp := lowPocklingtonPrime08 ⟨63, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9511) (q := 9521) (by
      have hp := lowPocklingtonPrime08 ⟨64, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9521) (q := 9533) (by
      have hp := lowPocklingtonPrime08 ⟨65, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9533) (q := 9539) (by
      have hp := lowPocklingtonPrime08 ⟨66, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part02_chain :
    DusartPrimeRowsChain 9467 9538 dusartPrimeRows_9419_9900_part02 := by
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
def dusartPrimeRows_9419_9900_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9539) (q := 9547) (by
      have hp := lowPocklingtonPrime08 ⟨67, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9547) (q := 9551) (by
      have hp := lowPocklingtonPrime08 ⟨68, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9551) (q := 9587) (by
      have hp := lowPocklingtonPrime08 ⟨69, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9587) (q := 9601) (by
      have hp := lowPocklingtonPrime08 ⟨70, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9601) (q := 9613) (by
      have hp := lowPocklingtonPrime08 ⟨71, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9613) (q := 9619) (by
      have hp := lowPocklingtonPrime08 ⟨72, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9619) (q := 9623) (by
      have hp := lowPocklingtonPrime08 ⟨73, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9623) (q := 9629) (by
      have hp := lowPocklingtonPrime08 ⟨74, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part03_chain :
    DusartPrimeRowsChain 9539 9628 dusartPrimeRows_9419_9900_part03 := by
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
def dusartPrimeRows_9419_9900_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9629) (q := 9631) (by
      have hp := lowPocklingtonPrime08 ⟨75, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9631) (q := 9643) (by
      have hp := lowPocklingtonPrime08 ⟨76, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9643) (q := 9649) (by
      have hp := lowPocklingtonPrime08 ⟨77, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9649) (q := 9661) (by
      have hp := lowPocklingtonPrime08 ⟨78, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9661) (q := 9677) (by
      have hp := lowPocklingtonPrime08 ⟨79, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9677) (q := 9679) (by
      have hp := lowPocklingtonPrime08 ⟨80, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9679) (q := 9689) (by
      have hp := lowPocklingtonPrime08 ⟨81, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9689) (q := 9697) (by
      have hp := lowPocklingtonPrime08 ⟨82, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part04_chain :
    DusartPrimeRowsChain 9629 9696 dusartPrimeRows_9419_9900_part04 := by
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
def dusartPrimeRows_9419_9900_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9697) (q := 9719) (by
      have hp := lowPocklingtonPrime08 ⟨83, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9719) (q := 9721) (by
      have hp := lowPocklingtonPrime08 ⟨84, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9721) (q := 9733) (by
      have hp := lowPocklingtonPrime08 ⟨85, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9733) (q := 9739) (by
      have hp := lowPocklingtonPrime08 ⟨86, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9739) (q := 9743) (by
      have hp := lowPocklingtonPrime08 ⟨87, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9743) (q := 9749) (by
      have hp := lowPocklingtonPrime08 ⟨88, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9749) (q := 9767) (by
      have hp := lowPocklingtonPrime08 ⟨89, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9767) (q := 9769) (by
      have hp := lowPocklingtonPrime08 ⟨90, by simp [lowPocklingtonData08]⟩
      simpa [lowPocklingtonData08] using hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part05_chain :
    DusartPrimeRowsChain 9697 9768 dusartPrimeRows_9419_9900_part05 := by
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
