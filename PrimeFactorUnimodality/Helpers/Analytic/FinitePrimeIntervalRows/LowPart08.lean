import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

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

theorem lowPrime_8969 : Nat.Prime 8969 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_8971 : Nat.Prime 8971 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_8999 : Nat.Prime 8999 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9001 : Nat.Prime 9001 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9007 : Nat.Prime 9007 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9011 : Nat.Prime 9011 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9013 : Nat.Prime 9013 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9029 : Nat.Prime 9029 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9041 : Nat.Prime 9041 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9043 : Nat.Prime 9043 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9049 : Nat.Prime 9049 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9059 : Nat.Prime 9059 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9067 : Nat.Prime 9067 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9091 : Nat.Prime 9091 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9103 : Nat.Prime 9103 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9109 : Nat.Prime 9109 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9127 : Nat.Prime 9127 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9133 : Nat.Prime 9133 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9137 : Nat.Prime 9137 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9151 : Nat.Prime 9151 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9157 : Nat.Prime 9157 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9161 : Nat.Prime 9161 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9173 : Nat.Prime 9173 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9181 : Nat.Prime 9181 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9187 : Nat.Prime 9187 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9199 : Nat.Prime 9199 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9203 : Nat.Prime 9203 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9209 : Nat.Prime 9209 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9221 : Nat.Prime 9221 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9227 : Nat.Prime 9227 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9239 : Nat.Prime 9239 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9241 : Nat.Prime 9241 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9257 : Nat.Prime 9257 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9277 : Nat.Prime 9277 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9281 : Nat.Prime 9281 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9283 : Nat.Prime 9283 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9293 : Nat.Prime 9293 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9311 : Nat.Prime 9311 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9319 : Nat.Prime 9319 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9323 : Nat.Prime 9323 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9337 : Nat.Prime 9337 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9341 : Nat.Prime 9341 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9343 : Nat.Prime 9343 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9349 : Nat.Prime 9349 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9371 : Nat.Prime 9371 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9377 : Nat.Prime 9377 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9391 : Nat.Prime 9391 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9397 : Nat.Prime 9397 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9403 : Nat.Prime 9403 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9413 : Nat.Prime 9413 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9419 : Nat.Prime 9419 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9421 : Nat.Prime 9421 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9431 : Nat.Prime 9431 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9433 : Nat.Prime 9433 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9437 : Nat.Prime 9437 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9439 : Nat.Prime 9439 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9461 : Nat.Prime 9461 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9463 : Nat.Prime 9463 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9467 : Nat.Prime 9467 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9473 : Nat.Prime 9473 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9479 : Nat.Prime 9479 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9491 : Nat.Prime 9491 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9497 : Nat.Prime 9497 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9511 : Nat.Prime 9511 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9521 : Nat.Prime 9521 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9533 : Nat.Prime 9533 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9539 : Nat.Prime 9539 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9547 : Nat.Prime 9547 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9551 : Nat.Prime 9551 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9587 : Nat.Prime 9587 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9601 : Nat.Prime 9601 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9613 : Nat.Prime 9613 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9619 : Nat.Prime 9619 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9623 : Nat.Prime 9623 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9629 : Nat.Prime 9629 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9631 : Nat.Prime 9631 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9643 : Nat.Prime 9643 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9649 : Nat.Prime 9649 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9661 : Nat.Prime 9661 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9677 : Nat.Prime 9677 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9679 : Nat.Prime 9679 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9689 : Nat.Prime 9689 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9697 : Nat.Prime 9697 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9719 : Nat.Prime 9719 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9721 : Nat.Prime 9721 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9733 : Nat.Prime 9733 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9739 : Nat.Prime 9739 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9743 : Nat.Prime 9743 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9749 : Nat.Prime 9749 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9767 : Nat.Prime 9767 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]

theorem lowPrime_9769 : Nat.Prime 9769 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData08_valid
  simp [lowPocklingtonData08]
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 8963) (q := 8969) (by exact lowPrime_8969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8969) (q := 8971) (by exact lowPrime_8971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8971) (q := 8999) (by exact lowPrime_8999) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 8999) (q := 9001) (by exact lowPrime_9001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9001) (q := 9007) (by exact lowPrime_9007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9007) (q := 9011) (by exact lowPrime_9011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9011) (q := 9013) (by exact lowPrime_9013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9013) (q := 9029) (by exact lowPrime_9029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_9414 (p := 9029) (q := 9041) (by exact lowPrime_9041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9041) (q := 9043) (by exact lowPrime_9043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9043) (q := 9049) (by exact lowPrime_9049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9049) (q := 9059) (by exact lowPrime_9059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9059) (q := 9067) (by exact lowPrime_9067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9067) (q := 9091) (by exact lowPrime_9091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9091) (q := 9103) (by exact lowPrime_9103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9103) (q := 9109) (by exact lowPrime_9109) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_9414 (p := 9109) (q := 9127) (by exact lowPrime_9127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9127) (q := 9133) (by exact lowPrime_9133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9133) (q := 9137) (by exact lowPrime_9137) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9137) (q := 9151) (by exact lowPrime_9151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9151) (q := 9157) (by exact lowPrime_9157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9157) (q := 9161) (by exact lowPrime_9161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9161) (q := 9173) (by exact lowPrime_9173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9173) (q := 9181) (by exact lowPrime_9181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_9414 (p := 9181) (q := 9187) (by exact lowPrime_9187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9187) (q := 9199) (by exact lowPrime_9199) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9199) (q := 9203) (by exact lowPrime_9203) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9203) (q := 9209) (by exact lowPrime_9209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9209) (q := 9221) (by exact lowPrime_9221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9221) (q := 9227) (by exact lowPrime_9227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9227) (q := 9239) (by exact lowPrime_9239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9239) (q := 9241) (by exact lowPrime_9241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_9414 (p := 9241) (q := 9257) (by exact lowPrime_9257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9257) (q := 9277) (by exact lowPrime_9277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9277) (q := 9281) (by exact lowPrime_9281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9281) (q := 9283) (by exact lowPrime_9283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9283) (q := 9293) (by exact lowPrime_9293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9293) (q := 9311) (by exact lowPrime_9311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9311) (q := 9319) (by exact lowPrime_9319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9319) (q := 9323) (by exact lowPrime_9323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_9414 (p := 9323) (q := 9337) (by exact lowPrime_9337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9337) (q := 9341) (by exact lowPrime_9341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9341) (q := 9343) (by exact lowPrime_9343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9343) (q := 9349) (by exact lowPrime_9349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9349) (q := 9371) (by exact lowPrime_9371) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9371) (q := 9377) (by exact lowPrime_9377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9377) (q := 9391) (by exact lowPrime_9391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9391) (q := 9397) (by exact lowPrime_9397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_9414 (p := 9397) (q := 9403) (by exact lowPrime_9403) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9403) (q := 9413) (by exact lowPrime_9413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9413) (q := 9419) (by exact lowPrime_9419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_9897 (p := 9419) (q := 9421) (by exact lowPrime_9421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9421) (q := 9431) (by exact lowPrime_9431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9431) (q := 9433) (by exact lowPrime_9433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9433) (q := 9437) (by exact lowPrime_9437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9437) (q := 9439) (by exact lowPrime_9439) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9439) (q := 9461) (by exact lowPrime_9461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9461) (q := 9463) (by exact lowPrime_9463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9463) (q := 9467) (by exact lowPrime_9467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_9897 (p := 9467) (q := 9473) (by exact lowPrime_9473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9473) (q := 9479) (by exact lowPrime_9479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9479) (q := 9491) (by exact lowPrime_9491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9491) (q := 9497) (by exact lowPrime_9497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9497) (q := 9511) (by exact lowPrime_9511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9511) (q := 9521) (by exact lowPrime_9521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9521) (q := 9533) (by exact lowPrime_9533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9533) (q := 9539) (by exact lowPrime_9539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_9897 (p := 9539) (q := 9547) (by exact lowPrime_9547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9547) (q := 9551) (by exact lowPrime_9551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9551) (q := 9587) (by exact lowPrime_9587) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9587) (q := 9601) (by exact lowPrime_9601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9601) (q := 9613) (by exact lowPrime_9613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9613) (q := 9619) (by exact lowPrime_9619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9619) (q := 9623) (by exact lowPrime_9623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9623) (q := 9629) (by exact lowPrime_9629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_9897 (p := 9629) (q := 9631) (by exact lowPrime_9631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9631) (q := 9643) (by exact lowPrime_9643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9643) (q := 9649) (by exact lowPrime_9649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9649) (q := 9661) (by exact lowPrime_9661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9661) (q := 9677) (by exact lowPrime_9677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9677) (q := 9679) (by exact lowPrime_9679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9679) (q := 9689) (by exact lowPrime_9689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9689) (q := 9697) (by exact lowPrime_9697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
    dusartPrimeRow_of_explicit_9897 (p := 9697) (q := 9719) (by exact lowPrime_9719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9719) (q := 9721) (by exact lowPrime_9721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9721) (q := 9733) (by exact lowPrime_9733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9733) (q := 9739) (by exact lowPrime_9739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9739) (q := 9743) (by exact lowPrime_9743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9743) (q := 9749) (by exact lowPrime_9749) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9749) (q := 9767) (by exact lowPrime_9767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9767) (q := 9769) (by exact lowPrime_9769) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
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
