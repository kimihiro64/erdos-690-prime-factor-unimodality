import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 02 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
def lowPocklingtonData02 : List PocklingtonData := [
    { n := 4013, F := 4012, R := 1, a := 2, factors := [2, 2, 17, 59], residues := [(2, 2006), (17, 1824), (59, 1179)] },
    { n := 4019, F := 4018, R := 1, a := 2, factors := [2, 7, 7, 41], residues := [(2, 2009), (7, 2438), (41, 3026)] },
    { n := 4021, F := 4020, R := 1, a := 2, factors := [2, 2, 3, 5, 67], residues := [(2, 2010), (3, 1944), (5, 1527), (67, 3694)] },
    { n := 4027, F := 4026, R := 1, a := 3, factors := [2, 3, 11, 61], residues := [(2, 2013), (3, 3291), (11, 3139), (61, 1678)] },
    { n := 4049, F := 4048, R := 1, a := 3, factors := [2, 2, 2, 2, 11, 23], residues := [(2, 2024), (11, 749), (23, 3208)] },
    { n := 4051, F := 4050, R := 1, a := 10, factors := [2, 3, 3, 3, 3, 5, 5], residues := [(2, 2025), (3, 1084), (5, 491)] },
    { n := 4057, F := 4056, R := 1, a := 5, factors := [2, 2, 2, 3, 13, 13], residues := [(2, 2028), (3, 469), (13, 1621)] },
    { n := 4073, F := 4072, R := 1, a := 3, factors := [2, 2, 2, 509], residues := [(2, 2036), (509, 660)] },
    { n := 4079, F := 4078, R := 1, a := 11, factors := [2, 2039], residues := [(2, 2039), (2039, 34)] },
    { n := 4091, F := 4090, R := 1, a := 2, factors := [2, 5, 409], residues := [(2, 2045), (5, 2319), (409, 4)] },
    { n := 4093, F := 4092, R := 1, a := 2, factors := [2, 2, 3, 11, 31], residues := [(2, 2046), (3, 1063), (11, 1323), (31, 1877)] },
    { n := 4099, F := 4098, R := 1, a := 2, factors := [2, 3, 683], residues := [(2, 2049), (3, 3426), (683, 3058)] },
    { n := 4111, F := 4110, R := 1, a := 12, factors := [2, 3, 5, 137], residues := [(2, 2055), (3, 3092), (5, 2447), (137, 1627)] },
    { n := 4127, F := 4126, R := 1, a := 5, factors := [2, 2063], residues := [(2, 2063), (2063, 172)] },
    { n := 4129, F := 4128, R := 1, a := 13, factors := [2, 2, 2, 2, 2, 3, 43], residues := [(2, 2064), (3, 3412), (43, 1473)] },
    { n := 4133, F := 4132, R := 1, a := 2, factors := [2, 2, 1033], residues := [(2, 2066), (1033, 3582)] },
    { n := 4139, F := 4138, R := 1, a := 2, factors := [2, 2069], residues := [(2, 2069), (2069, 1380)] },
    { n := 4153, F := 4152, R := 1, a := 5, factors := [2, 2, 2, 3, 173], residues := [(2, 2076), (3, 2825), (173, 3154)] },
    { n := 4157, F := 4156, R := 1, a := 2, factors := [2, 2, 1039], residues := [(2, 2078), (1039, 1940)] },
    { n := 4159, F := 4158, R := 1, a := 3, factors := [2, 3, 3, 3, 7, 11], residues := [(2, 2079), (3, 851), (7, 1837), (11, 3046)] },
    { n := 4177, F := 4176, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 3, 29], residues := [(2, 2088), (3, 367), (29, 1785)] },
    { n := 4201, F := 4200, R := 1, a := 11, factors := [2, 2, 2, 3, 5, 5, 7], residues := [(2, 2100), (3, 3175), (5, 2375), (7, 1806)] },
    { n := 4211, F := 4210, R := 1, a := 6, factors := [2, 5, 421], residues := [(2, 2105), (5, 2746), (421, 3094)] },
    { n := 4217, F := 4216, R := 1, a := 3, factors := [2, 2, 2, 17, 31], residues := [(2, 2108), (17, 3291), (31, 3244)] },
    { n := 4219, F := 4218, R := 1, a := 2, factors := [2, 3, 19, 37], residues := [(2, 2109), (3, 4181), (19, 1998), (37, 673)] },
    { n := 4229, F := 4228, R := 1, a := 2, factors := [2, 2, 7, 151], residues := [(2, 2114), (7, 129), (151, 3555)] },
    { n := 4231, F := 4230, R := 1, a := 3, factors := [2, 3, 3, 5, 47], residues := [(2, 2115), (3, 3027), (5, 236), (47, 1140)] },
    { n := 4241, F := 4240, R := 1, a := 3, factors := [2, 2, 2, 2, 5, 53], residues := [(2, 2120), (5, 575), (53, 2244)] },
    { n := 4243, F := 4242, R := 1, a := 2, factors := [2, 3, 7, 101], residues := [(2, 2121), (3, 4143), (7, 3750), (101, 4131)] },
    { n := 4253, F := 4252, R := 1, a := 2, factors := [2, 2, 1063], residues := [(2, 2126), (1063, 3686)] },
    { n := 4259, F := 4258, R := 1, a := 2, factors := [2, 2129], residues := [(2, 2129), (2129, 1420)] },
    { n := 4261, F := 4260, R := 1, a := 2, factors := [2, 2, 3, 5, 71], residues := [(2, 2130), (3, 2291), (5, 2211), (71, 2269)] },
    { n := 4271, F := 4270, R := 1, a := 7, factors := [2, 5, 7, 61], residues := [(2, 2135), (5, 1304), (7, 1834), (61, 646)] },
    { n := 4273, F := 4272, R := 1, a := 5, factors := [2, 2, 2, 2, 3, 89], residues := [(2, 2136), (3, 3385), (89, 184)] },
    { n := 4283, F := 4282, R := 1, a := 2, factors := [2, 2141], residues := [(2, 2141), (2141, 1428)] },
    { n := 4289, F := 4288, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 67], residues := [(2, 2144), (67, 836)] },
    { n := 4297, F := 4296, R := 1, a := 5, factors := [2, 2, 2, 3, 179], residues := [(2, 2148), (3, 2394), (179, 3818)] },
    { n := 4327, F := 4326, R := 1, a := 3, factors := [2, 3, 7, 103], residues := [(2, 2163), (3, 1651), (7, 2791), (103, 2422)] },
    { n := 4337, F := 4336, R := 1, a := 3, factors := [2, 2, 2, 2, 271], residues := [(2, 2168), (271, 4287)] },
    { n := 4339, F := 4338, R := 1, a := 10, factors := [2, 3, 3, 241], residues := [(2, 2169), (3, 2813), (241, 474)] },
    { n := 4349, F := 4348, R := 1, a := 2, factors := [2, 2, 1087], residues := [(2, 2174), (1087, 290)] },
    { n := 4357, F := 4356, R := 1, a := 2, factors := [2, 2, 3, 3, 11, 11], residues := [(2, 2178), (3, 3917), (11, 3605)] },
    { n := 4363, F := 4362, R := 1, a := 2, factors := [2, 3, 727], residues := [(2, 2181), (3, 4225), (727, 4086)] },
    { n := 4373, F := 4372, R := 1, a := 2, factors := [2, 2, 1093], residues := [(2, 2186), (1093, 3790)] },
    { n := 4391, F := 4390, R := 1, a := 14, factors := [2, 5, 439], residues := [(2, 2195), (5, 4358), (439, 552)] },
    { n := 4397, F := 4396, R := 1, a := 2, factors := [2, 2, 7, 157], residues := [(2, 2198), (7, 1321), (157, 1680)] },
    { n := 4409, F := 4408, R := 1, a := 3, factors := [2, 2, 2, 19, 29], residues := [(2, 2204), (19, 1505), (29, 3656)] },
    { n := 4421, F := 4420, R := 1, a := 3, factors := [2, 2, 5, 13, 17], residues := [(2, 2210), (5, 280), (13, 1950), (17, 3615)] },
    { n := 4423, F := 4422, R := 1, a := 3, factors := [2, 3, 11, 67], residues := [(2, 2211), (3, 2926), (11, 2632), (67, 2174)] },
    { n := 4441, F := 4440, R := 1, a := 21, factors := [2, 2, 2, 3, 5, 37], residues := [(2, 2220), (3, 300), (5, 3489), (37, 289)] },
    { n := 4447, F := 4446, R := 1, a := 3, factors := [2, 3, 3, 13, 19], residues := [(2, 2223), (3, 4408), (13, 827), (19, 3754)] },
    { n := 4451, F := 4450, R := 1, a := 2, factors := [2, 5, 5, 89], residues := [(2, 2225), (5, 3476), (89, 2301)] },
    { n := 4457, F := 4456, R := 1, a := 3, factors := [2, 2, 2, 557], residues := [(2, 2228), (557, 657)] },
    { n := 4463, F := 4462, R := 1, a := 5, factors := [2, 23, 97], residues := [(2, 2231), (23, 3102), (97, 2557)] },
    { n := 4481, F := 4480, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 2, 5, 7], residues := [(2, 2240), (5, 917), (7, 4450)] },
    { n := 4483, F := 4482, R := 1, a := 2, factors := [2, 3, 3, 3, 83], residues := [(2, 2241), (3, 4314), (83, 2394)] },
    { n := 4493, F := 4492, R := 1, a := 2, factors := [2, 2, 1123], residues := [(2, 2246), (1123, 3894)] },
    { n := 4507, F := 4506, R := 1, a := 2, factors := [2, 3, 751], residues := [(2, 2253), (3, 3268), (751, 3577)] },
    { n := 4513, F := 4512, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 3, 47], residues := [(2, 2256), (3, 271), (47, 2895)] },
    { n := 4517, F := 4516, R := 1, a := 2, factors := [2, 2, 1129], residues := [(2, 2258), (1129, 2108)] },
    { n := 4519, F := 4518, R := 1, a := 3, factors := [2, 3, 3, 251], residues := [(2, 2259), (3, 2660), (251, 2351)] },
    { n := 4523, F := 4522, R := 1, a := 5, factors := [2, 7, 17, 19], residues := [(2, 2261), (7, 1181), (17, 466), (19, 4380)] },
    { n := 4547, F := 4546, R := 1, a := 2, factors := [2, 2273], residues := [(2, 2273), (2273, 1516)] },
    { n := 4549, F := 4548, R := 1, a := 6, factors := [2, 2, 3, 379], residues := [(2, 2274), (3, 3967), (379, 2908)] },
    { n := 4561, F := 4560, R := 1, a := 11, factors := [2, 2, 2, 2, 3, 5, 19], residues := [(2, 2280), (3, 1601), (5, 3213), (19, 1941)] },
    { n := 4567, F := 4566, R := 1, a := 3, factors := [2, 3, 761], residues := [(2, 2283), (3, 3415), (761, 1813)] },
    { n := 4583, F := 4582, R := 1, a := 5, factors := [2, 29, 79], residues := [(2, 2291), (29, 3773), (79, 3741)] },
    { n := 4591, F := 4590, R := 1, a := 11, factors := [2, 3, 3, 3, 5, 17], residues := [(2, 2295), (3, 103), (5, 4366), (17, 3885)] },
    { n := 4597, F := 4596, R := 1, a := 5, factors := [2, 2, 3, 383], residues := [(2, 2298), (3, 1406), (383, 3696)] },
    { n := 4603, F := 4602, R := 1, a := 2, factors := [2, 3, 13, 59], residues := [(2, 2301), (3, 3128), (13, 4174), (59, 4028)] },
    { n := 4621, F := 4620, R := 1, a := 2, factors := [2, 2, 3, 5, 7, 11], residues := [(2, 2310), (3, 3668), (5, 1777), (7, 2941), (11, 1004)] },
    { n := 4637, F := 4636, R := 1, a := 2, factors := [2, 2, 19, 61], residues := [(2, 2318), (19, 2684), (61, 400)] },
    { n := 4639, F := 4638, R := 1, a := 3, factors := [2, 3, 773], residues := [(2, 2319), (3, 4185), (773, 873)] },
    { n := 4643, F := 4642, R := 1, a := 5, factors := [2, 11, 211], residues := [(2, 2321), (11, 3833), (211, 1635)] },
    { n := 4649, F := 4648, R := 1, a := 3, factors := [2, 2, 2, 7, 83], residues := [(2, 2324), (7, 954), (83, 3704)] },
    { n := 4651, F := 4650, R := 1, a := 3, factors := [2, 3, 5, 5, 31], residues := [(2, 2325), (3, 1812), (5, 5), (31, 995)] },
    { n := 4657, F := 4656, R := 1, a := 15, factors := [2, 2, 2, 2, 3, 97], residues := [(2, 2328), (3, 4334), (97, 863)] },
    { n := 4663, F := 4662, R := 1, a := 3, factors := [2, 3, 3, 7, 37], residues := [(2, 2331), (3, 3965), (7, 4088), (37, 1671)] },
    { n := 4673, F := 4672, R := 1, a := 3, factors := [2, 2, 2, 2, 2, 2, 73], residues := [(2, 2336), (73, 1954)] },
    { n := 4679, F := 4678, R := 1, a := 11, factors := [2, 2339], residues := [(2, 2339), (2339, 39)] },
    { n := 4691, F := 4690, R := 1, a := 2, factors := [2, 5, 7, 67], residues := [(2, 2345), (5, 4520), (7, 3249), (67, 2617)] },
    { n := 4703, F := 4702, R := 1, a := 5, factors := [2, 2351], residues := [(2, 2351), (2351, 196)] },
    { n := 4721, F := 4720, R := 1, a := 6, factors := [2, 2, 2, 2, 5, 59], residues := [(2, 2360), (5, 2164), (59, 3655)] },
    { n := 4723, F := 4722, R := 1, a := 2, factors := [2, 3, 787], residues := [(2, 2361), (3, 2909), (787, 2399)] },
    { n := 4729, F := 4728, R := 1, a := 17, factors := [2, 2, 2, 3, 197], residues := [(2, 2364), (3, 897), (197, 3298)] },
    { n := 4733, F := 4732, R := 1, a := 5, factors := [2, 2, 7, 13, 13], residues := [(2, 2366), (7, 2754), (13, 236)] },
    { n := 4751, F := 4750, R := 1, a := 19, factors := [2, 5, 5, 5, 19], residues := [(2, 2375), (5, 4604), (19, 3701)] },
    { n := 4759, F := 4758, R := 1, a := 3, factors := [2, 3, 13, 61], residues := [(2, 2379), (3, 508), (13, 1070), (61, 4065)] },
    { n := 4783, F := 4782, R := 1, a := 6, factors := [2, 3, 797], residues := [(2, 2391), (3, 1012), (797, 2939)] },
    { n := 4787, F := 4786, R := 1, a := 2, factors := [2, 2393], residues := [(2, 2393), (2393, 1596)] },
    { n := 4789, F := 4788, R := 1, a := 2, factors := [2, 2, 3, 3, 7, 19], residues := [(2, 2394), (3, 3752), (7, 1009), (19, 2654)] },
    { n := 4793, F := 4792, R := 1, a := 3, factors := [2, 2, 2, 599], residues := [(2, 2396), (599, 4576)] },
    { n := 4799, F := 4798, R := 1, a := 7, factors := [2, 2399], residues := [(2, 2399), (2399, 100)] },
    { n := 4801, F := 4800, R := 1, a := 7, factors := [2, 2, 2, 2, 2, 2, 3, 5, 5], residues := [(2, 2400), (3, 2420), (5, 330)] },
    { n := 4813, F := 4812, R := 1, a := 2, factors := [2, 2, 3, 401], residues := [(2, 2406), (3, 4183), (401, 3412)] }
  ]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPocklingtonData02_valid : PocklingtonRow.Valid lowPocklingtonData02 := by
  apply PocklingtonRow.valid_of_decide_all
  decide

theorem lowPrime_4013 : Nat.Prime 4013 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4019 : Nat.Prime 4019 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4021 : Nat.Prime 4021 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4027 : Nat.Prime 4027 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4049 : Nat.Prime 4049 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4051 : Nat.Prime 4051 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4057 : Nat.Prime 4057 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4073 : Nat.Prime 4073 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4079 : Nat.Prime 4079 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4091 : Nat.Prime 4091 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4093 : Nat.Prime 4093 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4099 : Nat.Prime 4099 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4111 : Nat.Prime 4111 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4127 : Nat.Prime 4127 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4129 : Nat.Prime 4129 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4133 : Nat.Prime 4133 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4139 : Nat.Prime 4139 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4153 : Nat.Prime 4153 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4157 : Nat.Prime 4157 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4159 : Nat.Prime 4159 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4177 : Nat.Prime 4177 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4201 : Nat.Prime 4201 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4211 : Nat.Prime 4211 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4217 : Nat.Prime 4217 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4219 : Nat.Prime 4219 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4229 : Nat.Prime 4229 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4231 : Nat.Prime 4231 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4241 : Nat.Prime 4241 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4243 : Nat.Prime 4243 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4253 : Nat.Prime 4253 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4259 : Nat.Prime 4259 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4261 : Nat.Prime 4261 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4271 : Nat.Prime 4271 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4273 : Nat.Prime 4273 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4283 : Nat.Prime 4283 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4289 : Nat.Prime 4289 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4297 : Nat.Prime 4297 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4327 : Nat.Prime 4327 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4337 : Nat.Prime 4337 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4339 : Nat.Prime 4339 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4349 : Nat.Prime 4349 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4357 : Nat.Prime 4357 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4363 : Nat.Prime 4363 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4373 : Nat.Prime 4373 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4391 : Nat.Prime 4391 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4397 : Nat.Prime 4397 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4409 : Nat.Prime 4409 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4421 : Nat.Prime 4421 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4423 : Nat.Prime 4423 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4441 : Nat.Prime 4441 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4447 : Nat.Prime 4447 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4451 : Nat.Prime 4451 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4457 : Nat.Prime 4457 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4463 : Nat.Prime 4463 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4481 : Nat.Prime 4481 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4483 : Nat.Prime 4483 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4493 : Nat.Prime 4493 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4507 : Nat.Prime 4507 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4513 : Nat.Prime 4513 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4517 : Nat.Prime 4517 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4519 : Nat.Prime 4519 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4523 : Nat.Prime 4523 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4547 : Nat.Prime 4547 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4549 : Nat.Prime 4549 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4561 : Nat.Prime 4561 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4567 : Nat.Prime 4567 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4583 : Nat.Prime 4583 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4591 : Nat.Prime 4591 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4597 : Nat.Prime 4597 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4603 : Nat.Prime 4603 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4621 : Nat.Prime 4621 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4637 : Nat.Prime 4637 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4639 : Nat.Prime 4639 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4643 : Nat.Prime 4643 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4649 : Nat.Prime 4649 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4651 : Nat.Prime 4651 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4657 : Nat.Prime 4657 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4663 : Nat.Prime 4663 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4673 : Nat.Prime 4673 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4679 : Nat.Prime 4679 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4691 : Nat.Prime 4691 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4703 : Nat.Prime 4703 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4721 : Nat.Prime 4721 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4723 : Nat.Prime 4723 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4729 : Nat.Prime 4729 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4733 : Nat.Prime 4733 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4751 : Nat.Prime 4751 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4759 : Nat.Prime 4759 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4783 : Nat.Prime 4783 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4787 : Nat.Prime 4787 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4789 : Nat.Prime 4789 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4793 : Nat.Prime 4793 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4799 : Nat.Prime 4799 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4801 : Nat.Prime 4801 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]

theorem lowPrime_4813 : Nat.Prime 4813 := by
  apply PocklingtonRow.prime_of_mem lowPocklingtonData02_valid
  simp [lowPocklingtonData02]
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4007) (q := 4013) (by exact lowPrime_4013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4013) (q := 4019) (by exact lowPrime_4019) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4019) (q := 4021) (by exact lowPrime_4021) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4021) (q := 4027) (by exact lowPrime_4027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4027) (q := 4049) (by exact lowPrime_4049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4049) (q := 4051) (by exact lowPrime_4051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4051) (q := 4057) (by exact lowPrime_4057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4057) (q := 4073) (by exact lowPrime_4073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part04_chain :
    DusartPrimeRowsChain 4007 4072 dusartPrimeRows_3803_4672_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4073) (q := 4079) (by exact lowPrime_4079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4079) (q := 4091) (by exact lowPrime_4091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4091) (q := 4093) (by exact lowPrime_4093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4093) (q := 4099) (by exact lowPrime_4099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4099) (q := 4111) (by exact lowPrime_4111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4111) (q := 4127) (by exact lowPrime_4127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4127) (q := 4129) (by exact lowPrime_4129) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4129) (q := 4133) (by exact lowPrime_4133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part05_chain :
    DusartPrimeRowsChain 4073 4132 dusartPrimeRows_3803_4672_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4133) (q := 4139) (by exact lowPrime_4139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4139) (q := 4153) (by exact lowPrime_4153) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4153) (q := 4157) (by exact lowPrime_4157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4157) (q := 4159) (by exact lowPrime_4159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4159) (q := 4177) (by exact lowPrime_4177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4177) (q := 4201) (by exact lowPrime_4201) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4201) (q := 4211) (by exact lowPrime_4211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4211) (q := 4217) (by exact lowPrime_4217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part06_chain :
    DusartPrimeRowsChain 4133 4216 dusartPrimeRows_3803_4672_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4217) (q := 4219) (by exact lowPrime_4219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4219) (q := 4229) (by exact lowPrime_4229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4229) (q := 4231) (by exact lowPrime_4231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4231) (q := 4241) (by exact lowPrime_4241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4241) (q := 4243) (by exact lowPrime_4243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4243) (q := 4253) (by exact lowPrime_4253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4253) (q := 4259) (by exact lowPrime_4259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4259) (q := 4261) (by exact lowPrime_4261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part07_chain :
    DusartPrimeRowsChain 4217 4260 dusartPrimeRows_3803_4672_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4261) (q := 4271) (by exact lowPrime_4271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4271) (q := 4273) (by exact lowPrime_4273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4273) (q := 4283) (by exact lowPrime_4283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4283) (q := 4289) (by exact lowPrime_4289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4289) (q := 4297) (by exact lowPrime_4297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4297) (q := 4327) (by exact lowPrime_4327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4327) (q := 4337) (by exact lowPrime_4337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4337) (q := 4339) (by exact lowPrime_4339) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part08_chain :
    DusartPrimeRowsChain 4261 4338 dusartPrimeRows_3803_4672_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4339) (q := 4349) (by exact lowPrime_4349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4349) (q := 4357) (by exact lowPrime_4357) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4357) (q := 4363) (by exact lowPrime_4363) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4363) (q := 4373) (by exact lowPrime_4373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4373) (q := 4391) (by exact lowPrime_4391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4391) (q := 4397) (by exact lowPrime_4397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4397) (q := 4409) (by exact lowPrime_4409) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4409) (q := 4421) (by exact lowPrime_4421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part09_chain :
    DusartPrimeRowsChain 4339 4420 dusartPrimeRows_3803_4672_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4421) (q := 4423) (by exact lowPrime_4423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4423) (q := 4441) (by exact lowPrime_4441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4441) (q := 4447) (by exact lowPrime_4447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4447) (q := 4451) (by exact lowPrime_4451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4451) (q := 4457) (by exact lowPrime_4457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4457) (q := 4463) (by exact lowPrime_4463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4463) (q := 4481) (by exact lowPrime_4481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4481) (q := 4483) (by exact lowPrime_4483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part10_chain :
    DusartPrimeRowsChain 4421 4482 dusartPrimeRows_3803_4672_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4483) (q := 4493) (by exact lowPrime_4493) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4493) (q := 4507) (by exact lowPrime_4507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4507) (q := 4513) (by exact lowPrime_4513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4513) (q := 4517) (by exact lowPrime_4517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4517) (q := 4519) (by exact lowPrime_4519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4519) (q := 4523) (by exact lowPrime_4523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4523) (q := 4547) (by exact lowPrime_4547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4547) (q := 4549) (by exact lowPrime_4549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part11_chain :
    DusartPrimeRowsChain 4483 4548 dusartPrimeRows_3803_4672_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4549) (q := 4561) (by exact lowPrime_4561) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4561) (q := 4567) (by exact lowPrime_4567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4567) (q := 4583) (by exact lowPrime_4583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4583) (q := 4591) (by exact lowPrime_4591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4591) (q := 4597) (by exact lowPrime_4597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4597) (q := 4603) (by exact lowPrime_4603) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4603) (q := 4621) (by exact lowPrime_4621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4621) (q := 4637) (by exact lowPrime_4637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part12_chain :
    DusartPrimeRowsChain 4549 4636 dusartPrimeRows_3803_4672_part12 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4637) (q := 4639) (by exact lowPrime_4639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4639) (q := 4643) (by exact lowPrime_4643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4643) (q := 4649) (by exact lowPrime_4649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4649) (q := 4651) (by exact lowPrime_4651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4651) (q := 4657) (by exact lowPrime_4657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4657) (q := 4663) (by exact lowPrime_4663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4663) (q := 4673) (by exact lowPrime_4673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part13_chain :
    DusartPrimeRowsChain 4637 4672 dusartPrimeRows_3803_4672_part13 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4673) (q := 4679) (by exact lowPrime_4679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4679) (q := 4691) (by exact lowPrime_4691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4691) (q := 4703) (by exact lowPrime_4703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4703) (q := 4721) (by exact lowPrime_4721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4721) (q := 4723) (by exact lowPrime_4723) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4723) (q := 4729) (by exact lowPrime_4729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4729) (q := 4733) (by exact lowPrime_4733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4733) (q := 4751) (by exact lowPrime_4751) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part01_chain :
    DusartPrimeRowsChain 4673 4750 dusartPrimeRows_4673_4918_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4914, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4751) (q := 4759) (by exact lowPrime_4759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4759) (q := 4783) (by exact lowPrime_4783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4783) (q := 4787) (by exact lowPrime_4787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4787) (q := 4789) (by exact lowPrime_4789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4789) (q := 4793) (by exact lowPrime_4793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4793) (q := 4799) (by exact lowPrime_4799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4799) (q := 4801) (by exact lowPrime_4801) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4801) (q := 4813) (by exact lowPrime_4813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part02_chain :
    DusartPrimeRowsChain 4751 4812 dusartPrimeRows_4673_4918_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4914, dusartPrimeRow_of_explicit_right]
