import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00028_values : List Nat :=
  [fullRecordGapCenterValue + 387462,
    fullRecordGapCenterValue + 387546,
    fullRecordGapCenterValue + 387578,
    fullRecordGapCenterValue + 387606,
    fullRecordGapCenterValue + 387626,
    fullRecordGapCenterValue + 387836,
    fullRecordGapCenterValue + 387896,
    fullRecordGapCenterValue + 387978,
    fullRecordGapCenterValue + 388028,
    fullRecordGapCenterValue + 388080,
    fullRecordGapCenterValue + 388158,
    fullRecordGapCenterValue + 388166,
    fullRecordGapCenterValue + 388202,
    fullRecordGapCenterValue + 388238,
    fullRecordGapCenterValue + 388298,
    fullRecordGapCenterValue + 388328,
    fullRecordGapCenterValue + 388412,
    fullRecordGapCenterValue + 388568,
    fullRecordGapCenterValue + 388686,
    fullRecordGapCenterValue + 388742,
    fullRecordGapCenterValue + 388748,
    fullRecordGapCenterValue + 388826,
    fullRecordGapCenterValue + 388862,
    fullRecordGapCenterValue + 388866,
    fullRecordGapCenterValue + 388902,
    fullRecordGapCenterValue + 388958,
    fullRecordGapCenterValue + 389042,
    fullRecordGapCenterValue + 389118,
    fullRecordGapCenterValue + 389432,
    fullRecordGapCenterValue + 389492,
    fullRecordGapCenterValue + 389526,
    fullRecordGapCenterValue + 389562,
    fullRecordGapCenterValue + 389678,
    fullRecordGapCenterValue + 389706,
    fullRecordGapCenterValue + 389798,
    fullRecordGapCenterValue + 389996,
    fullRecordGapCenterValue + 390086,
    fullRecordGapCenterValue + 390092,
    fullRecordGapCenterValue + 390098,
    fullRecordGapCenterValue + 390162,
    fullRecordGapCenterValue + 390206,
    fullRecordGapCenterValue + 390296,
    fullRecordGapCenterValue + 390308,
    fullRecordGapCenterValue + 390332,
    fullRecordGapCenterValue + 390506,
    fullRecordGapCenterValue + 390542,
    fullRecordGapCenterValue + 390596,
    fullRecordGapCenterValue + 390666,
    fullRecordGapCenterValue + 390686,
    fullRecordGapCenterValue + 390692,
    fullRecordGapCenterValue + 390938,
    fullRecordGapCenterValue + 390968,
    fullRecordGapCenterValue + 390986,
    fullRecordGapCenterValue + 391038,
    fullRecordGapCenterValue + 391098,
    fullRecordGapCenterValue + 391148,
    fullRecordGapCenterValue + 391218,
    fullRecordGapCenterValue + 391316,
    fullRecordGapCenterValue + 391436,
    fullRecordGapCenterValue + 391542,
    fullRecordGapCenterValue + 391602,
    fullRecordGapCenterValue + 391862,
    fullRecordGapCenterValue + 391868,
    fullRecordGapCenterValue + 391892,
    fullRecordGapCenterValue + 391946,
    fullRecordGapCenterValue + 391962,
    fullRecordGapCenterValue + 392040,
    fullRecordGapCenterValue + 392142,
    fullRecordGapCenterValue + 392222,
    fullRecordGapCenterValue + 392226,
    fullRecordGapCenterValue + 392358,
    fullRecordGapCenterValue + 392582,
    fullRecordGapCenterValue + 392648,
    fullRecordGapCenterValue + 392682,
    fullRecordGapCenterValue + 392858,
    fullRecordGapCenterValue + 392936,
    fullRecordGapCenterValue + 393086,
    fullRecordGapCenterValue + 393188,
    fullRecordGapCenterValue + 393258,
    fullRecordGapCenterValue + 393306,
    fullRecordGapCenterValue + 393416,
    fullRecordGapCenterValue + 393522,
    fullRecordGapCenterValue + 393702,
    fullRecordGapCenterValue + 393716,
    fullRecordGapCenterValue + 393746,
    fullRecordGapCenterValue + 394062,
    fullRecordGapCenterValue + 394076,
    fullRecordGapCenterValue + 394088,
    fullRecordGapCenterValue + 394172,
    fullRecordGapCenterValue + 394178,
    fullRecordGapCenterValue + 394206,
    fullRecordGapCenterValue + 394242,
    fullRecordGapCenterValue + 394278,
    fullRecordGapCenterValue + 394292,
    fullRecordGapCenterValue + 394322,
    fullRecordGapCenterValue + 394556,
    fullRecordGapCenterValue + 394586,
    fullRecordGapCenterValue + 394622,
    fullRecordGapCenterValue + 394662,
    fullRecordGapCenterValue + 394682,
    fullRecordGapCenterValue + 394712,
    fullRecordGapCenterValue + 394718,
    fullRecordGapCenterValue + 394766,
    fullRecordGapCenterValue + 394868,
    fullRecordGapCenterValue + 394916,
    fullRecordGapCenterValue + 394952,
    fullRecordGapCenterValue + 394986,
    fullRecordGapCenterValue + 395022,
    fullRecordGapCenterValue + 395078,
    fullRecordGapCenterValue + 395106,
    fullRecordGapCenterValue + 395202,
    fullRecordGapCenterValue + 395286,
    fullRecordGapCenterValue + 395288,
    fullRecordGapCenterValue + 395378,
    fullRecordGapCenterValue + 395526,
    fullRecordGapCenterValue + 395636,
    fullRecordGapCenterValue + 395816,
    fullRecordGapCenterValue + 395852,
    fullRecordGapCenterValue + 395942,
    fullRecordGapCenterValue + 395958,
    fullRecordGapCenterValue + 396000,
    fullRecordGapCenterValue + 396026,
    fullRecordGapCenterValue + 396068,
    fullRecordGapCenterValue + 396086,
    fullRecordGapCenterValue + 396212,
    fullRecordGapCenterValue + 396218,
    fullRecordGapCenterValue + 396246,
    fullRecordGapCenterValue + 396278,
    fullRecordGapCenterValue + 396386,
    fullRecordGapCenterValue + 396426,
    fullRecordGapCenterValue + 396498,
    fullRecordGapCenterValue + 396692,
    fullRecordGapCenterValue + 396782,
    fullRecordGapCenterValue + 397058,
    fullRecordGapCenterValue + 397226,
    fullRecordGapCenterValue + 397346,
    fullRecordGapCenterValue + 397388,
    fullRecordGapCenterValue + 397622,
    fullRecordGapCenterValue + 397682,
    fullRecordGapCenterValue + 397688,
    fullRecordGapCenterValue + 397806,
    fullRecordGapCenterValue + 398078,
    fullRecordGapCenterValue + 398162,
    fullRecordGapCenterValue + 398252,
    fullRecordGapCenterValue + 398408,
    fullRecordGapCenterValue + 398756,
    fullRecordGapCenterValue + 398778,
    fullRecordGapCenterValue + 398798,
    fullRecordGapCenterValue + 398802,
    fullRecordGapCenterValue + 398822,
    fullRecordGapCenterValue + 398828,
    fullRecordGapCenterValue + 398858,
    fullRecordGapCenterValue + 398946,
    fullRecordGapCenterValue + 399002,
    fullRecordGapCenterValue + 399236,
    fullRecordGapCenterValue + 399242,
    fullRecordGapCenterValue + 399246,
    fullRecordGapCenterValue + 399332,
    fullRecordGapCenterValue + 399368,
    fullRecordGapCenterValue + 399458,
    fullRecordGapCenterValue + 399506,
    fullRecordGapCenterValue + 399512,
    fullRecordGapCenterValue + 399558,
    fullRecordGapCenterValue + 399638,
    fullRecordGapCenterValue + 399662,
    fullRecordGapCenterValue + 399702,
    fullRecordGapCenterValue + 399716,
    fullRecordGapCenterValue + 399746,
    fullRecordGapCenterValue + 399998,
    fullRecordGapCenterValue + 400046,
    fullRecordGapCenterValue + 400058,
    fullRecordGapCenterValue + 400082,
    fullRecordGapCenterValue + 400206,
    fullRecordGapCenterValue + 400382,
    fullRecordGapCenterValue + 400586,
    fullRecordGapCenterValue + 400676,
    fullRecordGapCenterValue + 400746,
    fullRecordGapCenterValue + 400766,
    fullRecordGapCenterValue + 400802,
    fullRecordGapCenterValue + 400886,
    fullRecordGapCenterValue + 400922,
    fullRecordGapCenterValue + 401252,
    fullRecordGapCenterValue + 401378,
    fullRecordGapCenterValue + 401426,
    fullRecordGapCenterValue + 401462,
    fullRecordGapCenterValue + 401516,
    fullRecordGapCenterValue + 401538,
    fullRecordGapCenterValue + 401586,
    fullRecordGapCenterValue + 401612,
    fullRecordGapCenterValue + 401762,
    fullRecordGapCenterValue + 401768,
    fullRecordGapCenterValue + 401798,
    fullRecordGapCenterValue + 401942,
    fullRecordGapCenterValue + 401966,
    fullRecordGapCenterValue + 401972,
    fullRecordGapCenterValue + 402092,
    fullRecordGapCenterValue + 402098,
    fullRecordGapCenterValue + 402126,
    fullRecordGapCenterValue + 402188,
    fullRecordGapCenterValue + 402386,
    fullRecordGapCenterValue + 402452,
    fullRecordGapCenterValue + 402692,
    fullRecordGapCenterValue + 402806,
    fullRecordGapCenterValue + 402812,
    fullRecordGapCenterValue + 402902,
    fullRecordGapCenterValue + 402932,
    fullRecordGapCenterValue + 403016,
    fullRecordGapCenterValue + 403076,
    fullRecordGapCenterValue + 403148,
    fullRecordGapCenterValue + 403266,
    fullRecordGapCenterValue + 403292,
    fullRecordGapCenterValue + 403302,
    fullRecordGapCenterValue + 403386,
    fullRecordGapCenterValue + 403412,
    fullRecordGapCenterValue + 403418,
    fullRecordGapCenterValue + 403538,
    fullRecordGapCenterValue + 403562,
    fullRecordGapCenterValue + 403566,
    fullRecordGapCenterValue + 403638,
    fullRecordGapCenterValue + 403778,
    fullRecordGapCenterValue + 403838,
    fullRecordGapCenterValue + 403946,
    fullRecordGapCenterValue + 404126,
    fullRecordGapCenterValue + 404252,
    fullRecordGapCenterValue + 404258,
    fullRecordGapCenterValue + 404346,
    fullRecordGapCenterValue + 404366,
    fullRecordGapCenterValue + 404402,
    fullRecordGapCenterValue + 404526,
    fullRecordGapCenterValue + 404762,
    fullRecordGapCenterValue + 404792,
    fullRecordGapCenterValue + 404958,
    fullRecordGapCenterValue + 405000,
    fullRecordGapCenterValue + 405116,
    fullRecordGapCenterValue + 405176,
    fullRecordGapCenterValue + 405282,
    fullRecordGapCenterValue + 405332,
    fullRecordGapCenterValue + 405386,
    fullRecordGapCenterValue + 405402,
    fullRecordGapCenterValue + 405452,
    fullRecordGapCenterValue + 405458,
    fullRecordGapCenterValue + 405506,
    fullRecordGapCenterValue + 405906,
    fullRecordGapCenterValue + 405932,
    fullRecordGapCenterValue + 405998,
    fullRecordGapCenterValue + 406052,
    fullRecordGapCenterValue + 406338,
    fullRecordGapCenterValue + 406418,
    fullRecordGapCenterValue + 406442,
    fullRecordGapCenterValue + 406506,
    fullRecordGapCenterValue + 406560,
    fullRecordGapCenterValue + 406646,
    fullRecordGapCenterValue + 406682,
    fullRecordGapCenterValue + 406698,
    fullRecordGapCenterValue + 406712,
    fullRecordGapCenterValue + 406856]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00028_fermat : ∀ n ∈ fullRecordGapRow00028_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06913_not_prime : ¬(recordGapCenter + 387462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387462]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06914_not_prime : ¬(recordGapCenter + 387546).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387546]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06915_not_prime : ¬(recordGapCenter + 387578).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387578]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06916_not_prime : ¬(recordGapCenter + 387606).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387606]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06917_not_prime : ¬(recordGapCenter + 387626).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387626]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06918_not_prime : ¬(recordGapCenter + 387836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387836]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06919_not_prime : ¬(recordGapCenter + 387896).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387896]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06920_not_prime : ¬(recordGapCenter + 387978).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 387978]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06921_not_prime : ¬(recordGapCenter + 388028).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388028]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06922_not_prime : ¬(recordGapCenter + 388080).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388080]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06923_not_prime : ¬(recordGapCenter + 388158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388158]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06924_not_prime : ¬(recordGapCenter + 388166).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388166]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06925_not_prime : ¬(recordGapCenter + 388202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388202]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06926_not_prime : ¬(recordGapCenter + 388238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388238]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06927_not_prime : ¬(recordGapCenter + 388298).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388298]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06928_not_prime : ¬(recordGapCenter + 388328).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388328]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06929_not_prime : ¬(recordGapCenter + 388412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388412]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06930_not_prime : ¬(recordGapCenter + 388568).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388568]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06931_not_prime : ¬(recordGapCenter + 388686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388686]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06932_not_prime : ¬(recordGapCenter + 388742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388742]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06933_not_prime : ¬(recordGapCenter + 388748).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388748]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06934_not_prime : ¬(recordGapCenter + 388826).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388826]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06935_not_prime : ¬(recordGapCenter + 388862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388862]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06936_not_prime : ¬(recordGapCenter + 388866).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388866]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06937_not_prime : ¬(recordGapCenter + 388902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388902]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06938_not_prime : ¬(recordGapCenter + 388958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 388958]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06939_not_prime : ¬(recordGapCenter + 389042).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389042]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06940_not_prime : ¬(recordGapCenter + 389118).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389118]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06941_not_prime : ¬(recordGapCenter + 389432).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389432]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06942_not_prime : ¬(recordGapCenter + 389492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389492]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06943_not_prime : ¬(recordGapCenter + 389526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389526]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06944_not_prime : ¬(recordGapCenter + 389562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389562]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06945_not_prime : ¬(recordGapCenter + 389678).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389678]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06946_not_prime : ¬(recordGapCenter + 389706).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389706]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06947_not_prime : ¬(recordGapCenter + 389798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389798]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06948_not_prime : ¬(recordGapCenter + 389996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 389996]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06949_not_prime : ¬(recordGapCenter + 390086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390086]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06950_not_prime : ¬(recordGapCenter + 390092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390092]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06951_not_prime : ¬(recordGapCenter + 390098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390098]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06952_not_prime : ¬(recordGapCenter + 390162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390162]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06953_not_prime : ¬(recordGapCenter + 390206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390206]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06954_not_prime : ¬(recordGapCenter + 390296).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390296]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06955_not_prime : ¬(recordGapCenter + 390308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390308]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06956_not_prime : ¬(recordGapCenter + 390332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390332]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06957_not_prime : ¬(recordGapCenter + 390506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390506]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06958_not_prime : ¬(recordGapCenter + 390542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390542]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06959_not_prime : ¬(recordGapCenter + 390596).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390596]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06960_not_prime : ¬(recordGapCenter + 390666).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390666]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06961_not_prime : ¬(recordGapCenter + 390686).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390686]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06962_not_prime : ¬(recordGapCenter + 390692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390692]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06963_not_prime : ¬(recordGapCenter + 390938).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390938]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06964_not_prime : ¬(recordGapCenter + 390968).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390968]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06965_not_prime : ¬(recordGapCenter + 390986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 390986]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06966_not_prime : ¬(recordGapCenter + 391038).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391038]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06967_not_prime : ¬(recordGapCenter + 391098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391098]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06968_not_prime : ¬(recordGapCenter + 391148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391148]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06969_not_prime : ¬(recordGapCenter + 391218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391218]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06970_not_prime : ¬(recordGapCenter + 391316).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391316]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06971_not_prime : ¬(recordGapCenter + 391436).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391436]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06972_not_prime : ¬(recordGapCenter + 391542).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391542]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06973_not_prime : ¬(recordGapCenter + 391602).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391602]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06974_not_prime : ¬(recordGapCenter + 391862).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391862]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06975_not_prime : ¬(recordGapCenter + 391868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391868]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06976_not_prime : ¬(recordGapCenter + 391892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391892]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06977_not_prime : ¬(recordGapCenter + 391946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391946]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06978_not_prime : ¬(recordGapCenter + 391962).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 391962]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06979_not_prime : ¬(recordGapCenter + 392040).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392040]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06980_not_prime : ¬(recordGapCenter + 392142).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392142]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06981_not_prime : ¬(recordGapCenter + 392222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392222]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06982_not_prime : ¬(recordGapCenter + 392226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392226]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06983_not_prime : ¬(recordGapCenter + 392358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392358]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06984_not_prime : ¬(recordGapCenter + 392582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392582]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06985_not_prime : ¬(recordGapCenter + 392648).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392648]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06986_not_prime : ¬(recordGapCenter + 392682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392682]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06987_not_prime : ¬(recordGapCenter + 392858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392858]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06988_not_prime : ¬(recordGapCenter + 392936).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 392936]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06989_not_prime : ¬(recordGapCenter + 393086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393086]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06990_not_prime : ¬(recordGapCenter + 393188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393188]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06991_not_prime : ¬(recordGapCenter + 393258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393258]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06992_not_prime : ¬(recordGapCenter + 393306).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393306]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06993_not_prime : ¬(recordGapCenter + 393416).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393416]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06994_not_prime : ¬(recordGapCenter + 393522).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393522]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06995_not_prime : ¬(recordGapCenter + 393702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393702]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06996_not_prime : ¬(recordGapCenter + 393716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393716]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06997_not_prime : ¬(recordGapCenter + 393746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 393746]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06998_not_prime : ¬(recordGapCenter + 394062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394062]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm06999_not_prime : ¬(recordGapCenter + 394076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394076]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07000_not_prime : ¬(recordGapCenter + 394088).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394088]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07001_not_prime : ¬(recordGapCenter + 394172).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394172]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07002_not_prime : ¬(recordGapCenter + 394178).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394178]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07003_not_prime : ¬(recordGapCenter + 394206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394206]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07004_not_prime : ¬(recordGapCenter + 394242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394242]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07005_not_prime : ¬(recordGapCenter + 394278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394278]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07006_not_prime : ¬(recordGapCenter + 394292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394292]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07007_not_prime : ¬(recordGapCenter + 394322).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394322]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07008_not_prime : ¬(recordGapCenter + 394556).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394556]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07009_not_prime : ¬(recordGapCenter + 394586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394586]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07010_not_prime : ¬(recordGapCenter + 394622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394622]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07011_not_prime : ¬(recordGapCenter + 394662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394662]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07012_not_prime : ¬(recordGapCenter + 394682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394682]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07013_not_prime : ¬(recordGapCenter + 394712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394712]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07014_not_prime : ¬(recordGapCenter + 394718).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394718]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07015_not_prime : ¬(recordGapCenter + 394766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394766]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07016_not_prime : ¬(recordGapCenter + 394868).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394868]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07017_not_prime : ¬(recordGapCenter + 394916).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394916]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07018_not_prime : ¬(recordGapCenter + 394952).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394952]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07019_not_prime : ¬(recordGapCenter + 394986).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 394986]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07020_not_prime : ¬(recordGapCenter + 395022).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395022]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07021_not_prime : ¬(recordGapCenter + 395078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395078]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07022_not_prime : ¬(recordGapCenter + 395106).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395106]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07023_not_prime : ¬(recordGapCenter + 395202).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395202]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07024_not_prime : ¬(recordGapCenter + 395286).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395286]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07025_not_prime : ¬(recordGapCenter + 395288).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395288]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07026_not_prime : ¬(recordGapCenter + 395378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395378]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07027_not_prime : ¬(recordGapCenter + 395526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395526]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07028_not_prime : ¬(recordGapCenter + 395636).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395636]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07029_not_prime : ¬(recordGapCenter + 395816).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395816]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07030_not_prime : ¬(recordGapCenter + 395852).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395852]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07031_not_prime : ¬(recordGapCenter + 395942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395942]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07032_not_prime : ¬(recordGapCenter + 395958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 395958]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07033_not_prime : ¬(recordGapCenter + 396000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396000]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07034_not_prime : ¬(recordGapCenter + 396026).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396026]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07035_not_prime : ¬(recordGapCenter + 396068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396068]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07036_not_prime : ¬(recordGapCenter + 396086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396086]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07037_not_prime : ¬(recordGapCenter + 396212).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396212]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07038_not_prime : ¬(recordGapCenter + 396218).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396218]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07039_not_prime : ¬(recordGapCenter + 396246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396246]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07040_not_prime : ¬(recordGapCenter + 396278).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396278]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07041_not_prime : ¬(recordGapCenter + 396386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396386]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07042_not_prime : ¬(recordGapCenter + 396426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396426]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07043_not_prime : ¬(recordGapCenter + 396498).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396498]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07044_not_prime : ¬(recordGapCenter + 396692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396692]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07045_not_prime : ¬(recordGapCenter + 396782).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 396782]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07046_not_prime : ¬(recordGapCenter + 397058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397058]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07047_not_prime : ¬(recordGapCenter + 397226).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397226]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07048_not_prime : ¬(recordGapCenter + 397346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397346]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07049_not_prime : ¬(recordGapCenter + 397388).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397388]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07050_not_prime : ¬(recordGapCenter + 397622).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397622]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07051_not_prime : ¬(recordGapCenter + 397682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397682]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07052_not_prime : ¬(recordGapCenter + 397688).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397688]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07053_not_prime : ¬(recordGapCenter + 397806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 397806]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07054_not_prime : ¬(recordGapCenter + 398078).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398078]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07055_not_prime : ¬(recordGapCenter + 398162).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398162]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07056_not_prime : ¬(recordGapCenter + 398252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398252]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07057_not_prime : ¬(recordGapCenter + 398408).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398408]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07058_not_prime : ¬(recordGapCenter + 398756).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398756]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07059_not_prime : ¬(recordGapCenter + 398778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398778]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07060_not_prime : ¬(recordGapCenter + 398798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398798]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07061_not_prime : ¬(recordGapCenter + 398802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398802]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07062_not_prime : ¬(recordGapCenter + 398822).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398822]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07063_not_prime : ¬(recordGapCenter + 398828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398828]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07064_not_prime : ¬(recordGapCenter + 398858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398858]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07065_not_prime : ¬(recordGapCenter + 398946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 398946]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07066_not_prime : ¬(recordGapCenter + 399002).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399002]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07067_not_prime : ¬(recordGapCenter + 399236).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399236]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07068_not_prime : ¬(recordGapCenter + 399242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399242]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07069_not_prime : ¬(recordGapCenter + 399246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399246]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07070_not_prime : ¬(recordGapCenter + 399332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399332]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07071_not_prime : ¬(recordGapCenter + 399368).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399368]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07072_not_prime : ¬(recordGapCenter + 399458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399458]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07073_not_prime : ¬(recordGapCenter + 399506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399506]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07074_not_prime : ¬(recordGapCenter + 399512).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399512]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07075_not_prime : ¬(recordGapCenter + 399558).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399558]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07076_not_prime : ¬(recordGapCenter + 399638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399638]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07077_not_prime : ¬(recordGapCenter + 399662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399662]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07078_not_prime : ¬(recordGapCenter + 399702).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399702]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07079_not_prime : ¬(recordGapCenter + 399716).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399716]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07080_not_prime : ¬(recordGapCenter + 399746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399746]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07081_not_prime : ¬(recordGapCenter + 399998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 399998]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07082_not_prime : ¬(recordGapCenter + 400046).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400046]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07083_not_prime : ¬(recordGapCenter + 400058).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400058]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07084_not_prime : ¬(recordGapCenter + 400082).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400082]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07085_not_prime : ¬(recordGapCenter + 400206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400206]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07086_not_prime : ¬(recordGapCenter + 400382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400382]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07087_not_prime : ¬(recordGapCenter + 400586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400586]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07088_not_prime : ¬(recordGapCenter + 400676).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400676]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07089_not_prime : ¬(recordGapCenter + 400746).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400746]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07090_not_prime : ¬(recordGapCenter + 400766).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400766]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07091_not_prime : ¬(recordGapCenter + 400802).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400802]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07092_not_prime : ¬(recordGapCenter + 400886).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400886]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07093_not_prime : ¬(recordGapCenter + 400922).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 400922]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07094_not_prime : ¬(recordGapCenter + 401252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401252]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07095_not_prime : ¬(recordGapCenter + 401378).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401378]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07096_not_prime : ¬(recordGapCenter + 401426).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401426]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07097_not_prime : ¬(recordGapCenter + 401462).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401462]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07098_not_prime : ¬(recordGapCenter + 401516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401516]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07099_not_prime : ¬(recordGapCenter + 401538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401538]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07100_not_prime : ¬(recordGapCenter + 401586).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401586]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07101_not_prime : ¬(recordGapCenter + 401612).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401612]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07102_not_prime : ¬(recordGapCenter + 401762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401762]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07103_not_prime : ¬(recordGapCenter + 401768).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401768]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07104_not_prime : ¬(recordGapCenter + 401798).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401798]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07105_not_prime : ¬(recordGapCenter + 401942).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401942]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07106_not_prime : ¬(recordGapCenter + 401966).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401966]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07107_not_prime : ¬(recordGapCenter + 401972).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 401972]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07108_not_prime : ¬(recordGapCenter + 402092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402092]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07109_not_prime : ¬(recordGapCenter + 402098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402098]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07110_not_prime : ¬(recordGapCenter + 402126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402126]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07111_not_prime : ¬(recordGapCenter + 402188).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402188]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07112_not_prime : ¬(recordGapCenter + 402386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402386]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07113_not_prime : ¬(recordGapCenter + 402452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402452]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07114_not_prime : ¬(recordGapCenter + 402692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402692]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07115_not_prime : ¬(recordGapCenter + 402806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402806]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07116_not_prime : ¬(recordGapCenter + 402812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402812]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07117_not_prime : ¬(recordGapCenter + 402902).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402902]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07118_not_prime : ¬(recordGapCenter + 402932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 402932]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07119_not_prime : ¬(recordGapCenter + 403016).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403016]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07120_not_prime : ¬(recordGapCenter + 403076).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403076]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07121_not_prime : ¬(recordGapCenter + 403148).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403148]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07122_not_prime : ¬(recordGapCenter + 403266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403266]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07123_not_prime : ¬(recordGapCenter + 403292).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403292]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07124_not_prime : ¬(recordGapCenter + 403302).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403302]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07125_not_prime : ¬(recordGapCenter + 403386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403386]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07126_not_prime : ¬(recordGapCenter + 403412).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403412]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07127_not_prime : ¬(recordGapCenter + 403418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403418]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07128_not_prime : ¬(recordGapCenter + 403538).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403538]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07129_not_prime : ¬(recordGapCenter + 403562).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403562]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07130_not_prime : ¬(recordGapCenter + 403566).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403566]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07131_not_prime : ¬(recordGapCenter + 403638).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403638]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07132_not_prime : ¬(recordGapCenter + 403778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403778]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07133_not_prime : ¬(recordGapCenter + 403838).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403838]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07134_not_prime : ¬(recordGapCenter + 403946).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 403946]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07135_not_prime : ¬(recordGapCenter + 404126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404126]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07136_not_prime : ¬(recordGapCenter + 404252).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404252]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07137_not_prime : ¬(recordGapCenter + 404258).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404258]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07138_not_prime : ¬(recordGapCenter + 404346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404346]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07139_not_prime : ¬(recordGapCenter + 404366).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404366]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07140_not_prime : ¬(recordGapCenter + 404402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404402]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07141_not_prime : ¬(recordGapCenter + 404526).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404526]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07142_not_prime : ¬(recordGapCenter + 404762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404762]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07143_not_prime : ¬(recordGapCenter + 404792).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404792]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07144_not_prime : ¬(recordGapCenter + 404958).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 404958]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07145_not_prime : ¬(recordGapCenter + 405000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405000]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07146_not_prime : ¬(recordGapCenter + 405116).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405116]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07147_not_prime : ¬(recordGapCenter + 405176).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405176]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07148_not_prime : ¬(recordGapCenter + 405282).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405282]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07149_not_prime : ¬(recordGapCenter + 405332).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405332]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07150_not_prime : ¬(recordGapCenter + 405386).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405386]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07151_not_prime : ¬(recordGapCenter + 405402).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405402]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07152_not_prime : ¬(recordGapCenter + 405452).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405452]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07153_not_prime : ¬(recordGapCenter + 405458).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405458]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07154_not_prime : ¬(recordGapCenter + 405506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405506]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07155_not_prime : ¬(recordGapCenter + 405906).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405906]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07156_not_prime : ¬(recordGapCenter + 405932).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405932]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07157_not_prime : ¬(recordGapCenter + 405998).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 405998]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07158_not_prime : ¬(recordGapCenter + 406052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406052]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07159_not_prime : ¬(recordGapCenter + 406338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406338]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07160_not_prime : ¬(recordGapCenter + 406418).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406418]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07161_not_prime : ¬(recordGapCenter + 406442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406442]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07162_not_prime : ¬(recordGapCenter + 406506).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406506]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07163_not_prime : ¬(recordGapCenter + 406560).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406560]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07164_not_prime : ¬(recordGapCenter + 406646).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406646]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07165_not_prime : ¬(recordGapCenter + 406682).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406682]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07166_not_prime : ¬(recordGapCenter + 406698).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406698]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07167_not_prime : ¬(recordGapCenter + 406712).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406712]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

theorem fullRecordGapTerm07168_not_prime : ¬(recordGapCenter + 406856).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 406856]
  · apply fullRecordGapRow00028_fermat
    simp [fullRecordGapRow00028_values]

end PrimeFactorUnimodality
