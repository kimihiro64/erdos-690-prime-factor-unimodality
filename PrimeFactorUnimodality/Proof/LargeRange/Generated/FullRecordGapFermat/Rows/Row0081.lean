import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapRow00081_values : List Nat :=
  [fullRecordGapCenterValue + 237086,
    fullRecordGapCenterValue + 237092,
    fullRecordGapCenterValue + 237098,
    fullRecordGapCenterValue + 237206,
    fullRecordGapCenterValue + 237338,
    fullRecordGapCenterValue + 237476,
    fullRecordGapCenterValue + 237788,
    fullRecordGapCenterValue + 237806,
    fullRecordGapCenterValue + 237812,
    fullRecordGapCenterValue + 238052,
    fullRecordGapCenterValue + 238140,
    fullRecordGapCenterValue + 238262,
    fullRecordGapCenterValue + 238268,
    fullRecordGapCenterValue + 238346,
    fullRecordGapCenterValue + 238358,
    fullRecordGapCenterValue + 238466,
    fullRecordGapCenterValue + 238598,
    fullRecordGapCenterValue + 238778,
    fullRecordGapCenterValue + 238796,
    fullRecordGapCenterValue + 238892,
    fullRecordGapCenterValue + 238988,
    fullRecordGapCenterValue + 239066,
    fullRecordGapCenterValue + 239138,
    fullRecordGapCenterValue + 239222,
    fullRecordGapCenterValue + 239516,
    fullRecordGapCenterValue + 239762,
    fullRecordGapCenterValue + 239828,
    fullRecordGapCenterValue + 239846,
    fullRecordGapCenterValue + 239858,
    fullRecordGapCenterValue + 239996,
    fullRecordGapCenterValue + 240000,
    fullRecordGapCenterValue + 240068,
    fullRecordGapCenterValue + 240098,
    fullRecordGapCenterValue + 240158,
    fullRecordGapCenterValue + 240182,
    fullRecordGapCenterValue + 240206,
    fullRecordGapCenterValue + 240242,
    fullRecordGapCenterValue + 240308,
    fullRecordGapCenterValue + 240356,
    fullRecordGapCenterValue + 240446,
    fullRecordGapCenterValue + 240570,
    fullRecordGapCenterValue + 240662,
    fullRecordGapCenterValue + 240836,
    fullRecordGapCenterValue + 241238,
    fullRecordGapCenterValue + 241382,
    fullRecordGapCenterValue + 241442,
    fullRecordGapCenterValue + 241472,
    fullRecordGapCenterValue + 241652,
    fullRecordGapCenterValue + 241742,
    fullRecordGapCenterValue + 241778,
    fullRecordGapCenterValue + 241796,
    fullRecordGapCenterValue + 241920,
    fullRecordGapCenterValue + 242036,
    fullRecordGapCenterValue + 242126,
    fullRecordGapCenterValue + 242246,
    fullRecordGapCenterValue + 242342,
    fullRecordGapCenterValue + 242492,
    fullRecordGapCenterValue + 242550,
    fullRecordGapCenterValue + 242582,
    fullRecordGapCenterValue + 243062,
    fullRecordGapCenterValue + 243266,
    fullRecordGapCenterValue + 243476,
    fullRecordGapCenterValue + 243548,
    fullRecordGapCenterValue + 243692]

set_option maxHeartbeats 0 in
theorem fullRecordGapRow00081_fermat : ∀ n ∈ fullRecordGapRow00081_values,
    fastPowMod 3 n (n - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05121_not_prime : ¬(recordGapCenter + 237086).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 237086]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05122_not_prime : ¬(recordGapCenter + 237092).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 237092]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05123_not_prime : ¬(recordGapCenter + 237098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 237098]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05124_not_prime : ¬(recordGapCenter + 237206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 237206]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05125_not_prime : ¬(recordGapCenter + 237338).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 237338]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05126_not_prime : ¬(recordGapCenter + 237476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 237476]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05127_not_prime : ¬(recordGapCenter + 237788).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 237788]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05128_not_prime : ¬(recordGapCenter + 237806).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 237806]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05129_not_prime : ¬(recordGapCenter + 237812).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 237812]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05130_not_prime : ¬(recordGapCenter + 238052).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238052]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05131_not_prime : ¬(recordGapCenter + 238140).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238140]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05132_not_prime : ¬(recordGapCenter + 238262).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238262]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05133_not_prime : ¬(recordGapCenter + 238268).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238268]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05134_not_prime : ¬(recordGapCenter + 238346).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238346]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05135_not_prime : ¬(recordGapCenter + 238358).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238358]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05136_not_prime : ¬(recordGapCenter + 238466).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238466]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05137_not_prime : ¬(recordGapCenter + 238598).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238598]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05138_not_prime : ¬(recordGapCenter + 238778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238778]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05139_not_prime : ¬(recordGapCenter + 238796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238796]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05140_not_prime : ¬(recordGapCenter + 238892).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238892]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05141_not_prime : ¬(recordGapCenter + 238988).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 238988]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05142_not_prime : ¬(recordGapCenter + 239066).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 239066]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05143_not_prime : ¬(recordGapCenter + 239138).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 239138]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05144_not_prime : ¬(recordGapCenter + 239222).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 239222]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05145_not_prime : ¬(recordGapCenter + 239516).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 239516]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05146_not_prime : ¬(recordGapCenter + 239762).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 239762]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05147_not_prime : ¬(recordGapCenter + 239828).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 239828]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05148_not_prime : ¬(recordGapCenter + 239846).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 239846]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05149_not_prime : ¬(recordGapCenter + 239858).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 239858]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05150_not_prime : ¬(recordGapCenter + 239996).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 239996]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05151_not_prime : ¬(recordGapCenter + 240000).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240000]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05152_not_prime : ¬(recordGapCenter + 240068).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240068]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05153_not_prime : ¬(recordGapCenter + 240098).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240098]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05154_not_prime : ¬(recordGapCenter + 240158).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240158]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05155_not_prime : ¬(recordGapCenter + 240182).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240182]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05156_not_prime : ¬(recordGapCenter + 240206).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240206]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05157_not_prime : ¬(recordGapCenter + 240242).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240242]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05158_not_prime : ¬(recordGapCenter + 240308).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240308]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05159_not_prime : ¬(recordGapCenter + 240356).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240356]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05160_not_prime : ¬(recordGapCenter + 240446).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240446]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05161_not_prime : ¬(recordGapCenter + 240570).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240570]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05162_not_prime : ¬(recordGapCenter + 240662).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240662]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05163_not_prime : ¬(recordGapCenter + 240836).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 240836]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05164_not_prime : ¬(recordGapCenter + 241238).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 241238]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05165_not_prime : ¬(recordGapCenter + 241382).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 241382]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05166_not_prime : ¬(recordGapCenter + 241442).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 241442]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05167_not_prime : ¬(recordGapCenter + 241472).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 241472]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05168_not_prime : ¬(recordGapCenter + 241652).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 241652]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05169_not_prime : ¬(recordGapCenter + 241742).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 241742]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05170_not_prime : ¬(recordGapCenter + 241778).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 241778]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05171_not_prime : ¬(recordGapCenter + 241796).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 241796]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05172_not_prime : ¬(recordGapCenter + 241920).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 241920]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05173_not_prime : ¬(recordGapCenter + 242036).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 242036]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05174_not_prime : ¬(recordGapCenter + 242126).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 242126]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05175_not_prime : ¬(recordGapCenter + 242246).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 242246]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05176_not_prime : ¬(recordGapCenter + 242342).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 242342]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05177_not_prime : ¬(recordGapCenter + 242492).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 242492]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05178_not_prime : ¬(recordGapCenter + 242550).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 242550]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05179_not_prime : ¬(recordGapCenter + 242582).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 242582]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05180_not_prime : ¬(recordGapCenter + 243062).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 243062]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05181_not_prime : ¬(recordGapCenter + 243266).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 243266]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05182_not_prime : ¬(recordGapCenter + 243476).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 243476]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05183_not_prime : ¬(recordGapCenter + 243548).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 243548]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

theorem fullRecordGapTerm05184_not_prime : ¬(recordGapCenter + 243692).Prime := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapCenterValue + 243692]
  · apply fullRecordGapRow00081_fermat
    simp [fullRecordGapRow00081_values]

end PrimeFactorUnimodality
