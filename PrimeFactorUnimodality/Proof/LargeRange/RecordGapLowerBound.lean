import Mathlib.Algebra.Order.BigOperators.Group.List
import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapPrimeList

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # A compact structural lower bound for the certified record-gap input -/

namespace PrimeFactorUnimodality

/-- Ten coarse blocks under the increasing prime list.  The bound retains
enough logarithmic size for the optimized finite-range calculation without
normalizing the full 18,662-digit center. -/
def recordGapLowerFactors : List (Nat × Nat) :=
  [(13, 450), (3221, 450), (7043, 450), (11197, 450), (15461, 450),
    (19961, 450), (24373, 450), (29021, 450), (33641, 450), (38453, 449)]

def recordGapLowerProduct : Nat :=
  (recordGapLowerFactors.map (fun factor => factor.1 ^ factor.2)).prod

private theorem chunk0 : 13 ^ 450 ≤ (recordGapPrimeList.take 450).prod := by
  have h := List.pow_length_le_prod (recordGapPrimeList.take 450) 13 (by decide)
  have len : (recordGapPrimeList.take 450).length = 450 := by decide
  rwa [len] at h

private theorem chunk1 : 3221 ^ 450 ≤
    ((recordGapPrimeList.drop 450).take 450).prod := by
  have h := List.pow_length_le_prod ((recordGapPrimeList.drop 450).take 450) 3221
    (by decide)
  have len : ((recordGapPrimeList.drop 450).take 450).length = 450 := by decide
  rwa [len] at h

private theorem chunk2 : 7043 ^ 450 ≤
    ((recordGapPrimeList.drop 900).take 450).prod := by
  have h := List.pow_length_le_prod ((recordGapPrimeList.drop 900).take 450) 7043
    (by decide)
  have len : ((recordGapPrimeList.drop 900).take 450).length = 450 := by decide
  rwa [len] at h

private theorem chunk3 : 11197 ^ 450 ≤
    ((recordGapPrimeList.drop 1350).take 450).prod := by
  have h := List.pow_length_le_prod ((recordGapPrimeList.drop 1350).take 450) 11197
    (by decide)
  have len : ((recordGapPrimeList.drop 1350).take 450).length = 450 := by decide
  rwa [len] at h

private theorem chunk4 : 15461 ^ 450 ≤
    ((recordGapPrimeList.drop 1800).take 450).prod := by
  have h := List.pow_length_le_prod ((recordGapPrimeList.drop 1800).take 450) 15461
    (by decide)
  have len : ((recordGapPrimeList.drop 1800).take 450).length = 450 := by decide
  rwa [len] at h

private theorem chunk5 : 19961 ^ 450 ≤
    ((recordGapPrimeList.drop 2250).take 450).prod := by
  have h := List.pow_length_le_prod ((recordGapPrimeList.drop 2250).take 450) 19961
    (by decide)
  have len : ((recordGapPrimeList.drop 2250).take 450).length = 450 := by decide
  rwa [len] at h

private theorem chunk6 : 24373 ^ 450 ≤
    ((recordGapPrimeList.drop 2700).take 450).prod := by
  have h := List.pow_length_le_prod ((recordGapPrimeList.drop 2700).take 450) 24373
    (by decide)
  have len : ((recordGapPrimeList.drop 2700).take 450).length = 450 := by decide
  rwa [len] at h

private theorem chunk7 : 29021 ^ 450 ≤
    ((recordGapPrimeList.drop 3150).take 450).prod := by
  have h := List.pow_length_le_prod ((recordGapPrimeList.drop 3150).take 450) 29021
    (by decide)
  have len : ((recordGapPrimeList.drop 3150).take 450).length = 450 := by decide
  rwa [len] at h

private theorem chunk8 : 33641 ^ 450 ≤
    ((recordGapPrimeList.drop 3600).take 450).prod := by
  have h := List.pow_length_le_prod ((recordGapPrimeList.drop 3600).take 450) 33641
    (by decide)
  have len : ((recordGapPrimeList.drop 3600).take 450).length = 450 := by decide
  rwa [len] at h

private theorem chunk9 : 38453 ^ 449 ≤
    (recordGapPrimeList.drop 4050).prod := by
  have h := List.pow_length_le_prod (recordGapPrimeList.drop 4050) 38453 (by decide)
  have len : (recordGapPrimeList.drop 4050).length = 449 := by decide
  rwa [len] at h

theorem recordGapLowerProduct_le_tail :
    recordGapLowerProduct ≤ recordGapTailProduct := by
  rw [recordGapLowerProduct, recordGapLowerFactors, recordGapTailProduct]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have split0 := List.prod_take_mul_prod_drop recordGapPrimeList 450
  have split1 := List.prod_take_mul_prod_drop (recordGapPrimeList.drop 450) 450
  have split2 := List.prod_take_mul_prod_drop (recordGapPrimeList.drop 900) 450
  have split3 := List.prod_take_mul_prod_drop (recordGapPrimeList.drop 1350) 450
  have split4 := List.prod_take_mul_prod_drop (recordGapPrimeList.drop 1800) 450
  have split5 := List.prod_take_mul_prod_drop (recordGapPrimeList.drop 2250) 450
  have split6 := List.prod_take_mul_prod_drop (recordGapPrimeList.drop 2700) 450
  have split7 := List.prod_take_mul_prod_drop (recordGapPrimeList.drop 3150) 450
  have split8 := List.prod_take_mul_prod_drop (recordGapPrimeList.drop 3600) 450
  norm_num [List.drop_drop] at split1 split2 split3 split4 split5 split6 split7 split8
  rw [← split0, ← split1, ← split2, ← split3, ← split4,
    ← split5, ← split6, ← split7, ← split8]
  gcongr <;>
    first
    | exact chunk0
    | exact chunk1
    | exact chunk2
    | exact chunk3
    | exact chunk4
    | exact chunk5
    | exact chunk6
    | exact chunk7
    | exact chunk8
    | exact chunk9

end PrimeFactorUnimodality
