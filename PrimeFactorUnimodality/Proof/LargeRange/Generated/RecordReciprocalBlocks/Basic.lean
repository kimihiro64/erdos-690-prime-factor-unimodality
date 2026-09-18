import PrimeFactorUnimodality.Helpers.Analytic.PrimeWeightSum

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option linter.style.longLine false

/-! A finite wheel sieve and its interval-composition lemma.  Every prime is
a candidate, so summing over candidates gives a certified upper bound while
avoiding primality reduction at every integer below the cutoff. -/

namespace PrimeFactorUnimodality

def reciprocalCertificateScale : Nat := 1000000000

def roundedReciprocalNumerator (p : Nat) : Nat :=
  reciprocalCertificateScale / p + 1

def reciprocalSievePrimeList : List Nat :=
  [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
    41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
    97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
    157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
    227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
    283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359,
    367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433,
    439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499
  ]

def reciprocalSieveCandidate (n : Nat) : Prop :=
  (n < 500 ∧ n.Prime) ∨
    (499 < n ∧
      reciprocalSievePrimeList.all (fun p => decide (¬p ∣ n)) = true)

instance (n : Nat) : Decidable (reciprocalSieveCandidate n) :=
  by unfold reciprocalSieveCandidate; infer_instance

theorem prime_mem_reciprocalSieveCandidate {p : Nat} (hp : p.Prime) :
    reciprocalSieveCandidate p := by
  by_cases hpSmall : p < 500
  · exact Or.inl ⟨hpSmall, hp⟩
  · right
    refine ⟨by omega, ?_⟩
    rw [List.all_eq_true]
    intro q hq
    rw [decide_eq_true_eq]
    intro hqDvd
    have hqData : 2 ≤ q ∧ q < 500 := by
      simp only [reciprocalSievePrimeList, List.mem_cons,
        List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    rcases (Nat.dvd_prime hp).mp hqDvd with qOne | qEq
    · omega
    · omega

def roundedReciprocalBlockSum (lower upper : Nat) : Nat :=
  ∑ p ∈ (Finset.Ico lower upper).filter reciprocalSieveCandidate,
    roundedReciprocalNumerator p

def roundedReciprocalSieveSumBelow (upper : Nat) : Nat :=
  ∑ p ∈ (Finset.range upper).filter reciprocalSieveCandidate,
    roundedReciprocalNumerator p

theorem roundedReciprocalSieveSumBelow_add_block
    {lower upper : Nat} (h : lower ≤ upper) :
    roundedReciprocalSieveSumBelow upper =
      roundedReciprocalSieveSumBelow lower + roundedReciprocalBlockSum lower upper := by
  rw [roundedReciprocalSieveSumBelow, roundedReciprocalSieveSumBelow,
    roundedReciprocalBlockSum, Finset.range_eq_Ico,
    ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le lower) h,
    Finset.filter_union]
  have intervalsDisjoint :
      Disjoint (Finset.Ico 0 lower) (Finset.Ico lower upper) := by
    rw [Finset.disjoint_left]
    intro p hpLower hpUpper
    simp only [Finset.mem_Ico] at hpLower hpUpper
    omega
  rw [Finset.sum_union (Finset.disjoint_filter_filter intervalsDisjoint)]
  rw [Nat.Ico_zero_eq_range]

theorem roundedReciprocalBlockSum_add_block
    {lower middle upper : Nat} (h₁ : lower ≤ middle) (h₂ : middle ≤ upper) :
    roundedReciprocalBlockSum lower upper =
      roundedReciprocalBlockSum lower middle +
        roundedReciprocalBlockSum middle upper := by
  rw [roundedReciprocalBlockSum, roundedReciprocalBlockSum,
    roundedReciprocalBlockSum,
    ← Finset.Ico_union_Ico_eq_Ico h₁ h₂, Finset.filter_union]
  have intervalsDisjoint :
      Disjoint (Finset.Ico lower middle) (Finset.Ico middle upper) := by
    rw [Finset.disjoint_left]
    intro p hpLower hpUpper
    simp only [Finset.mem_Ico] at hpLower hpUpper
    omega
  rw [Finset.sum_union (Finset.disjoint_filter_filter intervalsDisjoint)]

end PrimeFactorUnimodality
