import PrimeCert.Pocklington
import PrimeCert.SieveCorrect

/-! # Pinned multiplicity port and unchanged primality conclusions -/

example {a b n : ℕ} (hn : n ≠ 0) :
    a ≡ b [MOD n] ↔ ∀ p : ℕ, p ∣ n → p.Prime → a ≡ b [MOD p ^ multiplicity p n] :=
  Nat.modEq_iff_forall_prime_dvd hn

example : multiplicity (2 : ℕ) 0 = 0 := by simp

example : ¬ ((0 : ℕ) ≡ 1 [MOD 0] ↔
    ∀ p : ℕ, p ∣ 0 → p.Prime → 0 ≡ 1 [MOD p ^ multiplicity p 0]) := by
  simp [Nat.modEq_zero_iff]
  intro p hp
  exact Nat.modEq_one

example (N F₁ : ℕ) (h2n : 2 ≤ N) (hf₁ : F₁ ∣ N - 1) (hf₁' : N.sqrt < F₁)
    (root : ℕ) (psp : root ^ (N - 1) ≡ 1 [MOD N])
    (primitive : PocklingtonPred N root F₁) : Nat.Prime N :=
  pocklington_certify N F₁ h2n hf₁ hf₁' root psp primitive

example {n sqrtN lit : ℕ} (hEq : PrimeCert.Sieve.sieveK n sqrtN = lit)
    (h3 : n.ble 12884901888) (h5 : n.ble (sqrtN.mul sqrtN)) :
    PrimeCert.Sieve.IsSieve n lit := PrimeCert.Sieve.isSieve_of_sieveK_eq hEq h3 h5
