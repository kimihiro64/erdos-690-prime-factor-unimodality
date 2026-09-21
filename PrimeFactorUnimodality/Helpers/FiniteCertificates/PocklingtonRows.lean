import PrimeFactorUnimodality.Mathlib.NumberTheory.Pocklington

set_option autoImplicit false

namespace PrimeFactorUnimodality

/-! Numeric Pocklington certificates are kept separate from the row consumers.
The generated layer supplies only this data and checks one reusable validity
predicate per row; the theorem below performs the conversion to primality. -/
structure PocklingtonData where
  n : Nat
  F : Nat
  R : Nat
  a : Nat
  factors : List Nat
  residues : List (Nat × Nat)

def PocklingtonData.residueValid
    (d : PocklingtonData) (r : Nat × Nat) : Bool :=
  decide (r.1 ∈ d.factors ∧
    (((d.a : ZMod d.n) ^ ((d.n - 1) / r.1) - 1) *
      (r.2 : ZMod d.n) = 1))

def PocklingtonData.coverValid (d : PocklingtonData) : Bool :=
  d.factors.all (fun q =>
    d.residues.any (fun r => decide (r.1 = q)))

def PocklingtonData.mainValid (d : PocklingtonData) : Bool :=
  decide (ZMod.val ((d.a : ZMod d.n) ^ (d.n - 1)) = ZMod.val (1 : ZMod d.n))

def PocklingtonData.Valid (d : PocklingtonData) : Prop :=
  1 < d.n ∧
    d.n - 1 = d.F * d.R ∧
    d.F = d.factors.prod ∧
    d.factors.all (fun p => decide p.Prime) = true ∧
    0 < d.F ∧
    d.n < d.F ^ 2 ∧
    d.mainValid = true ∧
    d.residues.all d.residueValid = true ∧
    d.coverValid = true ∧
    ¬ d.F - 1 ∣ d.n

instance (d : PocklingtonData) : Decidable d.Valid := by
  unfold PocklingtonData.Valid
  infer_instance

theorem PocklingtonData.prime
    (d : PocklingtonData) (h : d.Valid) : d.n.Prime := by
  dsimp [PocklingtonData.Valid] at h
  rcases h with
    ⟨hn, hfactor, hF, hfactorPrimesBool, hFpos, hlarge, hmain,
      hresiduesBool, hcoverBool, hexclude⟩
  letI : NeZero d.n := ⟨by omega⟩
  dsimp [PocklingtonData.mainValid] at hmain
  have hmain' : (d.a : ZMod d.n) ^ (d.n - 1) = 1 := by
    apply ZMod.val_injective d.n
    exact of_decide_eq_true hmain
  have hfactorPrimes : ∀ p ∈ d.factors, p.Prime := by
    simp only [List.all_eq_true] at hfactorPrimesBool
    intro p hp
    exact of_decide_eq_true (hfactorPrimesBool p hp)
  have hresidues : ∀ r ∈ d.residues,
      r.1 ∈ d.factors ∧
        (((d.a : ZMod d.n) ^ ((d.n - 1) / r.1) - 1) *
          (r.2 : ZMod d.n) = 1) := by
    simp only [List.all_eq_true] at hresiduesBool
    intro r hrmem
    exact of_decide_eq_true (hresiduesBool r hrmem)
  have hcover : ∀ q ∈ d.factors, ∃ r ∈ d.residues, r.1 = q := by
    simp only [PocklingtonData.coverValid, List.all_eq_true] at hcoverBool
    intro q hq
    obtain ⟨r, hr, heq⟩ := List.any_eq_true.mp (hcoverBool q hq)
    exact ⟨r, hr, of_decide_eq_true heq⟩
  have hproper : ∀ q : Nat, q ∈ d.factors →
      IsUnit ((d.a : ZMod d.n) ^ ((d.n - 1) / q) - 1) := by
    intro q hq
    obtain ⟨r, hr, hrq⟩ := hcover q hq
    have hv := hresidues r hr
    rw [hrq] at hv
    apply IsUnit.of_mul_eq_one (r.2 : ZMod d.n)
    exact hv.2
  apply Nat.prime_of_pocklington_factor_of_prime_factors
    d.n d.F d.R d.a d.factors
  · exact hn
  · exact hfactor
  · exact hF
  · exact hfactorPrimes
  · exact hFpos
  · exact hlarge
  · exact hmain'
  · exact hproper
  · exact hexclude

def PocklingtonRow.Valid (row : List PocklingtonData) : Prop :=
  ∀ d ∈ row, d.Valid

theorem PocklingtonRow.prime_of_mem
    {row : List PocklingtonData} (hrow : PocklingtonRow.Valid row)
    {d : PocklingtonData} (hd : d ∈ row) : d.n.Prime :=
  d.prime (hrow d hd)

/-! A generated shard can validate its whole data list with one closed Boolean computation. -/
theorem PocklingtonRow.valid_of_decide_all
    {row : List PocklingtonData}
    (h : row.all (fun d => decide d.Valid) = true) :
    PocklingtonRow.Valid row := by
  intro d hd
  exact of_decide_eq_true ((List.all_eq_true.mp h) d hd)

private def pocklingtonData3299 : PocklingtonData :=
  { n := 3299, F := 3298, R := 1, a := 2, factors := [2, 17, 97],
    residues := [(2, 1649), (17, 2551), (97, 2776)] }

set_option maxRecDepth 100000 in
private theorem pocklingtonData3299_valid :
    PocklingtonData.Valid pocklingtonData3299 := by
  unfold PocklingtonData.Valid pocklingtonData3299
    PocklingtonData.coverValid PocklingtonData.residueValid
  decide

end PrimeFactorUnimodality
