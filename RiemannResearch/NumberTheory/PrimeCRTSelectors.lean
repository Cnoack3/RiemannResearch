import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Basic
import Lean.Elab.Tactic.Omega

/-!
# Positive finite CRT coordinate selectors

Source: the user's prime-atom independence argument, 2026-11-12.
Mathlib's finite natural-number CRT supplies a representative. A selected
residue equal to one forces that representative to be positive.
-/

namespace RiemannResearch.NumberTheory.PrimeCRTSelectors

/-- A CRT coordinate selector has a positive natural representative. -/
theorem exists_positive_selector {ι : Type*} [Finite ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 2 ≤ m i)
    (hc : Pairwise (fun i j => Nat.Coprime (m i) (m j))) (selected : ι) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, n % m i = if i = selected then 1 else 0 := by
  letI := Fintype.ofFinite ι
  let a : ι → ℕ := fun i => if i = selected then 1 else 0
  have ha (i : ι) : a i < m i := by
    dsimp [a]
    split_ifs <;> have := hm i <;> omega
  obtain ⟨n, hn⟩ := Nat.chineseRemainderOfFinset a m Finset.univ
    (fun i _ => by have := hm i; omega)
    (fun i _ j _ hij => hc hij)
  have hres (i : ι) : n % m i = a i := by
    have h := hn i (Finset.mem_univ i)
    change n % m i = a i % m i at h
    rwa [Nat.mod_eq_of_lt (ha i)] at h
  refine ⟨n, ?_, hres⟩
  by_contra h
  have hz : n = 0 := Nat.eq_zero_of_not_pos h
  have hh := hres selected
  simp [hz, a] at hh

theorem exists_positive_prime_selector {ι : Type*} [Finite ι] [DecidableEq ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (selected : ι) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, n % p i = if i = selected then 1 else 0 := by
  apply exists_positive_selector p (fun i => (hp i).two_le) _ selected
  intro i j hij
  exact (Nat.coprime_primes (hp i) (hp j)).mpr
    (fun h => hij (hinj h))

end RiemannResearch.NumberTheory.PrimeCRTSelectors
