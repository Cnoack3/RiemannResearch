import RiemannResearch.Analysis.ThreePrimeFrequencyMesh
import RiemannResearch.Analysis.ThreePrimeGapParseval
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Topology.DenseEmbedding

/-! # Exact recovery of consecutive displacements from backward prime ratios

For each consecutive prime triple, two circle observations at a common
displacement determine that displacement. The proof uses the dense lattice
of integer multiples of the two logarithmic steps. Exact decoding is a
pointwise fact; continuity of a global decoding operation is not required.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualInfinitePrimeTorus

def orderedPrime (n : ℕ) : Nat.Primes :=
  ⟨Nat.nth Nat.Prime n, Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n⟩

theorem orderedPrime_strictMono : StrictMono (fun n => (orderedPrime n : ℕ)) :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem orderedPrime_bijective : Function.Bijective orderedPrime := by
  constructor
  · intro i j h
    exact orderedPrime_strictMono.injective (congrArg Subtype.val h)
  · intro p
    obtain ⟨n, hn⟩ := Nat.subset_range_nth (p := Nat.Prime) p.property
    exact ⟨n, Subtype.ext hn⟩

theorem orderedPrime_next (n : ℕ) : NextPrime (orderedPrime n) (orderedPrime (n+1)) := by
  refine ⟨orderedPrime_strictMono (Nat.lt_succ_self _), ?_⟩
  intro p hp hlt
  obtain ⟨m,hm⟩ := orderedPrime_bijective.surjective (⟨p,hp⟩ : Nat.Primes)
  have hv : (orderedPrime m : ℕ) = p := congrArg Subtype.val hm
  rw [← hv] at hlt ⊢
  exact orderedPrime_strictMono.monotone (orderedPrime_strictMono.lt_iff_lt.mp hlt)

theorem arbitrarily_large_consecutive_triples (B : ℕ) :
    ∃ p q r : Nat.Primes, B ≤ (p : ℕ) ∧ NextPrime p q ∧ NextPrime q r :=
  ⟨orderedPrime B, orderedPrime (B+1), orderedPrime (B+2),
    orderedPrime_strictMono.id_le B, orderedPrime_next B, orderedPrime_next (B+1)⟩

/-- The circle value x_p(t)/x_q(t), in the user's backward orientation. -/
def backwardPhase (p q : Nat.Primes) (t : ℝ) : Circle := phasePoint t p / phasePoint t q

theorem backwardPhase_eq_exp (p q : Nat.Primes) (t : ℝ) :
    backwardPhase p q t = Circle.exp (-(logPrimeStep p q * t)) := by
  simp only [backwardPhase, phasePoint, ← Circle.exp_sub]
  congr 1
  unfold logPrimeStep
  ring

theorem backwardPhase_sub (p q : Nat.Primes) (u v : ℝ) :
    backwardPhase p q (u-v) = backwardPhase p q u / backwardPhase p q v := by
  simp only [backwardPhase_eq_exp, ← Circle.exp_sub]
  congr 1
  ring

/-- Integer words in just two adjacent backward phase measurements determine
the actual real displacement without a choice of logarithm branch. -/
theorem backwardTriple_injective {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) :
    Function.Injective (fun t : ℝ => (backwardPhase p q t, backwardPhase q r t)) := by
  intro x y heq
  have hstep {p q : Nat.Primes} (h : backwardPhase p q x = backwardPhase p q y) :
      Circle.exp (logPrimeStep p q * x) = Circle.exp (logPrimeStep p q * y) := by
    simp only [backwardPhase_eq_exp, Circle.exp_neg, inv_inj] at h
    exact h
  have h₁ := hstep (congrArg Prod.fst heq)
  have h₂ := hstep (congrArg Prod.snd heq)
  let f := fun ab : ℤ × ℤ => wordFrequency (ratioWord p q ab.1 ++ ratioWord q r ab.2)
  have hh : (fun u : ℝ => Circle.exp (u*x)) = (fun u : ℝ => Circle.exp (u*y)) := by
    apply (threePrimeWordFrequency_dense hpq hqr).equalizer
      (Circle.exp.continuous.comp (continuous_id.mul continuous_const))
      (Circle.exp.continuous.comp (continuous_id.mul continuous_const))
    funext j
    change Circle.exp (f j * x) = Circle.exp (f j * y)
    simp only [f, wordFrequency_append, ratioWord_frequency, add_mul, mul_assoc,
      Circle.exp_add, Circle.exp_intCast_mul, h₁, h₂]
  by_contra hxy
  let u := Real.pi / (x-y)
  have hu : u*x - u*y = Real.pi := by
    rw [← mul_sub, div_mul_cancel₀ _ (sub_ne_zero.mpr hxy)]
  apply Circle.exp_pi_ne_one
  rw [← hu, Circle.exp_sub, congrFun hh u]
  simp

/-- Observing the two phase increments between any two heights determines
their signed difference, including a tie. -/
theorem backward_increments_eq_iff {p q r : Nat.Primes}
    (hpq : (p : ℕ) < q) (hqr : (q : ℕ) < r) (a b c d : ℝ) :
    (backwardPhase p q b / backwardPhase p q a,
      backwardPhase q r b / backwardPhase q r a) =
    (backwardPhase p q d / backwardPhase p q c,
      backwardPhase q r d / backwardPhase q r c) ↔ b-a = d-c := by
  simp only [← backwardPhase_sub]
  exact (backwardTriple_injective hpq hqr).eq_iff

/-- Even if a different consecutive prime triple is used for each gap,
every gap length is determined. -/
theorem all_consecutive_gaps_determined (index : ℕ → ℕ) (s t : ℕ → ℝ) :
    (∀ j, let p := orderedPrime (index j); let q := orderedPrime (index j+1)
          let r := orderedPrime (index j+2)
          (backwardPhase p q (s (j+1))/backwardPhase p q (s j),
            backwardPhase q r (s (j+1))/backwardPhase q r (s j)) =
          (backwardPhase p q (t (j+1))/backwardPhase p q (t j),
            backwardPhase q r (t (j+1))/backwardPhase q r (t j))) ↔
      ∀ j, s (j+1)-s j = t (j+1)-t j := by
  apply forall_congr'
  intro j
  exact backward_increments_eq_iff (orderedPrime_next (index j)).1
    (orderedPrime_next (index j+1)).1 _ _ _ _

end RiemannResearch.Analysis.ActualInfinitePrimeTorus
