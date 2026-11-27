import RiemannResearch.RH.CompositePacketClosure
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Prime.Infinite

/-! # Deleting pure prime-power towers from the packet dictionary

Source: the supplied OtherPrimePacketClosure proof and the mixed-conductor
rank-one splitting. The closure can be classified for every selection that
retains all mixed conductors, even when infinitely many pure towers are removed.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- Complete Pareto closure for the conductors selected by a set. -/
def selectedPacketClosure (A : Set ℕ) : Submodule ℝ ThresholdHilbert :=
  (Submodule.span ℝ (Set.range fun q : {q : ℕ // 1 < q ∧ q ∈ A} =>
    ramanujanPacketHilbert q.val)).topologicalClosure

private theorem packet_mem_selected {A : Set ℕ} {q : ℕ} (hq : 1 < q) (ha : q ∈ A) :
    ramanujanPacketHilbert q ∈ selectedPacketClosure A :=
  Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨⟨q, hq, ha⟩, rfl⟩)

private theorem selected_le {A : Set ℕ} {W : Submodule ℝ ThresholdHilbert}
    (hW : IsClosed (W : Set ThresholdHilbert))
    (h : ∀ q, 1 < q → q ∈ A → ramanujanPacketHilbert q ∈ W) :
    selectedPacketClosure A ≤ W := by
  apply Submodule.topologicalClosure_minimal _ _ hW
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  exact h q.val q.property.1 q.property.2

private theorem mixed_le_selected {A : Set ℕ}
    (hA : ∀ q, 1 < q → ¬IsPrimePow q → q ∈ A) :
    mixedClosure ≤ selectedPacketClosure A := by
  apply Submodule.topologicalClosure_minimal _ _ isClosed_closure
  apply iSup_le
  intro N
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  obtain ⟨hI, hm⟩ := Finset.mem_filter.mp q.property
  have hq : 1 < q.val := lt_of_lt_of_le (by decide : 1 < 2) (Finset.mem_Icc.mp hI).1
  exact packet_mem_selected hq (hA q.val hq hm)

/-- Among dictionaries containing every mixed conductor, one retained prime
power suffices for the full legal closure. Removing all of them gives the
mixed closure. Both assertions are independent of constant membership. -/
theorem selectedPacketClosure_dichotomy (A : Set ℕ)
    (hA : ∀ q, 1 < q → ¬IsPrimePow q → q ∈ A) :
    ((∃ q ∈ A, IsPrimePow q) → selectedPacketClosure A = closedSpace) ∧
    ((¬∃ q ∈ A, IsPrimePow q) → selectedPacketClosure A = mixedClosure) := by
  have hm := mixed_le_selected hA
  constructor
  · rintro ⟨q, hqA, hp⟩
    apply le_antisymm (selected_le isClosed_closure fun n hn _ => packet_mem_closedSpace n hn)
    have hz : inner ℝ (ramanujanPacketHilbert q) hilbertOne ≠ 0 := by
      rw [RiemannResearch.RH.RamanujanCanonicalOptimizer.packet_inner_one]
      exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr hp
    rw [← mixedClosure_sup_span_of_mean_ne_zero (packet_mem_closedSpace q hp.one_lt) hz]
    exact sup_le hm (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (packet_mem_selected hp.one_lt hqA)))
  · intro hn
    refine le_antisymm (selected_le isClosed_closure ?_) hm
    intro q hq hqA
    apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
    refine ⟨packet_mem_closedSpace q hq, ?_⟩
    rw [RiemannResearch.RH.RamanujanCanonicalOptimizer.packet_inner_one]
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr fun hp => hn ⟨q, hqA, hp⟩

/-- All packets with a prime divisor different from p, retaining mixed
conductors divisible by p. -/
def otherPrimePacketClosure (p : ℕ) : Submodule ℝ ThresholdHilbert :=
  selectedPacketClosure {q | ∃ r ∈ q.primeFactors, r ≠ p}

theorem otherPrimePacketClosure_eq_closedSpace (p : ℕ) :
    otherPrimePacketClosure p = closedSpace := by
  apply (selectedPacketClosure_dichotomy _ ?_).1
  · obtain ⟨q, hle, hq⟩ := Nat.exists_infinite_primes (p + 1)
    exact ⟨q, ⟨q, by simp [hq.primeFactors], by omega⟩, hq.isPrimePow⟩
  · intro q hq hpow
    change ∃ r ∈ q.primeFactors, r ≠ p
    by_contra hmiss
    have hsub : q.primeFactors ⊆ {p} := by
      intro r hr
      apply Finset.mem_singleton.mpr
      by_contra hne
      exact hmiss ⟨r, hr, hne⟩
    have hle : q.primeFactors.card ≤ 1 := by simpa using Finset.card_le_card hsub
    have hpos := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hq)
    exact hpow (isPrimePow_iff_card_primeFactors_eq_one.mpr (by omega))

end RiemannResearch.RH.Pareto.PrimePowerSchur
