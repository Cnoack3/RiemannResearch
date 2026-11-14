import RiemannResearch.Logic.EquivalenceRelationCRT
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact gluing with an exact common energy budget

Source: user-provided Categorical_CRT_Exact_Gluing_and_Energy_2026-11-14.md,
Theorems C and D. The proof is the finite-intersection property inside the
specified compact set. Arbitrary index sets are allowed; no sequential
compactness or separability is assumed. The fixed-budget theorem requires
finite feasibility inside that same compact sublevel, not just ambient
algebraic feasibility. It does not assert the full extended-real optimum
identity of Theorem D.
-/

namespace RiemannResearch.Topology.CompactConstraintGluing
variable {ι X : Type*} [TopologicalSpace X]

/-- Arbitrarily many closed constraints glue inside the same compact feasible region. -/
theorem exists_of_finite_constraints (K : Set X) (hK : IsCompact K)
    (C : ι → Set X) (hC : ∀ i, IsClosed (C i))
    (hfin : ∀ F : Finset ι, ∃ x ∈ K, ∀ i ∈ F, x ∈ C i) :
    ∃ x ∈ K, ∀ i, x ∈ C i := by
  have h := hK.inter_iInter_nonempty C hC (fun F => by
    obtain ⟨x, hx, hxc⟩ := hfin F
    refine ⟨x, hx, ?_⟩
    simpa only [Set.mem_iInter] using hxc)
  obtain ⟨x, hx, hxc⟩ := h
  exact ⟨x, hx, by simpa only [Set.mem_iInter] using hxc⟩

/-- Uniform finite feasibility at one energy budget is exactly global feasibility
at that same budget. Compactness is required in the actual energy topology. -/
theorem exists_energy_le_iff {E : Type*} [Preorder E]
    (energy : X → E) (B : E) (hB : IsCompact {x | energy x ≤ B})
    (C : ι → Set X) (hC : ∀ i, IsClosed (C i)) :
    (∃ x, energy x ≤ B ∧ ∀ i, x ∈ C i) ↔
    (∀ F : Finset ι, ∃ x, energy x ≤ B ∧ ∀ i ∈ F, x ∈ C i) := by
  constructor
  · rintro ⟨x, hx, hxc⟩ F
    exact ⟨x, hx, fun i _ => hxc i⟩
  · exact exists_of_finite_constraints {x | energy x ≤ B} hB C hC

/-- Compact completion of finite pointwise reconstruction, with no countability assumption. -/
theorem exists_joint_of_finite [CompactSpace X]
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, T1Space (Y i)]
    (q : ∀ i, X → Y i) (hq : ∀ i, Continuous (q i)) (b : ∀ i, Y i)
    (hfin : ∀ F : Finset ι, ∃ x, ∀ i ∈ F, q i x = b i) :
    ∃ x, ∀ i, q i x = b i := by
  obtain ⟨x, _, hx⟩ := exists_of_finite_constraints Set.univ isCompact_univ
    (fun i => q i ⁻¹' {b i})
    (fun i => isClosed_singleton.preimage (hq i)) (by
      intro F
      obtain ⟨x, hx⟩ := hfin F
      exact ⟨x, Set.mem_univ _, hx⟩)
  exact ⟨x, hx⟩

/-- The relation criterion and compactness together yield arbitrary-family CRT in sets. -/
theorem exists_joint_of_pairwise [CompactSpace X] [Nonempty X]
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, T1Space (Y i)]
    (q : ∀ i, X → Y i) (hq : ∀ i, Continuous (q i))
    (hqs : ∀ i, Function.Surjective (q i))
    (hcrt : RiemannResearch.Logic.FamilyCRT.MeetComposition
      (RiemannResearch.Logic.FamilyCRT.kernelFamily q))
    (b : ∀ i, Y i) (hb : ∀ i j, ∃ x, q i x = b i ∧ q j x = b j) :
    ∃ x, ∀ i, q i x = b i := by
  classical
  apply exists_joint_of_finite q hq b
  intro F
  by_cases hF : F.Nonempty
  · exact RiemannResearch.Logic.FamilyCRT.exists_joint_of_pairwise q hqs
      (RiemannResearch.Logic.FamilyCRT.hereditaryCRT_of_meetComposition _ hcrt)
      F hF b (fun i _ j _ => hb i j)
  · have hFe : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    exact ⟨Classical.arbitrary X, by simp [hFe]⟩

end RiemannResearch.Topology.CompactConstraintGluing
