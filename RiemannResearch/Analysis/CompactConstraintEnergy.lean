import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact reconstruction and exact constrained energy

Source: the user's categorical CRT and energy note, 14 November 2026,
Theorems C and D. The proofs use Mathlib's compact finite-intersection theorem.

The energy is extended nonnegative real valued, so infeasible finite or global
systems retain value infinity. The finite supremum includes the empty subsystem.
Only finite sublevels need to be compact. The abstract theorem does not need
Hausdorff separation, since closedness of sublevels is supplied separately by
lower semicontinuity.

RH consumer: compatible arithmetic reconstruction still needs a common finite
energy bound. This module gives the exact compactness implication once that
bound and the closedness of the actual admissible constraints are established.
It supplies no arithmetic bound.
-/

noncomputable section

open Set
open scoped ENNReal

namespace CompactConstraintEnergy

variable {X I : Type*} [TopologicalSpace X]

/-- Closed constraints in a compact set are jointly solvable precisely when
every finite collection is solvable in the same compact set. -/
theorem exists_mem_all_iff_finite {K : Set X} (hK : IsCompact K)
    (C : I → Set X) (hC : ∀ i, IsClosed (C i)) :
    (∃ x ∈ K, ∀ i, x ∈ C i) ↔
      ∀ F : Finset I, ∃ x ∈ K, ∀ i ∈ F, x ∈ C i := by
  constructor
  · rintro ⟨x, hxK, hx⟩ F
    exact ⟨x, hxK, fun i _ => hx i⟩
  · intro h
    obtain ⟨x, hx⟩ := hK.inter_iInter_nonempty C hC (fun F => by
      obtain ⟨x, hxK, hx⟩ := h F
      exact ⟨x, hxK, Set.mem_iInter₂.mpr hx⟩)
    exact ⟨x, hx.1, Set.mem_iInter.mp hx.2⟩

/-- Infimum energy; an empty feasible set has value infinity. -/
def optimum (E : X → ℝ≥0∞) (S : Set X) : ℝ≥0∞ := ⨅ x : S, E x

omit [TopologicalSpace X] in
theorem optimum_le (E : X → ℝ≥0∞) {S : Set X} {x : X} (hx : x ∈ S) :
    optimum E S ≤ E x :=
  iInf_le (fun y : S => E y) ⟨x, hx⟩

/-- Compact sublevels give a minimum on any closed set with finite infimum. -/
theorem exists_minimizer (E : X → ℝ≥0∞) (hE : LowerSemicontinuous E)
    (hcompact : ∀ t : ℝ≥0∞, t < ∞ → IsCompact {x | E x ≤ t})
    {S : Set X} (hS : IsClosed S) (hfinite : optimum E S < ∞) :
    ∃ x ∈ S, E x = optimum E S := by
  classical
  obtain ⟨x₀, hx₀⟩ := iInf_lt_iff.mp hfinite
  let K : Set X := {x | E x ≤ E x₀} ∩ S
  have hK : IsCompact K := (hcompact (E x₀) hx₀).inter_right hS
  let D : S → Set X := fun y => {x | E x ≤ E y}
  have hD (y : S) : IsClosed (D y) := hE.isClosed_preimage (E y)
  have hF (F : Finset S) : ∃ x ∈ K, ∀ y ∈ F, x ∈ D y := by
    induction F using Finset.induction_on with
    | empty =>
        exact ⟨x₀, ⟨show E (x₀ : X) ≤ E x₀ from le_rfl, x₀.property⟩, by simp⟩
    | @insert y F hy ih =>
        obtain ⟨x, hxK, hx⟩ := ih
        by_cases hxy : E y ≤ E x
        · refine ⟨y, ⟨hxy.trans hxK.1, y.property⟩, ?_⟩
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact show E (z : X) ≤ E z from le_rfl
          · exact hxy.trans (hx z hz)
        · refine ⟨x, hxK, ?_⟩
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact le_of_not_ge hxy
          · exact hx z hz
  obtain ⟨x, hxK, hx⟩ := (exists_mem_all_iff_finite hK D hD).mpr hF
  refine ⟨x, hxK.2, le_antisymm ?_ (optimum_le E hxK.2)⟩
  exact le_iInf hx

/-- The feasible set for a finite subsystem, with the empty subsystem allowed. -/
def finiteFeasible (C : I → Set X) (F : Finset I) : Set X :=
  {x | ∀ i ∈ F, x ∈ C i}

/-- The exact finite-subsystem supremum controls a global minimizer. -/
theorem exists_global_minimizer (E : X → ℝ≥0∞) (hE : LowerSemicontinuous E)
    (hcompact : ∀ t : ℝ≥0∞, t < ∞ → IsCompact {x | E x ≤ t})
    (C : I → Set X) (hC : ∀ i, IsClosed (C i))
    (hfinite : (⨆ F : Finset I, optimum E (finiteFeasible C F)) < ∞) :
    ∃ x, (∀ i, x ∈ C i) ∧
      E x = ⨆ F : Finset I, optimum E (finiteFeasible C F) := by
  let M := ⨆ F : Finset I, optimum E (finiteFeasible C F)
  have hF (F : Finset I) : ∃ x ∈ {x | E x ≤ M}, ∀ i ∈ F, x ∈ C i := by
    have hc : IsClosed (finiteFeasible C F) := by
      change IsClosed {x | ∀ i ∈ F, x ∈ C i}
      simp_rw [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => hC i
    have he : optimum E (finiteFeasible C F) ≤ M :=
      le_iSup (fun F => optimum E (finiteFeasible C F)) F
    obtain ⟨x, hx, hxe⟩ := exists_minimizer E hE hcompact hc (he.trans_lt hfinite)
    exact ⟨x, hxe.le.trans he, hx⟩
  obtain ⟨x, hxM, hx⟩ := (exists_mem_all_iff_finite (hcompact M hfinite) C hC).mpr hF
  refine ⟨x, hx, le_antisymm hxM ?_⟩
  exact iSup_le fun F => optimum_le E (fun i _ => hx i)

/-- Exact compactness/energy interchange, including infeasible systems and
infinite energy. The supremum includes the empty finite subsystem. -/
theorem optimum_iInter_eq_iSup_finite (E : X → ℝ≥0∞) (hE : LowerSemicontinuous E)
    (hcompact : ∀ t : ℝ≥0∞, t < ∞ → IsCompact {x | E x ≤ t})
    (C : I → Set X) (hC : ∀ i, IsClosed (C i)) :
    optimum E (⋂ i, C i) = ⨆ F : Finset I, optimum E (finiteFeasible C F) := by
  have hle : (⨆ F : Finset I, optimum E (finiteFeasible C F)) ≤
      optimum E (⋂ i, C i) := by
    apply iSup_le
    intro F
    apply le_iInf
    intro x
    exact optimum_le E (fun i _ => Set.mem_iInter.mp x.property i)
  by_cases hfinite : (⨆ F : Finset I, optimum E (finiteFeasible C F)) < ∞
  · obtain ⟨x, hx, hxe⟩ := exists_global_minimizer E hE hcompact C hC hfinite
    exact le_antisymm ((optimum_le E (Set.mem_iInter.mpr hx)).trans_eq hxe) hle
  · have htop : (⨆ F : Finset I, optimum E (finiteFeasible C F)) = ∞ :=
      top_unique (le_of_not_gt hfinite)
    rw [htop] at hle ⊢
    exact top_unique hle

/-- A finite budget is feasible globally if and only if every finite optimum
is bounded by the same budget. -/
theorem exists_global_le_iff_finite_optimum_le (E : X → ℝ≥0∞)
    (hE : LowerSemicontinuous E)
    (hcompact : ∀ t : ℝ≥0∞, t < ∞ → IsCompact {x | E x ≤ t})
    (C : I → Set X) (hC : ∀ i, IsClosed (C i))
    (M : ℝ≥0∞) (hM : M < ∞) :
    (∃ x, (∀ i, x ∈ C i) ∧ E x ≤ M) ↔
      ∀ F : Finset I, optimum E (finiteFeasible C F) ≤ M := by
  constructor
  · rintro ⟨x, hx, hxM⟩ F
    exact (optimum_le E (S := finiteFeasible C F) (fun i _ => hx i)).trans hxM
  · intro h
    have hs : (⨆ F : Finset I, optimum E (finiteFeasible C F)) ≤ M :=
      iSup_le h
    obtain ⟨x, hx, he⟩ := exists_global_minimizer E hE hcompact C hC (hs.trans_lt hM)
    exact ⟨x, hx, he.le.trans hs⟩

/-- Compact reconstruction for arbitrary continuously observed coordinates.
This works for an uncountable index type. -/
theorem exists_lift_iff_finite [CompactSpace X]
    {Y : I → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
    (q : ∀ i, X → Y i) (hq : ∀ i, Continuous (q i)) (b : ∀ i, Y i) :
    (∃ x, ∀ i, q i x = b i) ↔
      ∀ F : Finset I, ∃ x, ∀ i ∈ F, q i x = b i := by
  have h := exists_mem_all_iff_finite (X := X) isCompact_univ
    (fun i => {x | q i x = b i})
    (fun i => isClosed_eq (hq i) continuous_const)
  simpa only [Set.mem_univ, true_and, Set.mem_ofPred_eq] using h

/-- If binary compatibility solves every finite subsystem, compactness solves
the full compatible system. -/
theorem exists_lift_iff_pairwise [CompactSpace X]
    {Y : I → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, T2Space (Y i)]
    (q : ∀ i, X → Y i) (hq : ∀ i, Continuous (q i)) (b : ∀ i, Y i)
    (hcrt : ∀ F : Finset I,
      (∀ i ∈ F, ∀ j ∈ F, ∃ x, q i x = b i ∧ q j x = b j) →
      ∃ x, ∀ i ∈ F, q i x = b i) :
    (∃ x, ∀ i, q i x = b i) ↔
      ∀ i j, ∃ x, q i x = b i ∧ q j x = b j := by
  constructor
  · rintro ⟨x, hx⟩ i j
    exact ⟨x, hx i, hx j⟩
  · intro h
    exact (exists_lift_iff_finite q hq b).mpr
      (fun F => hcrt F (fun i _ j _ => h i j))


end CompactConstraintEnergy
