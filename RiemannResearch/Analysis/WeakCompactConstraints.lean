import RiemannResearch.Analysis.CompactConstraintEnergy
import RiemannResearch.Analysis.HilbertWeakCompactness
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Weak and weak-star reconstruction in a common ball

Source: the user's categorical CRT and energy note, 14 November 2026,
Theorem D. These are specializations of compact finite-intersection
reconstruction. Banach--Alaoglu is supplied by Mathlib and, for real Hilbert
spaces, transported through Riesz representation in HilbertWeakCompactness.
The closedness hypotheses concern the actual weak or weak-star topology.
No separability or sequential-compactness hypothesis is used.
For general reflexive spaces, the defining surjectivity of the canonical
bidual inclusion transports Banach--Alaoglu through Mathlib's weak embedding;
see Mathlib.Analysis.Normed.Module.DoubleDual.

The RH consumer is simultaneous reconstruction in a legal correction space:
uniform bounds must hold for the actual finite constrained solutions.
-/

noncomputable section
open Set

namespace CompactConstraintEnergy

variable {I : Type*}

/-- Arbitrarily many weak-star closed constraints have a common solution
in one dual ball exactly when all finite subsystems have such a solution. -/
theorem exists_weakDual_norm_le_iff_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (C : I → Set (WeakDual ℝ E)) (hC : ∀ i, IsClosed (C i)) :
    (∃ f : WeakDual ℝ E, ‖f.toStrongDual‖ ≤ r ∧ ∀ i, f ∈ C i) ↔
      ∀ F : Finset I, ∃ f : WeakDual ℝ E,
        ‖f.toStrongDual‖ ≤ r ∧ ∀ i ∈ F, f ∈ C i := by
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using
    exists_mem_all_iff_finite
      (WeakDual.isCompact_closedBall (0 : StrongDual ℝ E) r) C hC

/-- Hilbert weak reconstruction with exactly the same finite and infinite
norm bound. The index family may be uncountable. -/
theorem exists_weakHilbert_norm_le_iff_finite
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (r : ℝ) (C : I → Set (WeakSpace ℝ H)) (hC : ∀ i, IsClosed (C i)) :
    (∃ v : H, ‖v‖ ≤ r ∧ ∀ i, toWeakSpace ℝ H v ∈ C i) ↔
      ∀ F : Finset I, ∃ v : H,
        ‖v‖ ≤ r ∧ ∀ i ∈ F, toWeakSpace ℝ H v ∈ C i := by
  constructor
  · rintro ⟨v, hv, hvc⟩ F
    exact ⟨v, hv, fun i _ => hvc i⟩
  · intro h
    have hf (F : Finset I) :
        ∃ x ∈ toWeakSpace ℝ H '' Metric.closedBall (0 : H) r,
          ∀ i ∈ F, x ∈ C i := by
      obtain ⟨v, hv, hvc⟩ := h F
      refine ⟨toWeakSpace ℝ H v, ⟨v, ?_, rfl⟩, hvc⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    obtain ⟨x, hx, hxc⟩ := (exists_mem_all_iff_finite
      (RiemannResearch.Analysis.HilbertWeakCompactness.isCompact_closedBall_weak
        (H := H) r) C hC).mpr hf
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v, by simpa only [Metric.mem_closedBall, dist_zero_right] using hv, hxc⟩

/-- Reflexivity is used in its defining form: the canonical bidual inclusion
is onto. This proves weak compactness of balls for general real normed spaces
with that property, with no Hilbert or separability assumption. -/
theorem isCompact_closedBall_weak_of_bidual_surjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (href : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E)) (r : ℝ) :
    IsCompact (toWeakSpace ℝ E '' Metric.closedBall (0 : E) r) := by
  have hn (v : E) : ‖NormedSpace.inclusionInDoubleDual ℝ E v‖ = ‖v‖ :=
    (NormedSpace.inclusionInDoubleDualLi ℝ).norm_map v
  have himage :
      NormedSpace.inclusionInDoubleDualWeak ℝ E ''
        (toWeakSpace ℝ E '' Metric.closedBall (0 : E) r) =
      WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) r := by
    ext z
    constructor
    · rintro ⟨x, ⟨v, hv, rfl⟩, rfl⟩
      change NormedSpace.inclusionInDoubleDual ℝ E v ∈
        Metric.closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) r
      simpa only [Metric.mem_closedBall, dist_zero_right, hn] using hv
    · intro hz
      obtain ⟨v, hv⟩ := href z.toStrongDual
      refine ⟨toWeakSpace ℝ E v, ⟨v, ?_, rfl⟩, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, ← hn, hv]
        simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hz
      · apply WeakDual.toStrongDual.injective
        change NormedSpace.inclusionInDoubleDual ℝ E v = z.toStrongDual
        exact hv
  apply (NormedSpace.isEmbedding_inclusionInDoubleDualWeak ℝ E).isCompact_iff.mpr
  rw [himage]
  exact WeakDual.isCompact_closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) r

/-- Common-ball reconstruction in a reflexive real normed space. The explicit
surjectivity hypothesis is precisely reflexivity, not an added energy bound. -/
theorem exists_weakReflexive_norm_le_iff_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (href : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E))
    (r : ℝ) (C : I → Set (WeakSpace ℝ E)) (hC : ∀ i, IsClosed (C i)) :
    (∃ v : E, ‖v‖ ≤ r ∧ ∀ i, toWeakSpace ℝ E v ∈ C i) ↔
      ∀ F : Finset I, ∃ v : E,
        ‖v‖ ≤ r ∧ ∀ i ∈ F, toWeakSpace ℝ E v ∈ C i := by
  constructor
  · rintro ⟨v, hv, hvc⟩ F
    exact ⟨v, hv, fun i _ => hvc i⟩
  · intro h
    have hf (F : Finset I) :
        ∃ x ∈ toWeakSpace ℝ E '' Metric.closedBall (0 : E) r,
          ∀ i ∈ F, x ∈ C i := by
      obtain ⟨v, hv, hvc⟩ := h F
      refine ⟨toWeakSpace ℝ E v, ⟨v, ?_, rfl⟩, hvc⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    obtain ⟨x, hx, hxc⟩ := (exists_mem_all_iff_finite
      (isCompact_closedBall_weak_of_bidual_surjective href r) C hC).mpr hf
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v, by simpa only [Metric.mem_closedBall, dist_zero_right] using hv, hxc⟩

end CompactConstraintEnergy
