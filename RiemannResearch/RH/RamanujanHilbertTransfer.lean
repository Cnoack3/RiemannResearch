/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRamanujanPackets
import RiemannResearch.RH.RamanujanPrimeCoordinates
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.Analysis.FiniteGramBasisInvariance
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# Universal residue and dual Ramanujan transfer

Source: user-requested transfer of Pareto/Q results to dual Ramanujan coordinates,
23 October 2026. The arithmetic identities come from QRamanujanPackets; the
sequence-preserving change of measure comes from QParetoEquivalence.

Equality of algebraic spans is the master transfer result. It implies equality
of their closures, orthogonal complements, projections, and every property of
these subspaces in each fixed metric. The observation theorem also transfers
arbitrary affine dual data, without finiteness or independence assumptions.

The change from P to Q preserves topology and physical sequences, but does not
identify their numerical inner products or their orthogonal projections.
Legal moment coordinates retain the ambient orthogonal error term; their
injectivity on the whole ambient space is not asserted.

The projection identities use Mathlib's standard orthogonal projection theory:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Submodule.html
This reference supports the Hilbert-space machinery, not an RH closure claim.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanTransfer
open RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.QRamanujanPackets
open RiemannResearch.RH.ZetaTwoParetoTransfer
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.QParetoEquivalence
open RiemannResearch.RH.RamanujanPrimeCoordinates

/-- Exact algebraic transfer for any positive family closed under divisors above one.
Neither finiteness nor linear independence is required; conductor one may be omitted. -/
theorem q_span_eq (S : Set ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hdiv : ∀ d ∈ S, ∀ q, q ∣ d → 1 < q → q ∈ S) :
    Submodule.span ℝ (qRamanujanPacket '' S) =
      Submodule.span ℝ (qResidue '' S) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    unfold qRamanujanPacket
    apply Submodule.sum_mem
    intro q hq
    apply Submodule.smul_mem
    by_cases hq1 : q = 1
    · simp [hq1]
    · have hqgt : 1 < q := by
        have := Nat.pos_of_mem_divisors hq
        omega
      exact Submodule.subset_span
        ⟨q, hdiv d hd q (Nat.dvd_of_mem_divisors hq) hqgt, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    rw [qResidue_eq_divisor_packets d (hpos d hd)]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro q hq
    by_cases hq1 : q = 1
    · simp [hq1]
    · have hqgt : 1 < q := by
        have := Nat.pos_of_mem_divisors hq
        omega
      exact Submodule.subset_span
        ⟨q, hdiv d hd q (Nat.dvd_of_mem_divisors hq) hqgt, rfl⟩

theorem q_closure_eq (S : Set ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hdiv : ∀ d ∈ S, ∀ q, q ∣ d → 1 < q → q ∈ S) :
    (Submodule.span ℝ (qRamanujanPacket '' S)).topologicalClosure =
      (Submodule.span ℝ (qResidue '' S)).topologicalClosure := by
  rw [q_span_eq S hpos hdiv]

/-- Projections agree within Q because the closed subspaces are exactly equal. -/
theorem q_projection_eq (S : Set ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hdiv : ∀ d ∈ S, ∀ q, q ∣ d → 1 < q → q ∈ S) (f : QHilbert) :
    (Submodule.span ℝ (qRamanujanPacket '' S)).topologicalClosure.starProjection f =
      (Submodule.span ℝ (qResidue '' S)).topologicalClosure.starProjection f := by
  rw [q_span_eq S hpos hdiv]


theorem map_packet_span (S : Set ℕ) :
    (Submodule.span ℝ (qRamanujanPacket '' S)).map paretoEquiv.toLinearMap =
      Submodule.span ℝ (ramanujanPacketHilbert '' S) := by
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d, hd, (toPareto_packet d).symm⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨qRamanujanPacket d, ⟨d, hd, rfl⟩, toPareto_packet d⟩

theorem map_residue_span (S : Set ℕ) (hpos : ∀ d ∈ S, 0 < d) :
    (Submodule.span ℝ (qResidue '' S)).map paretoEquiv.toLinearMap =
      Submodule.span ℝ (BaezDuarte.residueVector '' S) := by
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    exact ⟨d, hd, (toPareto_qResidue d (hpos d hd)).symm⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨qResidue d, ⟨d, hd, rfl⟩, toPareto_qResidue d (hpos d hd)⟩

theorem p_span_eq (S : Set ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hdiv : ∀ d ∈ S, ∀ q, q ∣ d → 1 < q → q ∈ S) :
    Submodule.span ℝ (ramanujanPacketHilbert '' S) =
      Submodule.span ℝ (BaezDuarte.residueVector '' S) := by
  rw [← map_packet_span, q_span_eq S hpos hdiv, map_residue_span S hpos]

/-- Any target and any packet family transfer between Q and Pareto.
The two metrics have equivalent topology, rather than equal numerical norms. -/
theorem packet_closure_transfer (S : Set ℕ) (f : QHilbert) :
    f ∈ (Submodule.span ℝ (qRamanujanPacket '' S)).topologicalClosure ↔
      toPareto f ∈
        (Submodule.span ℝ (ramanujanPacketHilbert '' S)).topologicalClosure := by
  rw [← map_packet_span]
  exact (mem_closure_map_iff _ _).symm

theorem packet_moment (f : QHilbert) (q : ℕ) :
    inner ℝ f (qRamanujanPacket q) =
      ∑ d ∈ q.divisors, ((ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ)) *
        inner ℝ f (qResidue d) := by
  simp only [qRamanujanPacket, inner_sum, real_inner_smul_right]

theorem residue_moment (f : QHilbert) (d : ℕ) (hd : 0 < d) :
    inner ℝ f (qResidue d) =
      (1 / (d : ℝ)) * ∑ q ∈ d.divisors, inner ℝ f (qRamanujanPacket q) := by
  rw [qResidue_eq_divisor_packets d hd]
  simp only [real_inner_smul_right, inner_sum]

/-- All affine dual constraints transfer, for every algebraic linear functional. -/
theorem q_dual_observations_iff (S : Set ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hdiv : ∀ d ∈ S, ∀ q, q ∣ d → 1 < q → q ∈ S)
    (ℓ : QHilbert →ₗ[ℝ] ℝ) (z : QHilbert) :
    (∀ q ∈ S, inner ℝ (qRamanujanPacket q) z = ℓ (qRamanujanPacket q)) ↔
      (∀ d ∈ S, inner ℝ (qResidue d) z = ℓ (qResidue d)) := by
  have hrange (v : ℕ → QHilbert) : Set.range (fun d : S => v d) = v '' S := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, d.property, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
  have hspan : Submodule.span ℝ (Set.range (fun d : S => qRamanujanPacket d)) =
      Submodule.span ℝ (Set.range (fun d : S => qResidue d)) := by
    rw [hrange, hrange, q_span_eq S hpos hdiv]
  have h := RiemannResearch.Analysis.FiniteGramCapacity.observations_iff_of_span_eq
    (fun d : S => qRamanujanPacket d) (fun d : S => qResidue d) ℓ z hspan
  simpa only [Subtype.forall] using h

theorem q_orthogonal_eq (S : Set ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hdiv : ∀ d ∈ S, ∀ q, q ∣ d → 1 < q → q ∈ S) :
    (Submodule.span ℝ (qRamanujanPacket '' S))ᗮ =
      (Submodule.span ℝ (qResidue '' S))ᗮ := by
  rw [q_span_eq S hpos hdiv]

theorem p_closure_eq (S : Set ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hdiv : ∀ d ∈ S, ∀ q, q ∣ d → 1 < q → q ∈ S) :
    (Submodule.span ℝ (ramanujanPacketHilbert '' S)).topologicalClosure =
      (Submodule.span ℝ (BaezDuarte.residueVector '' S)).topologicalClosure := by
  rw [p_span_eq S hpos hdiv]

/-- Master closure transfer: the original Q legal problem is equivalent to
the Pareto Ramanujan problem for every target and divisor-closed family. -/
theorem legal_closure_iff_ramanujan (S : Set ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hdiv : ∀ d ∈ S, ∀ q, q ∣ d → 1 < q → q ∈ S) (f : QHilbert) :
    f ∈ (Submodule.span ℝ (qResidue '' S)).topologicalClosure ↔
      toPareto f ∈
        (Submodule.span ℝ (ramanujanPacketHilbert '' S)).topologicalClosure := by
  rw [← q_span_eq S hpos hdiv]
  exact packet_closure_transfer S f

theorem p_dual_observations_iff (S : Set ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hdiv : ∀ d ∈ S, ∀ q, q ∣ d → 1 < q → q ∈ S)
    (ℓ : ThresholdHilbert →ₗ[ℝ] ℝ) (z : ThresholdHilbert) :
    (∀ q ∈ S, inner ℝ (ramanujanPacketHilbert q) z = ℓ (ramanujanPacketHilbert q)) ↔
      (∀ d ∈ S, inner ℝ (BaezDuarte.residueVector d) z =
        ℓ (BaezDuarte.residueVector d)) := by
  have hrange (v : ℕ → ThresholdHilbert) :
      Set.range (fun d : S => v d) = v '' S := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨d, d.property, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
  have hspan :
      Submodule.span ℝ (Set.range (fun d : S => ramanujanPacketHilbert d)) =
        Submodule.span ℝ (Set.range (fun d : S => BaezDuarte.residueVector d)) := by
    rw [hrange, hrange, p_span_eq S hpos hdiv]
  have h := RiemannResearch.Analysis.FiniteGramCapacity.observations_iff_of_span_eq
    (fun d : S => ramanujanPacketHilbert d)
    (fun d : S => BaezDuarte.residueVector d) ℓ z hspan
  simpa only [Subtype.forall] using h

theorem p_projection_eq (S : Set ℕ) (hpos : ∀ d ∈ S, 0 < d)
    (hdiv : ∀ d ∈ S, ∀ q, q ∣ d → 1 < q → q ∈ S) (f : ThresholdHilbert) :
    (Submodule.span ℝ (ramanujanPacketHilbert '' S)).topologicalClosure.starProjection f =
      (Submodule.span ℝ (BaezDuarte.residueVector '' S)).topologicalClosure.starProjection f := by
  rw [p_span_eq S hpos hdiv]

/-- Legal Ramanujan moments see the orthogonal projection of the target. -/
theorem q_moments_eq_projection (S : Set ℕ) (f : QHilbert) :
    ∀ q ∈ S, inner ℝ (qRamanujanPacket q) f =
      inner ℝ (qRamanujanPacket q)
        ((Submodule.span ℝ (qRamanujanPacket '' S)).topologicalClosure.starProjection f) := by
  let K := (Submodule.span ℝ (qRamanujanPacket '' S)).topologicalClosure
  have ho : f - K.starProjection f ∈ Kᗮ :=
    Submodule.sub_starProjection_mem_orthogonal f
  intro q hq
  have hqK : qRamanujanPacket q ∈ K :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨q, hq, rfl⟩)
  have hh := (K.mem_orthogonal _).mp ho _ hqK
  rw [inner_sub_right] at hh
  exact sub_eq_zero.mp hh

/-- Exact transfer of the approximation error, retaining the full orthogonal
remainder invisible to legal moment observations. -/
theorem q_dual_error_exact (S : Set ℕ) (f v : QHilbert)
    (hv : v ∈ (Submodule.span ℝ (qRamanujanPacket '' S)).topologicalClosure) :
    ‖f - v‖ ^ 2 =
      ‖(Submodule.span ℝ (qRamanujanPacket '' S)).topologicalClosure.starProjection f - v‖ ^ 2 +
        ‖f - (Submodule.span ℝ (qRamanujanPacket '' S)).topologicalClosure.starProjection
          f‖ ^ 2 := by
  let K := (Submodule.span ℝ (qRamanujanPacket '' S)).topologicalClosure
  have ho : f - K.starProjection f ∈ Kᗮ :=
    Submodule.sub_starProjection_mem_orthogonal f
  have hk : K.starProjection f - v ∈ K :=
    K.sub_mem (K.starProjection_apply_mem f) hv
  have hh := (K.mem_orthogonal _).mp ho _ hk
  change ‖f - v‖ ^ 2 = ‖K.starProjection f - v‖ ^ 2 +
    ‖f - K.starProjection f‖ ^ 2
  calc
    ‖f - v‖ ^ 2 =
        ‖(K.starProjection f - v) + (f - K.starProjection f)‖ ^ 2 := by
      congr 1
      congr 1
      abel
    _ = _ := by rw [norm_add_sq_real, hh]; ring

end RiemannResearch.RH.RamanujanTransfer
