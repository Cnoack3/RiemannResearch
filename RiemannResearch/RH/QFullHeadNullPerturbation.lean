/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullHeadRepair
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.Analysis.RightInverseNullPerturbation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Arbitrarily large right inverses for one fixed actual arithmetic head

Source: user-provided `Reciprocal_Head_Investigation_2026-11-07.md`, Section 1.
The free vector is the literal full-conductor arithmetic two-atom direction.
Its first N sites vanish, while its next site is exactly -(N+1). This shows
why exact interpolation alone puts no upper bound on an unspecified choice
of a continuous linear right inverse, even for one fixed head.
-/

noncomputable section
namespace RiemannResearch.RH.QFullHeadNullPerturbation
open ZetaTwoHilbert QFullHeadRepair QFullResidueProjection
open RiemannResearch.Analysis.RightInverseNullPerturbation

def headNull (N : ℕ) : QHilbert :=
  ((N + 1 : ℕ) : ℝ) • qResidue (N + 1) -
    ((N + 2 : ℕ) : ℝ) • qResidue (N + 2)

theorem headNull_mem (N : ℕ) : headNull N ∈ legalSpan :=
  legalSpan.sub_mem
    (legalSpan.smul_mem _ (QFloorDilation.qResidue_mem_legalSpan _ (by omega)))
    (legalSpan.smul_mem _ (QFloorDilation.qResidue_mem_legalSpan _ (by omega)))

theorem headNull_sequence (N n : ℕ) :
    qSequence (headNull N) n =
      ((N + 1 : ℕ) : ℝ) * ArithmeticCumulative.residueFraction (N + 1) n -
        ((N + 2 : ℕ) : ℝ) * ArithmeticCumulative.residueFraction (N + 2) n := by
  change qSequenceLinear (_ - _) n = _
  rw [map_sub, map_smul, map_smul]
  change ((N + 1 : ℕ) : ℝ) * qSequence (qResidue (N + 1)) n -
    ((N + 2 : ℕ) : ℝ) * qSequence (qResidue (N + 2)) n = _
  rw [qSequence_qResidue, qSequence_qResidue]

theorem headNull_head (N n : ℕ) (hn : n ≤ N) : qSequence (headNull N) n = 0 := by
  rw [headNull_sequence]
  unfold ArithmeticCumulative.residueFraction
  rw [Nat.mod_eq_of_lt (by omega : n < N + 1), Nat.mod_eq_of_lt (by omega : n < N + 2)]
  field_simp [show ((N + 1 : ℕ) : ℝ) ≠ 0 by positivity,
    show ((N + 2 : ℕ) : ℝ) ≠ 0 by positivity]
  <;> ring

theorem headNull_next (N : ℕ) :
    qSequence (headNull N) (N + 1) = -((N + 1 : ℕ) : ℝ) := by
  rw [headNull_sequence]
  unfold ArithmeticCumulative.residueFraction
  rw [Nat.mod_self, Nat.mod_eq_of_lt (by omega : N + 1 < N + 2)]
  field_simp [show ((N + 2 : ℕ) : ℝ) ≠ 0 by positivity]
  <;> ring

theorem headNull_ne_zero (N : ℕ) : headNull N ≠ 0 := by
  intro hz
  have h := headNull_next N
  rw [hz] at h
  simp [qSequence] at h
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem headMap_headNull (N : ℕ) : headMap N (headNull N) = 0 := by
  ext i
  rw [headMap_apply]
  have h := headNull_head N (i.val + 1) (by omega)
  simp only [qSequence_succ] at h
  exact (div_eq_zero_iff.mp h).resolve_right
    (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos i.val)))

def perturbedHeadRepair (N : ℕ) (ℓ : (Fin N → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    (Fin N → ℝ) →L[ℝ] QHilbert :=
  perturbation (headRepair N) ℓ (headNull N) t

theorem perturbedHeadRepair_rightInverse (N : ℕ)
    (ℓ : (Fin N → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    Function.RightInverse (perturbedHeadRepair N ℓ t) (headMap N) :=
  perturbation_rightInverse (headMap N) (headRepair N) ℓ (headNull N) t
    (headRepair_rightInverse N) (headMap_headNull N)

theorem perturbedHeadRepair_mem (N : ℕ)
    (ℓ : (Fin N → ℝ) →L[ℝ] ℝ) (t : ℝ) (a : Fin N → ℝ) :
    perturbedHeadRepair N ℓ t a ∈ legalSpan :=
  perturbation_mem legalSpan (headRepair N) ℓ (headNull N) t
    (headRepair_mem N) (headNull_mem N) a

theorem perturbedHeadRepair_energy (N : ℕ)
    (ℓ : (Fin N → ℝ) →L[ℝ] ℝ) (t : ℝ) (a : Fin N → ℝ) :
    ‖perturbedHeadRepair N ℓ t a‖ ^ 2 = ‖headRepair N a‖ ^ 2 +
      2 * (t * ℓ a) * inner ℝ (headRepair N a) (headNull N) +
        (t * ℓ a) ^ 2 * ‖headNull N‖ ^ 2 :=
  perturbation_energy (headRepair N) ℓ (headNull N) t a

/-- A single fixed physical head admits legal continuous right inverses with
arbitrarily large complete operator norms. -/
theorem perturbedHeadRepair_opNorm_unbounded (N : ℕ)
    (ℓ : (Fin N → ℝ) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (C : ℝ) :
    ∃ t : ℝ, C < ‖perturbedHeadRepair N ℓ t‖ :=
  perturbation_opNorm_unbounded (headRepair N) ℓ hℓ (headNull N) (headNull_ne_zero N) C

end RiemannResearch.RH.QFullHeadNullPerturbation
