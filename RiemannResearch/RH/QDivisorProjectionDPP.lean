/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.Analysis.ProjectionDPPKernel
import RiemannResearch.Probability.DeterminantalExistence
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith

/-!
# Projection DPPs in the complete Q divisor-wavelet coordinates

Source: user-provided legal-residue DPP proposal, 14 October 2026.
The existing positive-contraction construction gives an actual Boolean law.
Sites are positive divisor-wavelet labels: site 1 is the constant mode.
The subspace is arbitrary; the legal-residue stages are supplied separately.
No legal closure or RH assertion is needed to construct the probability law.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology Classical
namespace RiemannResearch.RH.QDivisorProjectionDPP
open ZetaTwoHilbert QDivisorHilbert
open RiemannResearch.Analysis.ProjectionDPP
open RiemannResearch.Probability.DPP

variable (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]

@[simp] theorem normalized_one : normalizedDivisorWavelet 1 = qOne := by
  simp [normalizedDivisorWavelet, divisorWavelet_one, qJordanTwo]

def modeKernel (r s : ℕ+) : ℝ := kernel S normalizedDivisorWavelet r s

theorem mode_inner (r s : ℕ+) :
    inner ℝ (normalizedDivisorWavelet r) (normalizedDivisorWavelet s) =
      if r = s then 1 else 0 :=
  (orthonormal_iff_ite.mp normalizedDivisorWavelet_orthonormal) r s

theorem mode_norm_sq (r : ℕ+) : ‖normalizedDivisorWavelet r‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, mode_inner]
  simp

def modeLaw : Measure (ℕ+ → Bool) :=
  contractionDPP (modeKernel S)
    (fun I => principal_posSemidef S normalizedDivisorWavelet (fun i : I => i.1))
    (fun I => by
      have h := identity_sub_principal_posSemidef S normalizedDivisorWavelet
        (fun i : I => i.1) (by intro i j; simp [mode_inner])
      convert h using 1 <;> ext i j <;>
        simp [Matrix.sub_apply, Matrix.one_apply, modeKernel, kernel])

instance modeLaw_probability : IsProbabilityMeasure (modeLaw S) := by
  unfold modeLaw
  exact contractionDPP_probability _ _ _

theorem modeLaw_isDPP :
    IsDPP (modeLaw S) (fun x => {r | x r = true}) (modeKernel S) :=
  contractionDPP_isDPP _ _ _

theorem modeKernel_vacancy_energy (r : ℕ+) :
    1 - modeKernel S r r =
      ‖normalizedDivisorWavelet r - S.starProjection (normalizedDivisorWavelet r)‖ ^ 2 := by
  have h := holeKernel_diagonal S normalizedDivisorWavelet r
  rw [holeKernel_eq, real_inner_self_eq_norm_sq, mode_norm_sq] at h
  exact h

theorem modeLaw_occupation (r : ℕ+) :
    (modeLaw S).real {x | x r = true} = modeKernel S r r :=
  (modeLaw_isDPP S).occupation r

theorem modeLaw_vacancy_energy (r : ℕ+) :
    (modeLaw S).real {x | x r = false} =
      ‖normalizedDivisorWavelet r - S.starProjection (normalizedDivisorWavelet r)‖ ^ 2 := by
  simpa [modeKernel_vacancy_energy] using (modeLaw_isDPP S).vacancy r

theorem constant_occupation :
    (modeLaw S).real {x | x 1 = true} = ‖S.starProjection qOne‖ ^ 2 := by
  rw [modeLaw_occupation, modeKernel, kernel_diagonal, normalized_one]

theorem constant_vacancy :
    (modeLaw S).real {x | x 1 = false} = ‖qOne - S.starProjection qOne‖ ^ 2 := by
  simpa only [normalized_one] using modeLaw_vacancy_energy S 1

theorem constant_occupation_one_iff :
    (modeLaw S).real {x | x 1 = true} = 1 ↔ qOne ∈ S := by
  rw [modeLaw_occupation]
  simpa only [modeKernel, normalized_one] using
    diagonal_one_iff S normalizedDivisorWavelet 1 (mode_norm_sq 1)

theorem modeKernel_diagonal_mono (T : Submodule ℝ QHilbert)
    [T.HasOrthogonalProjection] (hST : S ≤ T) (r : ℕ+) :
    modeKernel S r r ≤ modeKernel T r r := by
  have h := nested_kernel_difference S T hST normalizedDivisorWavelet r r
  rw [real_inner_self_eq_norm_sq] at h
  have hn := sq_nonneg ‖T.starProjection (normalizedDivisorWavelet r) -
    S.starProjection (normalizedDivisorWavelet r)‖
  dsimp [modeKernel]
  linarith

theorem constant_trial_error (F : QHilbert) (hF : F ∈ S) :
    ‖qOne - F‖ ^ 2 = (modeLaw S).real {x | x 1 = false} +
      ‖S.starProjection qOne - F‖ ^ 2 := by
  have ho : inner ℝ (qOne - S.starProjection qOne)
      (S.starProjection qOne - F) = 0 := by
    rw [real_inner_comm]
    exact (S.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal qOne)
      _ (S.sub_mem (S.starProjection_apply_mem qOne) hF)
  have he : qOne - F = (qOne - S.starProjection qOne) +
      (S.starProjection qOne - F) := by abel
  rw [he, norm_add_sq_real, ho, constant_vacancy]
  ring

theorem constant_vacancy_le_trial_error (F : QHilbert) (hF : F ∈ S) :
    (modeLaw S).real {x | x 1 = false} ≤ ‖qOne - F‖ ^ 2 := by
  rw [constant_trial_error S F hF]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.RH.QDivisorProjectionDPP
