/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoJointAnnihilator
import RiemannResearch.RH.QParetoDisplacementResolvent
import RiemannResearch.RH.QParetoCenteredConstant

/-!
# The actual joint-annihilator block and its remaining coupling

Source: Pareto-first research agenda, Priority 5, 11 November 2026.
The two annihilations give zero W--K reciprocal coupling. They give
P-mean zero with all prime tests, and a quantitative bound on the
remaining Q mean. They do not prove Q-mean zero or zero displacement.
-/
noncomputable section
namespace RiemannResearch.RH.QParetoJointBlock
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoEquivalence QParetoJointAnnihilator QParetoMetric
open QParetoDisplacementBounds QParetoDisplacementResolvent
open QParetoClosedProjectionComparison

variable (V : Submodule ℝ ThresholdHilbert) (W : Submodule ℝ QHilbert)
variable [(jointAnnihilator V W).HasOrthogonalProjection]

theorem reciprocal_cross_zero (w : QHilbert) (hw : w ∈ W)
    (k : ThresholdHilbert) (hk : k ∈ jointAnnihilator V W) :
    inner ℝ k (reciprocalD (toPareto w)) = 0 := by
  have hp := Submodule.inner_right_of_mem_orthogonal
    (show toPareto w ∈ W.map toParetoLinear from ⟨w, hw, rfl⟩) hk.2.1
  have hq : inner ℝ w (toQ k) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hw hk.2.2
  have h := inner_identity w (toQ k)
  simp only [metricPairing, toPareto_toQ, hp, hq, mul_zero, zero_add] at h
  rw [← reciprocalD_symmetric, real_inner_comm]
  exact h.symm

theorem project_prime_zero (w : QHilbert) (hw : w ∈ W) :
    (jointAnnihilator V W).starProjection (toPareto w) = 0 := by
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  apply (Submodule.mem_orthogonal _ _).mpr
  intro k hk
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal
    (show toPareto w ∈ W.map toParetoLinear from ⟨w, hw, rfl⟩) hk.2.1

theorem project_reciprocal_prime_zero (w : QHilbert) (hw : w ∈ W) :
    (jointAnnihilator V W).starProjection (reciprocalD (toPareto w)) = 0 := by
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  exact (Submodule.mem_orthogonal _ _).mpr fun k hk => reciprocal_cross_zero V W w hw k hk

variable (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W)
include hW

theorem project_one_zero :
    (jointAnnihilator V W).starProjection hilbertOne = 0 := by
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  apply (Submodule.mem_orthogonal _ _).mpr
  intro k hk
  rw [real_inner_comm]
  exact joint_mean_zero_of_all_primes V W hW k hk

theorem project_pFit_zero [V.HasOrthogonalProjection] :
    (jointAnnihilator V W).starProjection (V.starProjection hilbertOne) = 0 := by
  rw [joint_projection_fit_eq, project_one_zero V W hW]

/-- Centering may be chosen to minimize or certify the remaining reciprocal pairing. -/
theorem qMean_centered (k : ThresholdHilbert) (hk : k ∈ jointAnnihilator V W) (alpha : ℝ) :
    zetaTwo * inner ℝ qOne (toQ k) =
      inner ℝ (reciprocalD hilbertOne - alpha • hilbertOne) k := by
  rw [joint_qMean_identity V W hW k hk, inner_sub_left, real_inner_smul_left,
    joint_mean_zero_of_all_primes V W hW k hk, mul_zero, sub_zero]

theorem qMean_bound (k : ThresholdHilbert) (hk : k ∈ jointAnnihilator V W) (alpha : ℝ) :
    |inner ℝ qOne (toQ k)| ≤
      ‖reciprocalD hilbertOne - alpha • hilbertOne‖ * ‖k‖ / zetaTwo := by
  apply (le_div_iff₀ zetaTwo_pos).mpr
  have h := abs_real_inner_le_norm (reciprocalD hilbertOne - alpha • hilbertOne) k
  rw [← qMean_centered V W hW k hk alpha, abs_mul, abs_of_pos zetaTwo_pos] at h
  simpa only [mul_comm] using h

/-- Universal explicit bound; sharper centered moments can replace the factor 1/2. -/
theorem qMean_bound_half (k : ThresholdHilbert) (hk : k ∈ jointAnnihilator V W) :
    |inner ℝ qOne (toQ k)| ≤ ‖k‖ / (2 * zetaTwo) := by
  have h := qMean_bound V W hW k hk (1 / 2)
  have hn : ‖reciprocalD hilbertOne - (1 / 2 : ℝ) • hilbertOne‖ ≤ (1 / 2 : ℝ) := by
    have he : reciprocalD hilbertOne - (1 / 2 : ℝ) • hilbertOne =
        (-1 / 2 : ℝ) • (hilbertOne - (2 : ℝ) • reciprocalD hilbertOne) := by module
    rw [he, norm_smul, Real.norm_eq_abs]
    norm_num
    have hu : ‖hilbertOne‖ = 1 := by
      nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
    have hc := reflected_reciprocal_norm_le hilbertOne
    rw [hu] at hc
    linarith
  apply h.trans
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hn (norm_nonneg k)) zetaTwo_pos.le
  convert hh using 1 <;> ring


/-- Thirty exact sites plus the complete tail improve 1/2 to sqrt(1/7). -/
theorem qMean_bound_seventh (k : ThresholdHilbert) (hk : k ∈ jointAnnihilator V W) :
    |inner ℝ qOne (toQ k)| ≤ Real.sqrt (1 / 7 : ℝ) * ‖k‖ / zetaTwo := by
  exact (qMean_bound V W hW k hk (2 / 3)).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right QParetoCenteredConstant.centered_constant_norm_le (norm_nonneg k))
      zetaTwo_pos.le)

/-- The Q normal equation compressed onto the actual K, with no free operator premise. -/
theorem actual_qFit_normal
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ V ↔ f ∈ S) :
    (jointAnnihilator V W).starProjection (toPareto (S.starProjection qOne)) +
      (jointAnnihilator V W).starProjection
        (reciprocalD (toPareto (S.starProjection qOne))) =
      (jointAnnihilator V W).starProjection (reciprocalD hilbertOne) := by
  let K := jointAnnihilator V W
  let f := toPareto (S.starProjection qOne)
  have hz : K.starProjection ((hilbertOne - f) + reciprocalD (hilbertOne - f)) = 0 := by
    apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
    apply (Submodule.mem_orthogonal _ _).mpr
    intro k hk
    have hV : k ∈ V := hk.1
    have hmem : toQ k ∈ S := (hsame _).mp (by
      rw [toPareto_toQ]
      exact hV)
    have ho := Submodule.inner_right_of_mem_orthogonal hmem
      (Submodule.sub_starProjection_mem_orthogonal (K := S) qOne)
    have hi := inner_identity (toQ k) (qOne - S.starProjection qOne)
    simp only [metricPairing, toPareto_toQ, toPareto_sub, toPareto_qOne, ho, mul_zero] at hi
    rw [inner_add_right]
    exact hi.symm
  have he : K.starProjection ((hilbertOne - f) + reciprocalD (hilbertOne - f)) =
      K.starProjection (reciprocalD hilbertOne) -
        (K.starProjection f + K.starProjection (reciprocalD f)) := by
    rw [map_add, map_sub, project_one_zero V W hW, map_sub, map_sub]
    abel
  rw [he] at hz
  exact (sub_eq_zero.mp hz).symm

/-- After removing any W component, the entire remaining coupling is explicit. -/
theorem actual_block_equation
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ V ↔ f ∈ S)
    (w : QHilbert) (hw : w ∈ W) :
    let K := jointAnnihilator V W
    let f := toPareto (S.starProjection qOne)
    let k := K.starProjection f
    let u := f - toPareto w - k
    k + K.starProjection (reciprocalD k) =
      K.starProjection (reciprocalD hilbertOne) -
        K.starProjection (reciprocalD u) := by
  dsimp only
  have hn := actual_qFit_normal V W hW S hsame
  simp only [map_sub]
  rw [project_reciprocal_prime_zero V W w hw, sub_zero]
  rw [← hn]
  abel

/-- Stable inversion controls the actual K displacement by the unresolved signed coupling. -/
theorem actual_block_bound
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ V ↔ f ∈ S)
    (w : QHilbert) (hw : w ∈ W) :
    let K := jointAnnihilator V W
    let f := toPareto (S.starProjection qOne)
    let k := K.starProjection f
    let u := f - toPareto w - k
    ‖k‖ ≤ ‖K.starProjection (reciprocalD hilbertOne) -
      K.starProjection (reciprocalD u)‖ := by
  dsimp only
  exact displacement_le_forcing _ _ _ ((jointAnnihilator V W).starProjection_apply_mem _)
    (actual_block_equation V W hW S hsame w hw)

variable [(W.map toParetoLinear).HasOrthogonalProjection]

def middleComponent (f : ThresholdHilbert) : ThresholdHilbert :=
  f - (W.map toParetoLinear).starProjection f -
    (jointAnnihilator V W).starProjection f

def middleSpace : Submodule ℝ ThresholdHilbert :=
  V ⊓ ((W.map toParetoLinear)ᗮ ⊓ (jointAnnihilator V W)ᗮ)

/-- The actual middle component is orthogonal to both the P prime space and K. -/
theorem middleComponent_mem (hWV : W.map toParetoLinear ≤ V)
    (f : ThresholdHilbert) (hf : f ∈ V) :
    middleComponent V W f ∈ middleSpace V W := by
  let P := W.map toParetoLinear
  let K := jointAnnihilator V W
  have hk : K.starProjection f ∈ K := K.starProjection_apply_mem f
  have hwp : P.starProjection f ∈ P := P.starProjection_apply_mem f
  obtain ⟨w, hw, he⟩ := hwp
  have hPK : P.starProjection (K.starProjection f) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hk.2.1
  have hKP : K.starProjection (P.starProjection f) = 0 := by
    rw [← he]
    exact project_prime_zero V W w hw
  refine ⟨V.sub_mem (V.sub_mem hf (hWV (P.starProjection_apply_mem f))) hk.1, ?_, ?_⟩
  · apply (Submodule.starProjection_apply_eq_zero_iff _).mp
    change P.starProjection (f - P.starProjection f - K.starProjection f) = 0
    rw [map_sub, map_sub, Submodule.starProjection_eq_self_iff.mpr
      (P.starProjection_apply_mem f), hPK, sub_self, sub_zero]
  · apply (Submodule.starProjection_apply_eq_zero_iff _).mp
    change K.starProjection (f - P.starProjection f - K.starProjection f) = 0
    rw [map_sub, map_sub, hKP, Submodule.starProjection_eq_self_iff.mpr hk,
      sub_zero, sub_self]

/-- The block equation with the actual orthogonal middle component U. -/
theorem actual_middle_block_equation
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ V ↔ f ∈ S) :
    let f := toPareto (S.starProjection qOne)
    let k := (jointAnnihilator V W).starProjection f
    k + (jointAnnihilator V W).starProjection (reciprocalD k) =
      (jointAnnihilator V W).starProjection (reciprocalD hilbertOne) -
        (jointAnnihilator V W).starProjection (reciprocalD (middleComponent V W f)) := by
  dsimp only
  obtain ⟨w, hw, he⟩ :=
    (W.map toParetoLinear).starProjection_apply_mem (toPareto (S.starProjection qOne))
  have h := actual_block_equation V W hW S hsame w hw
  change toPareto w = _ at he
  simpa only [he, middleComponent] using h

/-- K sees exactly the K component of physical displacement: the P fit contributes zero. -/
theorem actual_K_displacement [V.HasOrthogonalProjection]
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection] :
    (jointAnnihilator V W).starProjection
      (toPareto (S.starProjection qOne) - V.starProjection hilbertOne) =
      (jointAnnihilator V W).starProjection (toPareto (S.starProjection qOne)) := by
  rw [map_sub, project_pFit_zero V W hW, sub_zero]

theorem actual_middle_block_bound
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ V ↔ f ∈ S) :
    let f := toPareto (S.starProjection qOne)
    ‖(jointAnnihilator V W).starProjection f‖ ≤
      ‖(jointAnnihilator V W).starProjection (reciprocalD hilbertOne) -
        (jointAnnihilator V W).starProjection (reciprocalD (middleComponent V W f))‖ := by
  dsimp only
  exact displacement_le_forcing _ _ _ ((jointAnnihilator V W).starProjection_apply_mem _)
    (actual_middle_block_equation V W hW S hsame)


end RiemannResearch.RH.QParetoJointBlock
