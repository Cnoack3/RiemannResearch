/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Complete primitive-penalty regularization

Source: user-provided Squarefree_Primitive_Energy_Regularization_2026-10-17,
Sections 4--6. The standard quadratic method is also described in Albani,
Elbau, de Hoop and Scherzer, https://arxiv.org/abs/1511.02950, introduction.
The existence proof uses Mathlib's Lax--Milgram theorem. These references
support the method; the exact signed identities are derived here.

The concrete RH consumer is `RH.QPrimitiveEnergyClosure`. Both norm-square
remainders and every signed cross term are retained. A positive penalty
supplies existence and uniqueness without any arithmetic density assumption.
-/

noncomputable section
namespace RiemannResearch.Analysis.PrimitiveRegularization
variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Normality in the actual signed primitive and derivative forms. -/
def IsNormal (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E) (e : Y)
    (lam : ℝ) (u : E) : Prop :=
  ∀ h ∈ S, inner ℝ (T u - e) (T h) + lam * inner ℝ u h = 0

/-- Complete objective difference, including both norm-square remainders. -/
theorem objective_completion (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (lam : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hn : IsNormal T S e lam u) :
    ‖T v - e‖ ^ 2 + lam * ‖v‖ ^ 2 =
      ‖T u - e‖ ^ 2 + lam * ‖u‖ ^ 2 +
        ‖T (v-u)‖ ^ 2 + lam * ‖v-u‖ ^ 2 := by
  have h := hn (v-u) (S.sub_mem hv hu)
  have ht : T (v-u) = (T v-e) - (T u-e) := by rw [map_sub]; abel
  rw [ht, inner_sub_right] at h
  rw [inner_sub_right u v u, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at h
  rw [ht, norm_sub_sq_real (T v-e) (T u-e), norm_sub_sq_real v u]
  rw [real_inner_comm (T u-e) (T v-e), real_inner_comm u v]
  nlinarith only [h]

/-- Exact two-parameter primitive-energy identity. -/
theorem energy_difference_exact (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (lam mu : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hnlam : IsNormal T S e lam u) (hnmu : IsNormal T S e mu v) :
    (mu-lam) * (‖u‖ ^ 2 - ‖v‖ ^ 2) =
      2 * ‖T (u-v)‖ ^ 2 + (lam+mu) * ‖u-v‖ ^ 2 := by
  have hlam := objective_completion T S e lam u v hu hv hnlam
  have hmu := objective_completion T S e mu v u hv hu hnmu
  have he : ‖T (v-u)‖ ^ 2 = ‖T (u-v)‖ ^ 2 := by
    rw [← neg_sub u v, map_neg, norm_neg]
  have he' : ‖v-u‖ ^ 2 = ‖u-v‖ ^ 2 := by
    rw [norm_sub_rev]
  rw [he, he'] at hlam
  nlinarith

end RiemannResearch.Analysis.PrimitiveRegularization



namespace RiemannResearch.Analysis.PrimitiveRegularization
variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The normal equation gives a signed formula for the optimized value. -/
theorem objective_at_normal (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (lam : ℝ) (u : E) (hu : u ∈ S)
    (hn : IsNormal T S e lam u) :
    ‖T u - e‖ ^ 2 + lam * ‖u‖ ^ 2 = ‖e‖ ^ 2 - inner ℝ e (T u) := by
  have h := hn u hu
  rw [inner_sub_left, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at h
  rw [norm_sub_sq_real]
  nlinarith [real_inner_comm (T u) e]

/-- Changing the penalty retains the complete signed cross inner product. -/
theorem objective_cross_difference (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (lam mu : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hnlam : IsNormal T S e lam u) (hnmu : IsNormal T S e mu v) :
    (‖T v - e‖ ^ 2 + mu * ‖v‖ ^ 2) -
      (‖T u - e‖ ^ 2 + lam * ‖u‖ ^ 2) =
      (mu - lam) * inner ℝ u v := by
  have h1 := hnlam v hv
  have h2 := hnmu u hu
  rw [inner_sub_left] at h1 h2
  rw [objective_at_normal T S e mu v hv hnmu,
    objective_at_normal T S e lam u hu hnlam]
  rw [real_inner_comm (T u) (T v), real_inner_comm u v] at h2
  nlinarith only [h1, h2]

/-- The complete derivative-error difference. -/
theorem derivative_error_difference_exact
    (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (lam : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hn : IsNormal T S e lam u) :
    ‖T v - e‖ ^ 2 - ‖T u - e‖ ^ 2 =
      lam * (‖u‖ ^ 2 - ‖v‖ ^ 2) +
        ‖T (v-u)‖ ^ 2 + lam * ‖v-u‖ ^ 2 := by
  have h := objective_completion T S e lam u v hu hv hn
  nlinarith

/-- Primitive energy decreases when a positive penalty is increased. -/
theorem energy_antitone (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (lam mu : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hlam : 0 ≤ lam) (hlt : lam < mu)
    (hnlam : IsNormal T S e lam u) (hnmu : IsNormal T S e mu v) :
    ‖v‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have h := energy_difference_exact T S e lam mu u v hu hv hnlam hnmu
  have hp := mul_nonneg (show 0 ≤ lam + mu by linarith) (sq_nonneg ‖u-v‖)
  nlinarith [sq_nonneg ‖T (u-v)‖]

/-- Derivative error increases when a positive penalty is increased. -/
theorem derivative_error_monotone (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (lam mu : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hlam : 0 ≤ lam) (hlt : lam < mu)
    (hnlam : IsNormal T S e lam u) (hnmu : IsNormal T S e mu v) :
    ‖T u-e‖ ^ 2 ≤ ‖T v-e‖ ^ 2 := by
  have he := energy_antitone T S e lam mu u v hu hv hlam hlt hnlam hnmu
  have h := derivative_error_difference_exact T S e lam u v hu hv hnlam
  have hp := mul_nonneg hlam (sub_nonneg.mpr he)
  have hp' := mul_nonneg hlam (sq_nonneg ‖v-u‖)
  nlinarith [sq_nonneg ‖T (v-u)‖]

/-- A positive penalty makes a normal solution the unique minimizer. -/
theorem normal_unique (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (lam : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hlam : 0 < lam) (hnu : IsNormal T S e lam u)
    (hnv : IsNormal T S e lam v) : u = v := by
  have h1 := objective_completion T S e lam u v hu hv hnu
  have h2 := objective_completion T S e lam v u hv hu hnv
  have hp := mul_nonneg hlam.le (sq_nonneg ‖u-v‖)
  have hp' := mul_nonneg hlam.le (sq_nonneg ‖v-u‖)
  have hz : ‖v-u‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖T (v-u)‖, sq_nonneg ‖T (u-v)‖, sq_nonneg ‖v-u‖]
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm

/-- An exact target gives the three-term primitive/error energy identity. -/
theorem exact_target_identity (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (lam : ℝ) (u x : E) (hu : u ∈ S) (hx : x ∈ S)
    (htarget : T x = e) (hn : IsNormal T S e lam u) :
    lam * ‖x‖ ^ 2 = lam * ‖u‖ ^ 2 +
      2 * ‖T u-e‖ ^ 2 + lam * ‖x-u‖ ^ 2 := by
  have h := objective_completion T S e lam u x hu hx hn
  have he : ‖T (x-u)‖ ^ 2 = ‖T u-e‖ ^ 2 := by
    rw [map_sub, htarget, norm_sub_rev]
  rw [htarget, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, he] at h
  linarith

end RiemannResearch.Analysis.PrimitiveRegularization


namespace RiemannResearch.Analysis.PrimitiveRegularization
variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace E] [CompleteSpace Y]

/-- The coercive normal operator for a strictly positive primitive penalty. -/
def penaltyOperator (T : E →L[ℝ] Y) (lam : ℝ) : E →L[ℝ] E :=
  T.adjoint.comp T + lam • ContinuousLinearMap.id ℝ E

def penaltyForm (T : E →L[ℝ] Y) (lam : ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ).comp (penaltyOperator T lam)

theorem penaltyForm_apply (T : E →L[ℝ] Y) (lam : ℝ) (u v : E) :
    penaltyForm T lam u v = inner ℝ (T u) (T v) + lam * inner ℝ u v := by
  change inner ℝ ((T.adjoint) (T u) + lam • u) v = _
  rw [inner_add_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]

theorem penaltyForm_coercive (T : E →L[ℝ] Y) {lam : ℝ} (hlam : 0 < lam) :
    IsCoercive (penaltyForm T lam) := by
  refine ⟨lam, hlam, ?_⟩
  intro u
  rw [penaltyForm_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖T u‖]

/-- Lax--Milgram supplies a normal solution without a range or density assumption. -/
theorem exists_normal (T : E →L[ℝ] Y) (e : Y) {lam : ℝ} (hlam : 0 < lam) :
    ∃ u : E, IsNormal T.toLinearMap ⊤ e lam u := by
  let hB := penaltyForm_coercive T hlam
  obtain ⟨u, hu⟩ := hB.continuousLinearEquivOfBilin.surjective (T.adjoint e)
  refine ⟨u, ?_⟩
  intro w _
  have h := hB.continuousLinearEquivOfBilin_apply u w
  rw [hu, ContinuousLinearMap.adjoint_inner_left, penaltyForm_apply] at h
  change inner ℝ (T u - e) (T w) + lam * inner ℝ u w = 0
  rw [inner_sub_left]
  linarith

theorem exists_unique_normal (T : E →L[ℝ] Y) (e : Y) {lam : ℝ} (hlam : 0 < lam) :
    ∃! u : E, IsNormal T.toLinearMap ⊤ e lam u := by
  obtain ⟨u, hu⟩ := exists_normal T e hlam
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact normal_unique T.toLinearMap ⊤ e lam v u (by simp) (by simp) hlam hv hu

end RiemannResearch.Analysis.PrimitiveRegularization


namespace RiemannResearch.Analysis.PrimitiveRegularization
variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Every normal solution minimizes the complete penalized objective. -/
theorem normal_minimizes (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (lam : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hlam : 0 ≤ lam) (hn : IsNormal T S e lam u) :
    ‖T u - e‖ ^ 2 + lam * ‖u‖ ^ 2 ≤ ‖T v - e‖ ^ 2 + lam * ‖v‖ ^ 2 := by
  have h := objective_completion T S e lam u v hu hv hn
  have hp := mul_nonneg hlam (sq_nonneg ‖v-u‖)
  nlinarith [sq_nonneg ‖T (v-u)‖]

/-- Exact Galerkin Pythagoras in the complete penalty norm. -/
theorem galerkin_identity (T : E →ₗ[ℝ] Y) (S R : Submodule ℝ E)
    (hRS : R ≤ S) (e : Y) (lam : ℝ) (u v w : E)
    (hu : u ∈ S) (hv : v ∈ R) (hw : w ∈ R)
    (hnu : IsNormal T S e lam u) (hnv : IsNormal T R e lam v) :
    ‖T (w-u)‖ ^ 2 + lam * ‖w-u‖ ^ 2 =
      ‖T (v-u)‖ ^ 2 + lam * ‖v-u‖ ^ 2 +
        ‖T (w-v)‖ ^ 2 + lam * ‖w-v‖ ^ 2 := by
  have h1 := objective_completion T S e lam u w hu (hRS hw) hnu
  have h2 := objective_completion T S e lam u v hu (hRS hv) hnu
  have h3 := objective_completion T R e lam v w hv hw hnv
  linarith

variable [CompleteSpace E] [CompleteSpace Y]

/-- A complete Hilbert domain and a positive penalty give a unique minimizer. -/
theorem exists_unique_minimizer (T : E →L[ℝ] Y) (e : Y)
    {lam : ℝ} (hlam : 0 < lam) :
    ∃! u : E, ∀ v : E,
      ‖T u-e‖ ^ 2 + lam * ‖u‖ ^ 2 ≤ ‖T v-e‖ ^ 2 + lam * ‖v‖ ^ 2 := by
  obtain ⟨u, hu⟩ := exists_normal T e hlam
  refine ⟨u, fun v => normal_minimizes T.toLinearMap ⊤ e lam u v
    (by simp) (by simp) hlam.le hu, ?_⟩
  intro v hv
  have hcomp := objective_completion T.toLinearMap ⊤ e lam u v
    (by simp) (by simp) hu
  simp only [ContinuousLinearMap.coe_coe] at hcomp
  have hmin := hv u
  have hz : ‖v-u‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖T (v-u)‖, sq_nonneg ‖v-u‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

end RiemannResearch.Analysis.PrimitiveRegularization

namespace RiemannResearch.Analysis.PrimitiveRegularization
variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The signed correlation with the unpenalized optimizer contains the entire
penalized primitive energy and the derivative-displacement remainder. -/
theorem zero_penalty_cross_identity (T : E →ₗ[ℝ] Y) (S : Submodule ℝ E)
    (e : Y) (lam : ℝ) (u v : E) (hu : u ∈ S) (hv : v ∈ S)
    (hnu : IsNormal T S e 0 u) (hnv : IsNormal T S e lam v) :
    lam * inner ℝ u v = lam * ‖v‖ ^ 2 + ‖T (v-u)‖ ^ 2 := by
  have h1 := objective_completion T S e 0 u v hu hv hnu
  have h2 := objective_cross_difference T S e 0 lam u v hu hv hnu hnv
  simp only [zero_mul, add_zero, sub_zero] at h1 h2
  nlinarith

end RiemannResearch.Analysis.PrimitiveRegularization
