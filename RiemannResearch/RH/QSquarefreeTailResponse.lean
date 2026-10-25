/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QShiftedReciprocalTail
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QUniformTail
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Solved squarefree response on directions with zero head

Source: direct Hilbert-space decomposition developed in continuation of the
user's odd-radical projection handoff, 25 October 2026. The estimates apply
after orthogonal projection onto the actual legal directions with zero head.
All norms include the complete infinite tail. The complementary response
still requires an arithmetic estimate; this module does not prove RH.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeTailResponse
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QShiftedReciprocal QFiniteSupportDualCriterion QAnnihilatorTailEscape
open QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.ResidualizedProjectionKernel

/-- Zero on physical sites 1 through H, in the zero-based Hilbert coordinates. -/
def headNull (H : ℕ) : Submodule ℝ QHilbert where
  carrier := {f | ∀ i < H, f i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg i hi
    change f i + g i = 0
    rw [hf i hi, hg i hi, add_zero]
  smul_mem' := by
    intro c f hf i hi
    change c * f i = 0
    rw [hf i hi, mul_zero]

theorem finiteHead_eq_zero_of_mem {H : ℕ} {f : QHilbert}
    (hf : f ∈ headNull H) : finiteHead H f = 0 := by
  apply lp.ext
  funext i
  by_cases hi : i < H
  · rw [finiteHead_apply_of_lt H f i hi]
    exact hf i hi
  · rw [finiteHead_apply_eq_zero H f i (by omega)]
    rfl

theorem B_mem_headNull {H : ℕ} {f : QHilbert} (hf : f ∈ headNull H) :
    B f ∈ headNull H := by
  intro i hi
  rw [B_apply, hf i hi, zero_div]

theorem inner_tail_of_mem (H : ℕ) (f v : QHilbert) (hv : v ∈ headNull H) :
    inner ℝ (tail H f) v = inner ℝ f v := by
  rw [tail, inner_sub_left, finiteHead_inner,
    finiteHead_eq_zero_of_mem hv, inner_zero_right, sub_zero]

theorem physical_zero_of_mem {H : ℕ} {f : QHilbert} (hf : f ∈ headNull H)
    (n : ℕ) (hn : n ≤ H) : qSequence f n = 0 := by
  cases n with
  | zero => rfl
  | succ i => rw [qSequence_succ, hf i (by omega), zero_div]

theorem mem_headNull_of_physical_zero {H : ℕ} {f : QHilbert}
    (hf : ∀ n : ℕ, n ≤ H → qSequence f n = 0) : f ∈ headNull H := by
  intro i hi
  have h := hf (i + 1) (by omega)
  rw [qSequence_succ] at h
  exact (div_eq_zero_iff.mp h).resolve_right
    (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos i)))

/-- Actual legal directions whose first H physical values vanish. -/
def tailStage (N H : ℕ) : Submodule ℝ QHilbert := stage N ⊓ headNull H

instance tailStage_finiteDimensional (N H : ℕ) :
    FiniteDimensional ℝ (tailStage N H) :=
  Submodule.finiteDimensional_of_le (show tailStage N H ≤ stage N from inf_le_left)

def tailResponse (N H : ℕ) : QHilbert :=
  (tailStage N H).starProjection (B (residual N))

def headResponse (N H : ℕ) : QHilbert := movingCorrection N - tailResponse N H

theorem tailResponse_mem (N H : ℕ) : tailResponse N H ∈ tailStage N H :=
  (tailStage N H).starProjection_apply_mem _

theorem tailResponse_zero_on_head (N H n : ℕ) (hn : n ≤ H) :
    qSequence (tailResponse N H) n = 0 :=
  physical_zero_of_mem (tailResponse_mem N H).2 n hn

/-- The exact signed decomposition, before either component is estimated. -/
theorem response_split (N H : ℕ) :
    movingCorrection N = headResponse N H + tailResponse N H := by
  simp [headResponse]

theorem headResponse_mem_stage (N H : ℕ) : headResponse N H ∈ stage N :=
  (stage N).sub_mem ((stage N).starProjection_apply_mem _) (tailResponse_mem N H).1

theorem headResponse_mem_orthogonal (N H : ℕ) :
    headResponse N H ∈ (tailStage N H)ᗮ := by
  have he : (tailStage N H).starProjection (movingCorrection N) = tailResponse N H := by
    have h := Submodule.starProjection_comp_starProjection_of_le
      (show tailStage N H ≤ stage N from inf_le_left)
    exact congrArg (fun T : QHilbert →L[ℝ] QHilbert => T (B (residual N))) h
  rw [headResponse, ← he]
  exact Submodule.sub_starProjection_mem_orthogonal _

theorem response_pythagorean (N H : ℕ) :
    ‖movingCorrection N‖ ^ 2 = ‖headResponse N H‖ ^ 2 + ‖tailResponse N H‖ ^ 2 := by
  have ho := Submodule.inner_right_of_mem_orthogonal
    (tailResponse_mem N H) (headResponse_mem_orthogonal N H)
  rw [real_inner_comm] at ho
  rw [response_split N H, norm_add_sq_real, ho]
  ring

/-- The complementary component has exactly the original response's head. -/
theorem headResponse_agrees (N H n : ℕ) (hn : n ≤ H) :
    qSequence (headResponse N H) n = qSequence (movingCorrection N) n := by
  change qSequenceLinear (movingCorrection N - tailResponse N H) n = _
  rw [map_sub]
  change qSequence (movingCorrection N) n - qSequence (tailResponse N H) n = _
  rw [tailResponse_zero_on_head N H n hn, sub_zero]

/-- Among all actual stage vectors with the specified response head, this
component is the unique minimum-norm extension. The excess square is retained. -/
theorem headResponse_minimum_identity (N H : ℕ) (g : QHilbert)
    (hg : g ∈ stage N)
    (hh : ∀ n : ℕ, n ≤ H → qSequence g n = qSequence (movingCorrection N) n) :
    ‖g‖ ^ 2 = ‖headResponse N H‖ ^ 2 + ‖g - headResponse N H‖ ^ 2 := by
  have ht : g - headResponse N H ∈ tailStage N H := by
    refine ⟨(stage N).sub_mem hg (headResponse_mem_stage N H), ?_⟩
    apply mem_headNull_of_physical_zero
    intro n hn
    change qSequenceLinear (g - headResponse N H) n = 0
    rw [map_sub]
    change qSequence g n - qSequence (headResponse N H) n = 0
    rw [hh n hn, headResponse_agrees N H n hn, sub_self]
  have ho := Submodule.inner_right_of_mem_orthogonal ht (headResponse_mem_orthogonal N H)
  rw [real_inner_comm] at ho
  have he : g = headResponse N H + (g - headResponse N H) := by abel
  conv_lhs => rw [he, norm_add_sq_real, ho]
  ring

/-- Exact centered pairing for the already solved tail response. -/
theorem tailResponse_pairing (N H : ℕ) (a : ℝ) :
    ‖tailResponse N H‖ ^ 2 =
      inner ℝ (tail H (B (tail H (residual N)) - a • tail H (residual N)))
        (tailResponse N H) := by
  let v := tailResponse N H
  have hv : v ∈ tailStage N H := tailResponse_mem N H
  have hr : inner ℝ (residual N) v = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hv.1 (residual_mem_orthogonal N)
  have hp : inner ℝ (B (residual N)) v = ‖v‖ ^ 2 := by
    have ho := Submodule.inner_right_of_mem_orthogonal hv
      (Submodule.sub_starProjection_mem_orthogonal
        (K := tailStage N H) (B (residual N)))
    change inner ℝ v (B (residual N) - v) = 0 at ho
    rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm] at ho
    linarith
  change ‖v‖ ^ 2 = _
  rw [inner_tail_of_mem H _ v hv.2, inner_sub_left, real_inner_smul_left,
    inner_tail_of_mem H _ v hv.2, hr, mul_zero, sub_zero,
    B_symmetric, inner_tail_of_mem H _ (B v) (B_mem_headNull hv.2),
    ← B_symmetric, hp]

/-- Midpoint centering gains the factor two, using the coupled residual's
orthogonality to the actual legal tail subspace. -/
theorem tailResponse_norm_le (N H : ℕ) :
    ‖tailResponse N H‖ ≤
      (1 / (2 * ((H : ℝ) + 2))) * ‖tail H (residual N)‖ := by
  let c : ℝ := 1 / (2 * ((H : ℝ) + 2))
  let w := tail H (B (tail H (residual N)) - c • tail H (residual N))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have he := midpoint_tail_energy_le (tail H (residual N)) H
  have hw : ‖w‖ ≤ c * ‖tail H (residual N)‖ := by
    change ‖w‖ ^ 2 ≤ c ^ 2 * ‖tail H (residual N)‖ ^ 2 at he
    nlinarith [norm_nonneg w, norm_nonneg (tail H (residual N)),
      mul_nonneg hc (norm_nonneg (tail H (residual N)))]
  have hp := tailResponse_pairing N H c
  have hi := real_inner_le_norm w (tailResponse N H)
  change ‖tailResponse N H‖ ^ 2 = inner ℝ w (tailResponse N H) at hp
  have hm := mul_le_mul_of_nonneg_right hw (norm_nonneg (tailResponse N H))
  change ‖tailResponse N H‖ ≤ c * ‖tail H (residual N)‖
  by_cases hz : ‖tailResponse N H‖ = 0
  · rw [hz]
    exact mul_nonneg hc (norm_nonneg _)
  · have hv : 0 < ‖tailResponse N H‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hs : ‖tailResponse N H‖ * ‖tailResponse N H‖ ≤
        (c * ‖tail H (residual N)‖) * ‖tailResponse N H‖ := by
      calc
        ‖tailResponse N H‖ * ‖tailResponse N H‖ = ‖tailResponse N H‖ ^ 2 := by ring
        _ ≤ c * ‖tail H (residual N)‖ * ‖tailResponse N H‖ := hp.le.trans (hi.trans hm)
    by_contra h
    exact (not_lt_of_ge hs) (mul_lt_mul_of_pos_right (lt_of_not_ge h) hv)

theorem tailResponse_physical_bound (N H n : ℕ) :
    |qSequence (tailResponse N H) n| ≤
      Real.sqrt zetaTwo * (n : ℝ) / (2 * ((H : ℝ) + 2)) *
        ‖tail H (residual N)‖ := by
  have hp := QPrimePowerSieve.qSequence_abs_le (tailResponse N H) n
  have hn := mul_le_mul_of_nonneg_left (tailResponse_norm_le N H)
    (show 0 ≤ Real.sqrt zetaTwo * (n : ℝ) by positivity)
  calc
    _ ≤ Real.sqrt zetaTwo * (n : ℝ) * ‖tailResponse N H‖ := by nlinarith [hp]
    _ ≤ Real.sqrt zetaTwo * (n : ℝ) *
        ((1 / (2 * ((H : ℝ) + 2))) * ‖tail H (residual N)‖) := hn
    _ = _ := by ring

theorem tailResponse_window_bound (N H n : ℕ) (A : ℝ)
    (hn : (n : ℝ) ≤ A * ((H : ℝ) + 2)) :
    |qSequence (tailResponse N H) n| ≤
      (Real.sqrt zetaTwo * A / 2) * ‖tail H (residual N)‖ := by
  have hd : 0 < 2 * ((H : ℝ) + 2) := by positivity
  have hratio : Real.sqrt zetaTwo * (n : ℝ) / (2 * ((H : ℝ) + 2)) ≤
      Real.sqrt zetaTwo * A / 2 := by
    apply (div_le_iff₀ hd).mpr
    have ht := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg zetaTwo)
    nlinarith
  exact (tailResponse_physical_bound N H n).trans
    (mul_le_mul_of_nonneg_right hratio (norm_nonneg _))

/-- A whole comparable physical window has uniformly vanishing solved tail
response, with the stage N completely unrestricted. No convergence rate is claimed. -/
theorem tailResponse_uniform_window (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ H₀ : ℕ, ∀ H ≥ H₀, ∀ N n : ℕ,
      (n : ℝ) ≤ A * ((H : ℝ) + 2) →
        |qSequence (tailResponse N H) n| < ε := by
  let D : ℝ := Real.sqrt zetaTwo * A / 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hδ : 0 < ε / (D + 1) := div_pos hε (by positivity)
  obtain ⟨H₀, hH₀⟩ := uniform_tail_tightness_of_tendsto residual limitingResidual
    residual_tendsto (ε / (D + 1)) hδ
  refine ⟨H₀, ?_⟩
  intro H hH N n hn
  have ht := hH₀ H hH N
  have hp := tailResponse_window_bound N H n A hn
  have hm := (mul_lt_mul_of_pos_left ht (show 0 < D + 1 by positivity))
  have he : (D + 1) * (ε / (D + 1)) = ε := by
    field_simp
  rw [he] at hm
  change |qSequence (tailResponse N H) n| ≤ D * ‖tail H (residual N)‖ at hp
  nlinarith [norm_nonneg (tail H (residual N))]

open RiemannResearch.Analysis.ExhaustiveWalk

/-- An active atom, with the original masked-stage indexing. -/
theorem active_qResidue_mem_stage (N : ℕ) (i : Fin N)
    (hi : Squarefree (i.val + 2)) : qResidue (i.val + 2) ∈ stage N := by
  change qResidue (i.val + 2) ∈ walkSpan squarefreeAtom id N
  apply Submodule.subset_span
  refine ⟨i, ?_⟩
  simp [squarefreeAtom, hi, id_eq]

/-- Above H all normalized residue atoms have the same literal head n.
Their differences are actual legal zero-head directions, not independent
formal coefficient vectors. -/
theorem normalized_contrast_mem_tailStage (N H : ℕ) (i j : Fin N)
    (hi : Squarefree (i.val + 2)) (hj : Squarefree (j.val + 2))
    (hHi : H < i.val + 2) (hHj : H < j.val + 2) :
    ((i.val + 2 : ℕ) : ℝ) • qResidue (i.val + 2) -
      ((j.val + 2 : ℕ) : ℝ) • qResidue (j.val + 2) ∈ tailStage N H := by
  refine ⟨(stage N).sub_mem
    ((stage N).smul_mem _ (active_qResidue_mem_stage N i hi))
    ((stage N).smul_mem _ (active_qResidue_mem_stage N j hj)), ?_⟩
  apply mem_headNull_of_physical_zero
  intro n hn
  change qSequenceLinear
    (((i.val + 2 : ℕ) : ℝ) • qResidue (i.val + 2) -
      ((j.val + 2 : ℕ) : ℝ) • qResidue (j.val + 2)) n = 0
  rw [map_sub, map_smul, map_smul]
  change ((i.val + 2 : ℕ) : ℝ) * qSequence (qResidue (i.val + 2)) n -
      ((j.val + 2 : ℕ) : ℝ) * qSequence (qResidue (j.val + 2)) n = 0
  rw [qSequence_qResidue, qSequence_qResidue]
  simp only [ArithmeticCumulative.residueFraction,
    Nat.mod_eq_of_lt (lt_of_le_of_lt hn hHi),
    Nat.mod_eq_of_lt (lt_of_le_of_lt hn hHj)]
  have hi0 : ((i.val + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hj0 : ((j.val + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hi0, hj0] <;> ring

/-- After the legal zero-head response is removed, every remaining high
conductor has the same normalized normal moment. -/
theorem headResponse_normalized_moments_eq (N H : ℕ) (i j : Fin N)
    (hi : Squarefree (i.val + 2)) (hj : Squarefree (j.val + 2))
    (hHi : H < i.val + 2) (hHj : H < j.val + 2) :
    ((i.val + 2 : ℕ) : ℝ) * inner ℝ (qResidue (i.val + 2)) (headResponse N H) =
      ((j.val + 2 : ℕ) : ℝ) * inner ℝ (qResidue (j.val + 2)) (headResponse N H) := by
  have ho := Submodule.inner_right_of_mem_orthogonal
    (normalized_contrast_mem_tailStage N H i j hi hj hHi hHj)
    (headResponse_mem_orthogonal N H)
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left] at ho
  exact sub_eq_zero.mp ho

end RiemannResearch.RH.QSquarefreeTailResponse
