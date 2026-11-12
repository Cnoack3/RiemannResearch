import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Exact D head-tail energies and convergence
Source: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Section 6.2.
The exact identity precedes its bound. The complete tail is never truncated.
The convergence result removes the redundant separate cofinal-head assumption.
Its RH specialization is a conditional reduction: both error limits are open.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QReciprocalHeadTail
open ZetaTwoHilbert QReciprocalMetric QFiniteSupportDualCriterion

theorem norm_sq_eq_D_head_add_completeTail (H : ℕ) (f : QHilbert) :
    ‖f‖ ^ 2 = (∑ n ∈ Finset.range H, ((n : ℝ) + 1) ^ 2 * (D f n) ^ 2) +
      ‖f - finiteHead H f‖ ^ 2 := by
  rw [finiteHead_norm_sq_split H f]
  congr 1
  rw [← real_inner_self_eq_norm_sq, inner_finiteHead_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [finiteHead_apply_of_lt H f n (Finset.mem_range.mp hn), D_apply]
  field_simp

theorem head_norm_sq_le_D (H : ℕ) (f : QHilbert) :
    ‖finiteHead H f‖ ^ 2 ≤ (H : ℝ) ^ 2 * ‖D f‖ ^ 2 := by
  rw [qNorm_sq, qNorm_sq, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _)
    ((qCoordinate_square_summable _).mul_left _)
  intro n
  by_cases hn : n < H
  · rw [finiteHead_apply_of_lt H f n hn, D_apply]
    have hd : (0 : ℝ) < n + 1 := by positivity
    have hdn : (n : ℝ) + 1 ≤ H := by exact_mod_cast (show n + 1 ≤ H by omega)
    have hsq := pow_le_pow_left₀ hd.le hdn 2
    have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (f n / ((n : ℝ)+1)))
    have he : ((n : ℝ)+1) ^ 2 * (f n / ((n : ℝ)+1)) ^ 2 = (f n) ^ 2 := by
      field_simp
    rwa [he] at hmul
  · rw [finiteHead_apply_eq_zero H f n (by omega), zero_pow (by decide)]
    positivity

theorem complete_head_tail_bound (H : ℕ) (f : QHilbert) :
    ‖f‖ ^ 2 ≤ (H : ℝ) ^ 2 * ‖D f‖ ^ 2 + ‖f - finiteHead H f‖ ^ 2 := by
  have he := finiteHead_norm_sq_split H f
  have hh := head_norm_sq_le_D H f
  linarith

theorem tendsto_of_variable_head_tail (F : ℕ → QHilbert) (x : QHilbert)
    (H : ℕ → ℕ)
    (hh : Tendsto (fun j => (H j : ℝ) ^ 2 * ‖D (F j - x)‖ ^ 2) atTop (𝓝 0))
    (ht : Tendsto (fun j => ‖(F j - x) - finiteHead (H j) (F j - x)‖ ^ 2) atTop (𝓝 0)) :
    Tendsto F atTop (𝓝 x) := by
  have hu := hh.add ht
  simp only [zero_add] at hu
  have hs := squeeze_zero (fun j => sq_nonneg ‖F j - x‖)
    (fun j => complete_head_tail_bound (H j) (F j - x)) hu
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

theorem riemannHypothesis_of_variable_D_head_tail
    (F : ℕ → QHilbert) (hm : ∀ j, F j ∈ QFullResidueProjection.closure)
    (H : ℕ → ℕ)
    (hh : Tendsto (fun j => (H j : ℝ) ^ 2 * ‖D (F j - qOne)‖ ^ 2) atTop (𝓝 0))
    (ht : Tendsto (fun j => ‖(F j - qOne) - finiteHead (H j) (F j - qOne)‖ ^ 2)
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  exact QFullResidueProjection.legalSpan.isClosed_topologicalClosure.mem_of_tendsto
    (tendsto_of_variable_head_tail F qOne H hh ht) (Eventually.of_forall hm)

end RiemannResearch.RH.QReciprocalHeadTail
