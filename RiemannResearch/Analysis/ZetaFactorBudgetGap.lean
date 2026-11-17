import RiemannResearch.Analysis.ZetaFactorObstruction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Positive residual floors for bounded finite spectral corrections

Continuation of highest viability RH.pdf, agenda G1-G2 and the diagonal
pair-energy budget:
https://drive.google.com/file/d/1smLPEbJDfOV2Z5mMSMMQvFEd3_qRYopL/view

The analytic obstruction is uniform over each compact coefficient set.
The positive floor is cutoff-dependent and is not a uniform lower bound in x.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ZetaFactorObstruction
variable {ι : Type*} [Fintype ι]

def correctedBlockEnergy (H : ℂ) (F : ℂ → ℂ) (G : ι → ℂ → ℂ)
    (σ a b : ℝ) (c : ι → ℂ) : ℝ :=
  ∫ t in a..b,
    ‖numerator H F (line σ t) +
      ∑ i, c i * (riemannZeta (1-line σ t) * G i (line σ t))‖ ^ 2 /
        (Real.pi * (t ^ 2 + 1/4))

theorem correctedBlockEnergy_continuous (H : ℂ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F) (G : ι → ℂ → ℂ)
    (hG : ∀ i, Differentiable ℂ (G i))
    (σ a b : ℝ) (hσ : 0 < σ) :
    Continuous (correctedBlockEnergy H F G σ a b) := by
  have h0 := numerator_on_line_continuous H F hF σ hσ
  have hg (i : ι) : Continuous
      (fun t => riemannZeta (1-line σ t) * G i (line σ t)) := by
    simpa [numerator] using numerator_on_line_continuous 0 (G i) (hG i) σ hσ
  have hc : Continuous (fun q : (ι → ℂ) × ℝ =>
      numerator H F (line σ q.2) +
        ∑ i, q.1 i * (riemannZeta (1-line σ q.2) * G i (line σ q.2))) :=
    (h0.comp continuous_snd).add
      (continuous_finsetSum _ (fun i _ =>
        ((continuous_apply i).comp continuous_fst).mul ((hg i).comp continuous_snd)))
  unfold correctedBlockEnergy
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hc.norm.pow 2).div
    (continuous_const.mul ((continuous_snd.pow 2).add continuous_const))
    (by intro q; positivity)

theorem compact_correction_minimum_pos (H : ℂ) (hH : H ≠ 0)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (G : ι → ℂ → ℂ)
    (hG : ∀ i, Differentiable ℂ (G i))
    (σ a b : ℝ) (hσ : 0 < σ) (hab : a < b)
    (K : Set (ι → ℂ)) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ c ∈ K, 0 < correctedBlockEnergy H F G σ a b c ∧
      ∀ d ∈ K, correctedBlockEnergy H F G σ a b c ≤
        correctedBlockEnergy H F G σ a b d := by
  obtain ⟨c,hc,hmin⟩ := hK.exists_isMinOn hne
    (correctedBlockEnergy_continuous H F hF G hG σ a b hσ).continuousOn
  exact ⟨c,hc,finite_corrected_block_pos H hH F hF G hG c σ a b hσ hab,
    fun d hd => hmin hd⟩

/-- A fixed finite coefficient budget has a strictly positive residual floor.
The floor depends on the cutoff, columns, interval, and budget. -/
theorem bounded_correction_gap (H : ℂ) (hH : H ≠ 0)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (G : ι → ℂ → ℂ)
    (hG : ∀ i, Differentiable ℂ (G i))
    (σ a b : ℝ) (hσ : 0 < σ) (hab : a < b)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : ι → ℂ, ‖c‖ ≤ R →
      ε ≤ correctedBlockEnergy H F G σ a b c := by
  obtain ⟨c,hc,hpos,hmin⟩ := compact_correction_minimum_pos H hH F hF G hG
    σ a b hσ hab (Metric.closedBall 0 R) (isCompact_closedBall 0 R)
    ⟨0,Metric.mem_closedBall_self hR⟩
  refine ⟨_,hpos,fun d hd => hmin d ?_⟩
  simpa [Metric.mem_closedBall,dist_zero_right] using hd


/-- The paper's diagonal pair weights are at least one. A fixed diagonal
energy budget therefore also has a positive continuous residual floor. -/
theorem diagonal_budget_gap (H : ℂ) (hH : H ≠ 0)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (G : ι → ℂ → ℂ)
    (hG : ∀ i, Differentiable ℂ (G i))
    (σ a b : ℝ) (hσ : 0 < σ) (hab : a < b)
    (d : ι → ℝ) (hd : ∀ i, 1 ≤ d i) (B : ℝ) (hB : 0 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : ι → ℂ, (∑ i, d i * ‖c i‖ ^ 2) ≤ B →
      ε ≤ correctedBlockEnergy H F G σ a b c := by
  obtain ⟨ε,hε,hgap⟩ := bounded_correction_gap H hH F hF G hG σ a b hσ hab
    (Real.sqrt B) (Real.sqrt_nonneg B)
  refine ⟨ε,hε,fun c hc => hgap c ?_⟩
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg B)).mpr
  intro i
  have hi : d i * ‖c i‖ ^ 2 ≤ ∑ j, d j * ‖c j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => mul_nonneg (le_trans (by norm_num) (hd j))
      (sq_nonneg ‖c j‖)) (Finset.mem_univ i)
  have hmul := mul_nonneg (sub_nonneg.mpr (hd i)) (sq_nonneg ‖c i‖)
  have hs := Real.sq_sqrt hB
  have hs0 := Real.sqrt_nonneg B
  nlinarith [norm_nonneg (c i)]

end RiemannResearch.Analysis.ZetaFactorObstruction
