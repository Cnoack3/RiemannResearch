/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LegalTailCompletedMesh
import RiemannResearch.RH.LegalTailOptimizerLimit
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The capacity endpoint as a continuous complex Nyman projection

Source: Christian Noack, November 2026. Embed the real optimizers in complex
L². Triangular rational rows exhaust the generators, and their orthogonality
passes to the strong limit. Burnol's Theorem 1.2 identifies the target space
and states the additional Hardy-space product formula (https://arxiv.org/abs/math/9910055).
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open RiemannResearch.RH.Burnol.ContinuousNyman

private def meshComplexify : RealMeshHilbert →L[ℝ] Hilbert :=
  Complex.ofRealCLM.compLpL 2 intervalMeasure

private theorem meshComplexify_ae (f : RealMeshHilbert) :
    (meshComplexify f : ℝ → ℂ) =ᵐ[intervalMeasure] fun t => ((f t : ℝ) : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

private theorem meshComplexify_inner (f g : RealMeshHilbert) :
    inner ℂ (meshComplexify f) (meshComplexify g) = ((inner ℝ f g : ℝ) : ℂ) := by
  rw [L2.inner_def,L2.inner_def]
  calc
    _ = ∫ t, ((inner ℝ (f t) (g t) : ℝ) : ℂ) ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [meshComplexify_ae f,meshComplexify_ae g] with t hf hg
      simp [hf,hg,RCLike.inner_apply,mul_comm]
    _ = _ := integral_ofReal

private theorem meshComplexify_gen (α : ℝ) :
    meshComplexify (realMeshGenerator α) = generator α := by
  apply Lp.ext
  filter_upwards [meshComplexify_ae (realMeshGenerator α), realMeshGenerator_ae α,
    generator_ae α] with t hf hr hc
  simp only [hf,hr,hc,generatorFunction]

private theorem meshComplexify_one : meshComplexify realMeshUnit = unitVector := by
  apply Lp.ext
  filter_upwards [meshComplexify_ae realMeshUnit, (memLp_const (μ := intervalMeasure)
    (p := 2) (1 : ℝ)).coeFn_toLp,unitVector_ae] with t hf hr hc
  change (realMeshUnit : ℝ → ℝ) t = 1 at hr
  rw [hf,hr,hc]
  norm_num

private theorem legal_image_mem_complex (K : ℕ) :
    meshComplexify (commonTailOptimizer K) ∈ closedSpace := by
  let S := (closedSpace.restrictScalars ℝ).comap meshComplexify.toLinearMap
  have hc : IsClosed (S : Set RealMeshHilbert) :=
    closedSpace_isClosed.preimage meshComplexify.continuous
  have hle : realStageMesh K ≤ S := by
    apply Submodule.topologicalClosure_minimal _ _ hc
    apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨d,hd,rfl⟩,rfl⟩
    change meshComplexify (realMeshGenerator _) ∈ closedSpace
    rw [meshComplexify_gen]
    apply generator_mem_closedSpace
    have hdR : (0:ℝ) < d := by exact_mod_cast (Nat.succ_pos K).trans hd
    exact ⟨div_pos (by positivity) hdR, (div_lt_one hdR).mpr (by exact_mod_cast hd)⟩
  apply hle
  rw [← realStageMesh_projection]
  exact (realStageMesh K).starProjection_apply_mem _

instance : CompleteSpace closedSpace := closedSpace_isClosed.completeSpace_coe

/-- The limiting discrete projection norm equals the projection norm in Burnol's complex space. -/
theorem normalizedLegalTailMeanCapacity_iSup_eq_nymanProjection :
    (⨆ K, normalizedLegalTailMeanCapacity K) = ‖closedSpace.starProjection unitVector‖^2 := by
  obtain ⟨p,hp,_⟩ := commonTailOptimizer_strong_limit
  have hpC := meshComplexify.continuous.continuousAt.tendsto.comp hp
  have hmem : meshComplexify p ∈ closedSpace :=
    closedSpace_isClosed.mem_of_tendsto hpC (Eventually.of_forall legal_image_mem_complex)
  let r := realMeshUnit - p
  let L := innerSL ℂ (meshComplexify r)
  have horth : closedSpace ≤ L.ker := by
    rw [← triangularMesh_closedSpan]
    apply Submodule.topologicalClosure_minimal _ _ L.isClosed_ker
    apply Submodule.span_le.mpr
    rintro _ ⟨α,hα,rfl⟩
    obtain ⟨N,hN⟩ := mem_iUnion.mp hα
    have he : ∀ᶠ n : ℕ in atTop, inner ℝ
        (realMeshUnit-commonTailOptimizer (n.factorial-1)) (realMeshGenerator α) = 0 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hgen : realMeshGenerator α ∈ realStageMesh (n.factorial-1) := by
        apply Submodule.le_topologicalClosure
        apply Submodule.subset_span
        refine ⟨α,?_,rfl⟩
        rw [Nat.sub_add_cancel (Nat.factorial_pos n)]
        exact triangularMeshRow_subset_factorial n (triangularMeshRow_mono hn hN)
      rw [← realStageMesh_projection]
      exact Submodule.starProjection_inner_eq_zero _ _ hgen
    have hlim : Tendsto (fun n : ℕ => inner ℝ (realMeshUnit-commonTailOptimizer (n.factorial-1))
        (realMeshGenerator α)) atTop (𝓝 (inner ℝ r (realMeshGenerator α))) :=
      (tendsto_const_nhds.sub (hp.comp factorialCutoff_tendsto)).inner tendsto_const_nhds
    have hrzero : inner ℝ r (realMeshGenerator α) = 0 :=
      tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (he.mono fun _ hn => hn.symm))
    change inner ℂ (meshComplexify r) (generator α) = 0
    rw [← meshComplexify_gen,meshComplexify_inner,hrzero]
    norm_num
  have heq : closedSpace.starProjection unitVector = meshComplexify p := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
    intro y hy
    change inner ℂ (unitVector-meshComplexify p) y = 0
    rw [← meshComplexify_one,← map_sub]
    exact horth hy
  rw [heq]
  have hn : Tendsto (fun K => ‖commonTailOptimizer K‖^2) atTop (𝓝 (‖p‖^2)) := hp.norm.pow 2
  have hcap : (⨆ k, normalizedLegalTailMeanCapacity k) = ‖p‖^2 :=
    tendsto_nhds_unique normalizedLegalTailMeanCapacity_tendsto
      (by simpa only [commonTailOptimizer_norm_sq] using hn)
  rw [hcap]
  have hnrm : (fun t => ‖p t‖) =ᵐ[intervalMeasure] (fun t => ‖meshComplexify p t‖) := by
    filter_upwards [meshComplexify_ae p] with t ht
    rw [ht, Complex.norm_real]
  have heLp := eLpNorm_congr_ae (p := 2) hnrm
  simp only [eLpNorm_norm] at heLp
  exact congrArg (fun z : ENNReal => z.toReal^2) heLp

end RiemannResearch.RH.Pareto.PrimePowerSchur
