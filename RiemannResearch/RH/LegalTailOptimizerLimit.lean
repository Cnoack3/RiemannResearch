/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LegalTailReciprocalCell
import Mathlib.Topology.Sequences

/-!
# Exact strong limit of the rescaled legal optimizers

Source: Christian Noack, November 2026. A common multiple compares each pair
of scales. Taking a factorial limit in the exact increment identifies the
error for each fixed scale, without a saturation assumption.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open RiemannResearch.RH.Burnol.ContinuousNyman

private theorem lift_mem {K L h : ℕ} (hh : 0 < h) (hL : L + 1 = h * (K + 1)) :
    dilatedLegalTailMeanVector K h hh ∈ legalHeadKernel L :=
  (legalHeadKernel L).smul_mem _ (legalHeadKernel_dilation hh hL (legalTailMeanVector_mem K))

private theorem legalCellMap_lift {K L h : ℕ} (hh : 0 < h) (hL : L + 1 = h * (K + 1)) :
    legalCellMap L ⟨dilatedLegalTailMeanVector K h hh, lift_mem hh hL⟩ = commonTailOptimizer K := by
  apply Lp.ext
  filter_upwards [reciprocalCellMap_ae L ⟨_,(lift_mem hh hL).2⟩,
    reciprocalCellMap_ae K ⟨_,(legalTailMeanVector_mem K).2⟩,
    ae_restrict_mem (μ := volume) measurableSet_Ioc] with t hl hk ht
  change (reciprocalCellMap L ⟨dilatedLegalTailMeanVector K h hh, (lift_mem hh hL).2⟩ : ℝ → ℝ) t =
    (reciprocalCellMap K ⟨legalTailMeanVector K, (legalTailMeanVector_mem K).2⟩ : ℝ → ℝ) t
  rw [hl,hk]
  have hcast : ((L+1 : ℕ) : ℝ) = (h : ℝ)*((K+1 : ℕ) : ℝ) := by exact_mod_cast hL
  have hfloor : ⌊((L+1 : ℕ) : ℝ)/t⌋₊ / h = ⌊((K+1 : ℕ) : ℝ)/t⌋₊ := by
    rw [← Nat.floor_div_natCast,hcast]
    congr 1
    have hhR : (h : ℝ) ≠ 0 := by positivity
    field_simp [hhR,ht.1.ne']
  simp only [reciprocalCellFunction,dilatedLegalTailMeanVector,hilbertSequence_smul,Pi.smul_apply,
    smul_eq_mul,hilbertDilation_sequence,dilation,hfloor,← mul_assoc,
    inv_mul_cancel₀ (show (h : ℝ) ≠ 0 by positivity), one_mul]

theorem commonTailOptimizer_gain {K L : ℕ} (hdiv : K + 1 ∣ L + 1) :
    ‖commonTailOptimizer L - commonTailOptimizer K‖^2 =
      normalizedLegalTailMeanCapacity L - normalizedLegalTailMeanCapacity K := by
  obtain ⟨h,hh⟩ := hdiv
  have hhpos : 0 < h := by by_contra! hz; simp [show h=0 by omega] at hh
  have hL := hh.trans (Nat.mul_comm _ _)
  let a : legalHeadKernel L := ⟨_,legalTailMeanVector_mem L⟩
  let b : legalHeadKernel L := ⟨_,lift_mem hhpos hL⟩
  have hb : legalCellMap L b = commonTailOptimizer K := legalCellMap_lift hhpos hL
  rw [← hb, normalizedLegalTailMeanCapacity_gain hhpos hL]
  change ‖legalCellMap L a - legalCellMap L b‖ ^ 2 = _
  rw [← map_sub,legalCellMap_norm_sq]
  rfl

private theorem cap_le_sup (K : ℕ) :
    normalizedLegalTailMeanCapacity K ≤ ⨆ k, normalizedLegalTailMeanCapacity k :=
  le_ciSup (show BddAbove (range normalizedLegalTailMeanCapacity) from
    ⟨1, by rintro _ ⟨k,rfl⟩; exact (legalTailMeanCapacity_normalized_bounds k).2⟩) K

/-- Divisibility of successive ordinary integers is unnecessary: compare them at a common stage. -/
theorem commonTailOptimizer_cauchy : CauchySeq commonTailOptimizer := by
  let C := ⨆ k, normalizedLegalTailMeanCapacity k
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have he2 := sq_pos_of_pos (half_pos hε)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp normalizedLegalTailMeanCapacity_tendsto _ he2
  have bound {K L : ℕ} (hK : N ≤ K) (hd : K + 1 ∣ L + 1) :
      dist (commonTailOptimizer L) (commonTailOptimizer K) < ε/2 := by
    have h := hN K hK
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (cap_le_sup K))] at h
    have hdist := commonTailOptimizer_gain hd
    have hsup := cap_le_sup L
    rw [dist_eq_norm]
    nlinarith only [h,hdist,hsup,half_pos hε,
      norm_nonneg (commonTailOptimizer L - commonTailOptimizer K)]
  refine ⟨N, fun i hi j hj => ?_⟩
  let L := (i+1)*(j+1)-1
  have hL : L+1 = (i+1)*(j+1) := Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
  have h₁ := bound (L := L) hi (hL ▸ dvd_mul_right (i+1) (j+1))
  have h₂ := bound (L := L) hj (hL ▸ dvd_mul_left (j+1) (i+1))
  rw [dist_comm] at h₁
  exact (dist_triangle _ (commonTailOptimizer L) _).trans_lt (by linarith)

theorem factorialCutoff_tendsto : Tendsto (fun n : ℕ => n.factorial-1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [eventually_ge_atTop (B+1)] with n hn
  have := Nat.self_le_factorial n
  omega

/-- The error formula holds at each individual stage, with ordinary full-sequence convergence. -/
theorem commonTailOptimizer_strong_limit :
    ∃ p : RealMeshHilbert, Tendsto commonTailOptimizer atTop (𝓝 p) ∧
      ∀ K, ‖p-commonTailOptimizer K‖^2 =
        (⨆ k, normalizedLegalTailMeanCapacity k) - normalizedLegalTailMeanCapacity K := by
  obtain ⟨p,hp⟩ := cauchySeq_tendsto_of_complete commonTailOptimizer_cauchy
  refine ⟨p,hp,fun K => ?_⟩
  have he : (fun n : ℕ => ‖commonTailOptimizer (n.factorial-1)-commonTailOptimizer K‖^2)
      =ᶠ[atTop] (fun n => normalizedLegalTailMeanCapacity (n.factorial-1) -
        normalizedLegalTailMeanCapacity K) := by
    filter_upwards [eventually_ge_atTop (K+1)] with n hn
    apply commonTailOptimizer_gain
    rw [Nat.sub_add_cancel (Nat.factorial_pos n)]
    exact Nat.dvd_factorial (Nat.succ_pos _) hn
  have h₁ := (((hp.comp factorialCutoff_tendsto).sub_const
    (commonTailOptimizer K)).norm.pow 2).congr' he
  exact tendsto_nhds_unique h₁ (normalizedLegalTailMeanCapacity_factorial_tendsto.sub_const _)

theorem commonTailResidual_energy (K : ℕ) :
    ‖realMeshUnit-commonTailOptimizer K‖^2 = tailCapacityDeficit K := by
  let t : TailHeadSpace K := ⟨paretoTail K,paretoTail_mem_headKer K⟩
  let v : TailHeadSpace K := ⟨legalTailMeanVector K,(legalTailMeanVector_mem K).2⟩
  rw [← reciprocalCellMap_tail K]
  change ‖reciprocalCellMap K t - reciprocalCellMap K v‖^2 = _
  rw [← map_sub, reciprocalCellMap_norm_sq, Nat.cast_add, Nat.cast_one]
  exact legalTailResidual_scaled_energy K

private def meshAbs (f : RealMeshHilbert) : RealMeshHilbert :=
  (Lp.memLp f).norm.toLp (fun t => ‖f t‖)

private theorem meshAbs_norm (f : RealMeshHilbert) : ‖meshAbs f‖ = ‖f‖ := by
  rw [meshAbs,Lp.norm_toLp,eLpNorm_norm,Lp.norm_def]

private theorem energy_density_L1_bound (f g : RealMeshHilbert) :
    (∫ t, |f t ^ 2 - g t ^ 2| ∂intervalMeasure) ≤ (‖f‖+‖g‖)*‖f-g‖ := by
  have he : (∫ t, |f t ^ 2 - g t ^ 2| ∂intervalMeasure) =
      inner ℝ (meshAbs (f+g)) (meshAbs (f-g)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [((Lp.memLp (f+g)).norm).coeFn_toLp,((Lp.memLp (f-g)).norm).coeFn_toLp,
      Lp.coeFn_add f g,Lp.coeFn_sub f g] with t ha hb hs hd
    change (meshAbs (f+g) : ℝ → ℝ) t = _ at ha
    change (meshAbs (f-g) : ℝ → ℝ) t = _ at hb
    rw [ha,hb,hs,hd]
    simp only [Pi.add_apply,Pi.sub_apply,Real.norm_eq_abs, RCLike.inner_apply]
    rw [show f t ^ 2 - g t ^ 2 = (f t-g t)*(f t+g t) by ring, abs_mul]
    simp [mul_comm]
  rw [he]
  calc
    _ ≤ ‖meshAbs (f+g)‖ * ‖meshAbs (f-g)‖ := real_inner_le_norm _ _
    _ ≤ _ := by rw [meshAbs_norm,meshAbs_norm]
                exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)

/-- Total variation norm of the common-coordinate energy densities, with the exact scale error. -/
theorem commonTailResidual_energy_variation :
    ∃ p : RealMeshHilbert, Tendsto commonTailOptimizer atTop (𝓝 p) ∧
      let R := realMeshUnit-p
      let C := ⨆ K, normalizedLegalTailMeanCapacity K
      ‖R‖^2 = 1-C ∧ ∀ K,
        (∫ t, |(realMeshUnit-commonTailOptimizer K : RealMeshHilbert) t ^ 2 - R t ^ 2|
          ∂intervalMeasure) ≤
          (Real.sqrt (tailCapacityDeficit K)+Real.sqrt (1-C)) *
          Real.sqrt (C-normalizedLegalTailMeanCapacity K) := by
  obtain ⟨p,hp,he⟩ := commonTailOptimizer_strong_limit
  refine ⟨p,hp,?_⟩
  let R := realMeshUnit - p
  let C := ⨆ K, normalizedLegalTailMeanCapacity K
  have hlim : Tendsto (fun K => ‖realMeshUnit-commonTailOptimizer K‖^2) atTop (𝓝 (‖R‖^2)) :=
    (tendsto_const_nhds.sub hp).norm.pow 2
  have hr : ‖R‖^2 = 1-C := tendsto_nhds_unique hlim
    (by simp only [commonTailResidual_energy]
        exact tendsto_const_nhds.sub normalizedLegalTailMeanCapacity_tendsto)
  refine ⟨hr,fun K => ?_⟩
  change _ ≤ (Real.sqrt (tailCapacityDeficit K) + Real.sqrt (1-C)) * _
  rw [← hr, ← he K, ← commonTailResidual_energy K, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)]
  have h := energy_density_L1_bound (realMeshUnit-commonTailOptimizer K) R
  have hd : realMeshUnit-commonTailOptimizer K - R = p - commonTailOptimizer K := by dsimp [R]; abel
  rwa [hd] at h

end RiemannResearch.RH.Pareto.PrimePowerSchur
