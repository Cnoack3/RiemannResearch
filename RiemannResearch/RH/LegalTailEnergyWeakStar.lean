/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.LegalTailResidual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval

/-!
# Weak-star compactness of the physical legal tail energy

Source: Christian Noack, legal tail-capacity weak-star handoff, November 2026.
The test space is the continuous real functions on the compact interval.
Banach–Alaoglu supplies one compact ball for all the physical energy measures.
Their shrinking supports and exact masses identify the limit of the full sequence.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur

abbrev TailEnergyTest := C(unitInterval, ℝ)

/-- Index `j` is the physical Pareto site `j+1`. -/
def tailEnergySite (j : ℕ) : unitInterval :=
  ⟨1 / ((j : ℝ) + 1), by positivity,
    (div_le_one (by positivity : (0 : ℝ) < (j : ℝ)+1)).mpr
      (by linarith only [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j])⟩

def tailEnergyWeight (K j : ℕ) : ℝ :=
  ((K : ℝ) + 1) * (legalTailResidual K j) ^ 2

theorem tailEnergyWeight_physical (K j : ℕ) :
    tailEnergyWeight K j = ((K : ℝ)+1) * (positiveWeight (j+1) *
      hilbertSequence (legalTailResidual K) (j+1) ^ 2) := by
  rw [hilbertSequence_weighted_square]; rfl

private theorem weight_nonneg (K j : ℕ) : 0 ≤ tailEnergyWeight K j := by
  unfold tailEnergyWeight
  positivity

theorem tailEnergyWeight_head {K j : ℕ} (hj : j < K) : tailEnergyWeight K j = 0 := by
  rw [tailEnergyWeight_physical, legalTailResidual_sequence_head (by omega : j+1 ≤ K)]
  ring

theorem tailEnergyWeight_hasSum (K : ℕ) :
    HasSum (tailEnergyWeight K) (tailCapacityDeficit K) := by
  rw [← legalTailResidual_scaled_energy, hilbert_norm_sq]
  exact (hilbert_coordinate_square_summable _).hasSum.mul_left _

private def energyAtom (K j : ℕ) : StrongDual ℝ TailEnergyTest :=
  tailEnergyWeight K j • ContinuousMap.evalCLM ℝ (tailEnergySite j)

private theorem eval_norm_le (x : unitInterval) :
    ‖(ContinuousMap.evalCLM ℝ x : StrongDual ℝ TailEnergyTest)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using f.norm_coe_le_norm x

private theorem atom_norm_le (K j : ℕ) : ‖energyAtom K j‖ ≤ tailEnergyWeight K j := by
  rw [energyAtom, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg K j)]
  simpa using mul_le_mul_of_nonneg_left (eval_norm_le (tailEnergySite j)) (weight_nonneg K j)

private theorem atoms_summable (K : ℕ) : Summable (energyAtom K) :=
  (tailEnergyWeight_hasSum K).summable.of_norm_bounded (atom_norm_le K)

/-- The actual positive atomic measure, represented by integration against continuous tests. -/
def physicalTailEnergy (K : ℕ) : StrongDual ℝ TailEnergyTest := ∑' j, energyAtom K j

theorem physicalTailEnergy_apply (K : ℕ) (f : TailEnergyTest) :
    physicalTailEnergy K f = ∑' j, tailEnergyWeight K j * f (tailEnergySite j) := by
  let E : (StrongDual ℝ TailEnergyTest) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ f
  exact E.map_tsum (atoms_summable K)

theorem physicalTailEnergy_mass (K : ℕ) :
    physicalTailEnergy K (ContinuousMap.const _ 1) = tailCapacityDeficit K := by
  simpa [physicalTailEnergy_apply] using (tailEnergyWeight_hasSum K).tsum_eq

theorem physicalTailEnergy_norm_le (K : ℕ) : ‖physicalTailEnergy K‖ ≤ tailCapacityDeficit K := by
  have hs := (tailEnergyWeight_hasSum K).summable.of_nonneg_of_le
    (fun j => norm_nonneg (energyAtom K j)) (atom_norm_le K)
  calc
    _ ≤ ∑' j, ‖energyAtom K j‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' j, tailEnergyWeight K j := hs.tsum_le_tsum (atom_norm_le K)
      (tailEnergyWeight_hasSum K).summable
    _ = _ := (tailEnergyWeight_hasSum K).tsum_eq

/-- A single Banach–Alaoglu compact set contains the entire sequence. -/
theorem physicalTailEnergy_weakStar_compact :
    ∃ S : Set (WeakDual ℝ TailEnergyTest), IsCompact S ∧
      ∀ K, (physicalTailEnergy K).toWeakDual ∈ S := by
  refine ⟨WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ TailEnergyTest) 1,
    WeakDual.isCompact_closedBall _ _, ?_⟩
  intro K
  simpa only [Set.mem_preimage, StrongDual.toStrongDual_toWeakDual, Metric.mem_closedBall,
    dist_zero_right] using (physicalTailEnergy_norm_le K).trans (tailCapacityDeficit_bounds K).2

/-- A pointwise modulus on the surviving sites controls the error by the exact mass. -/
theorem physicalTailEnergy_test_error (K : ℕ) (f : TailEnergyTest) {a : ℝ}
    (hf : ∀ j ≥ K, |f (tailEnergySite j) - f 0| ≤ a) :
    |physicalTailEnergy K f - tailCapacityDeficit K * f 0| ≤ tailCapacityDeficit K * a := by
  let w := tailEnergyWeight K
  let g := fun j => w j * (f (tailEnergySite j) - f 0)
  have hb (j : ℕ) : ‖g j‖ ≤ w j * a := by
    change |tailEnergyWeight K j * (f (tailEnergySite j) - f 0)| ≤ tailEnergyWeight K j * a
    rw [abs_mul, abs_of_nonneg (weight_nonneg K j)]
    by_cases h : K ≤ j
    · exact mul_le_mul_of_nonneg_left (hf j h) (weight_nonneg K j)
    · simp [tailEnergyWeight_head (lt_of_not_ge h)]
  have hsum := (tailEnergyWeight_hasSum K).mul_right a
  have hn : Summable (fun j => ‖g j‖) :=
    hsum.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hfSum : HasSum (fun j => w j * f (tailEnergySite j)) (physicalTailEnergy K f) := by
    rw [physicalTailEnergy_apply]
    have h := (tailEnergyWeight_hasSum K).summable.mul_right ‖f‖
    apply Summable.hasSum
    apply h.of_norm_bounded
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_nonneg K j)]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (weight_nonneg K j)
  have hg : HasSum g (physicalTailEnergy K f - tailCapacityDeficit K * f 0) := by
    simpa [g,w,mul_sub] using hfSum.sub ((tailEnergyWeight_hasSum K).mul_right (f 0))
  calc
    _ = ‖∑' j, g j‖ := by rw [hg.tsum_eq, Real.norm_eq_abs]
    _ ≤ ∑' j, ‖g j‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j, w j * a := hn.tsum_le_tsum hb hsum.summable
    _ = _ := hsum.tsum_eq

private theorem site_tendsto : Tendsto tailEnergySite atTop (𝓝 0) := by
  apply tendsto_subtype_rng.mpr
  have h := tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  simpa [tailEnergySite, Function.comp_def, Nat.cast_add, one_div] using
    h.comp (tendsto_add_atTop_nat 1)

def tailEnergyBoundaryAtom (d : ℝ) : WeakDual ℝ TailEnergyTest :=
  StrongDual.toWeakDual
    (d • ContinuousMap.evalCLM ℝ (0 : unitInterval) : StrongDual ℝ TailEnergyTest)

/-- Physical energy converges along every scale to its exact missing-capacity atom at zero. -/
theorem physicalTailEnergy_weakStar_tendsto :
    Tendsto (fun K => (physicalTailEnergy K).toWeakDual) atTop
      (𝓝 (tailEnergyBoundaryAtom (1 - ⨆ K, normalizedLegalTailMeanCapacity K))) := by
  apply tendsto_iff_forall_eval_tendsto_topDualPairing.mpr
  intro f
  change Tendsto (fun K => physicalTailEnergy K f) atTop
    (𝓝 ((1 - ⨆ K, normalizedLegalTailMeanCapacity K) * f 0))
  have hc : Tendsto (fun K => physicalTailEnergy K f - tailCapacityDeficit K * f 0)
      atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have h := f.continuous.continuousAt.tendsto.comp site_tendsto
    obtain ⟨N,hN⟩ := (Metric.tendsto_atTop.mp h) (ε/2) (half_pos hε)
    refine ⟨N, fun K hK => ?_⟩
    rw [Real.dist_eq, sub_zero]
    have hb := physicalTailEnergy_test_error K f (a := ε/2) (fun j hj =>
      (hN j (hK.trans hj)).le)
    exact hb.trans_lt ((mul_le_of_le_one_left (half_pos hε).le
      (tailCapacityDeficit_bounds K).2).trans_lt (half_lt_self hε))
  have hm : Tendsto tailCapacityDeficit atTop (𝓝 (1 - ⨆ K, normalizedLegalTailMeanCapacity K)) :=
    tendsto_const_nhds.sub normalizedLegalTailMeanCapacity_tendsto
  simpa only [sub_add_cancel, zero_add] using hc.add (hm.mul_const (f 0))

theorem physicalTailEnergy_weakStar_zero_iff_RH :
    Tendsto (fun K => (physicalTailEnergy K).toWeakDual) atTop (𝓝 0) ↔ RiemannHypothesis := by
  constructor
  · intro hz
    have he := tendsto_nhds_unique physicalTailEnergy_weakStar_tendsto hz
    have hm := congrArg (fun l : WeakDual ℝ TailEnergyTest => l (ContinuousMap.const _ 1)) he
    change (1 - ⨆ K, normalizedLegalTailMeanCapacity K) * 1 = 0 at hm
    exact normalizedLegalTailMeanCapacity_iSup_eq_one_iff_RH.mp (by linarith)
  · intro hRH
    have h := normalizedLegalTailMeanCapacity_iSup_eq_one_iff_RH.mpr hRH
    simpa [h,tailEnergyBoundaryAtom] using physicalTailEnergy_weakStar_tendsto

/-- Piecewise-linear triangular hat at node i/N on the physical unit interval. -/
def tailMeshHat (N i : ℕ) : TailEnergyTest :=
  ⟨fun x => max (1 - |(N : ℝ) * (x : ℝ) - i|) 0, by fun_prop⟩

private theorem hats_first_cell (N : ℕ) (x : unitInterval) (hx : (N : ℝ)*(x : ℝ) ≤ 1) :
    tailMeshHat N 0 x = 1-(N : ℝ)*(x : ℝ) ∧
    tailMeshHat N 1 x = (N : ℝ)*(x : ℝ) ∧
    ∀ i : ℕ, 2 ≤ i → tailMeshHat N i x = 0 := by
  let y := (N : ℝ)*(x : ℝ)
  have hy : 0 ≤ y := mul_nonneg (Nat.cast_nonneg _) x.property.1
  change y ≤ 1 at hx
  refine ⟨?_, ?_, ?_⟩
  · change max (1 - |y - ((0 : ℕ) : ℝ)|) 0 = 1-y
    simpa only [Nat.cast_zero,sub_zero,abs_of_nonneg hy] using
      (max_eq_left (sub_nonneg.mpr hx) : max (1-y) 0 = 1-y)
  · change max (1 - |y - ((1 : ℕ) : ℝ)|) 0 = y
    rw [Nat.cast_one,abs_of_nonpos (sub_nonpos.mpr hx),show 1 - -(y-1) = y by ring,max_eq_left hy]
  · intro i hi
    have hiR : (2 : ℝ) ≤ i := by exact_mod_cast hi
    change max (1 - |y-i|) 0 = 0
    rw [abs_of_nonpos (by linarith : y-(i : ℝ) ≤ 0), max_eq_right (by linarith)]

private theorem mesh_site_in_first_cell {N K j : ℕ} (hN : N ≤ K + 1) (hj : K ≤ j) :
    (N : ℝ) * (tailEnergySite j : ℝ) ≤ 1 := by
  change (N : ℝ) * (1/((j : ℝ)+1)) ≤ 1
  rw [mul_one_div, div_le_one (by positivity)]
  exact_mod_cast (show N ≤ j+1 by omega)

/-- From node two onwards all hats vanish once the support lies in the first cell. -/
theorem physicalTailEnergy_hat_vanish {N K i : ℕ} (hN : N ≤ K + 1) (hi : 2 ≤ i) :
    physicalTailEnergy K (tailMeshHat N i) = 0 := by
  rw [physicalTailEnergy_apply]
  have hz (j : ℕ) : tailEnergyWeight K j * tailMeshHat N i (tailEnergySite j) = 0 := by
    by_cases hj : K ≤ j
    · rw [(hats_first_cell N _ (mesh_site_in_first_cell hN hj)).2.2 i hi, mul_zero]
    · rw [tailEnergyWeight_head (lt_of_not_ge hj),zero_mul]
  simp only [hz,tsum_zero]

/-- The two surviving hat coefficients sum to exactly the finite-stage deficit. -/
theorem physicalTailEnergy_first_hat_pair {N K : ℕ} (hN : N ≤ K + 1) :
    physicalTailEnergy K (tailMeshHat N 0) + physicalTailEnergy K (tailMeshHat N 1) =
      tailCapacityDeficit K := by
  let f := tailMeshHat N 0 + tailMeshHat N 1
  have h0 : f 0 = 1 := by simp [f,tailMeshHat]
  have h := physicalTailEnergy_test_error K f (a := 0) (fun j hj => by
    obtain ⟨ha,hb,_⟩ := hats_first_cell N _ (mesh_site_in_first_cell hN hj)
    change |tailMeshHat N 0 (tailEnergySite j) + tailMeshHat N 1 (tailEnergySite j) - f 0| ≤ 0
    rw [ha,hb,h0]; simp)
  rw [h0,mul_one,mul_zero,abs_nonpos_iff,sub_eq_zero] at h
  simpa [f] using h

/-- The first interior hat has weight at most N times the support radius times the mass. -/
theorem physicalTailEnergy_first_interior_hat_bound {N K : ℕ} (hN : N ≤ K + 1) :
    |physicalTailEnergy K (tailMeshHat N 1)| ≤
      tailCapacityDeficit K * ((N : ℝ)/((K : ℝ)+1)) := by
  have h0 : tailMeshHat N 1 0 = 0 := by simp [tailMeshHat]
  have h := physicalTailEnergy_test_error K (tailMeshHat N 1)
    (a := (N : ℝ)/((K : ℝ)+1)) (fun j hj => by
      rw [(hats_first_cell N _ (mesh_site_in_first_cell hN hj)).2.1, h0, sub_zero,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg N) (tailEnergySite j).property.1)]
      change (N : ℝ)*(1/((j : ℝ)+1)) ≤ _
      rw [mul_one_div]
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
      exact_mod_cast Nat.succ_le_succ hj)
  simpa only [h0,mul_zero,sub_zero] using h

end RiemannResearch.RH.Pareto.PrimePowerSchur
