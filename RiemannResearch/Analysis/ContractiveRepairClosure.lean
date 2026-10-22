import RiemannResearch.Analysis.ContractiveRepair
import RiemannResearch.Analysis.MeanNormalization
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Vanishing-repair orbits and closed approximation spaces

Source: Section 4 of the contracting-evolution report. This exact equivalence
makes the logical difficulty explicit: existence of a finite legal orbit
with vanishing repair is equivalent to membership of the fixed target in
the closed legal space, under the stated contraction hypotheses.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis.ContractiveRepair

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite-legal, mean-one orbit whose actual repair errors vanish. -/
def HasVanishingRepairOrbit (V : Submodule ℝ E) (P : E →L[ℝ] E)
    (ℓ : E →L[ℝ] ℝ) : Prop :=
  ∃ F : ℕ → E, (∀ n, F n ∈ V) ∧ (∀ n, ℓ (F n) = 1) ∧
    Tendsto (repairError P.toLinearMap F) atTop (𝓝 0)

theorem mem_closure_of_vanishing_repair_orbit
    (V : Submodule ℝ E) (P : E →L[ℝ] E) (ℓ : E →L[ℝ] ℝ) (z : E) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hz : P z = z) (hℓz : ℓ z = 1)
    (hcontract : ∀ x, ℓ x = 0 → ‖P x‖ ≤ q * ‖x‖)
    (horbit : HasVanishingRepairOrbit V P ℓ) : z ∈ V.topologicalClosure := by
  obtain ⟨F, hFV, hFm, he⟩ := horbit
  change z ∈ closure (V : Set E)
  exact mem_closure_iff_seq_limit.2 ⟨F, hFV,
    tendsto_fixedPoint_of_vanishing_repair P.toLinearMap ℓ.toLinearMap F z
      hq0 hq1 hz hℓz hFm hcontract he⟩

/-- The converse uses approximation of the target, continuity of P, and exact
mean normalization. It does not assume P preserves the legal subspace. -/
theorem vanishing_repair_orbit_of_mem_closure
    (V : Submodule ℝ E) (P : E →L[ℝ] E) (ℓ : E →L[ℝ] ℝ) (z : E)
    (hz : P z = z) (hℓz : ℓ z = 1) (hV : z ∈ V.topologicalClosure) :
    HasVanishingRepairOrbit V P ℓ := by
  change z ∈ closure (V : Set E) at hV
  obtain ⟨G, hGV, hG⟩ := mem_closure_iff_seq_limit.1 hV
  have hmeans : Tendsto (fun n => ℓ (G n)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, hℓz] using (ℓ.continuous.tendsto z).comp hG
  obtain ⟨N, hN⟩ := (hmeans.eventually
    (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists
  let v : E := (ℓ (G N))⁻¹ • G N
  have hvV : v ∈ V := V.smul_mem _ (hGV N)
  have hvm : ℓ v = 1 := by
    simp [v, map_smul, ne_of_gt hN]
  let F : ℕ → E := fun n => MeanNormalization.normalize ℓ v (G n)
  have hFV : ∀ n, F n ∈ V := fun n =>
    MeanNormalization.normalize_mem V ℓ v (G n) hvV (hGV n)
  have hFm : ∀ n, ℓ (F n) = 1 := fun n =>
    MeanNormalization.normalize_mean ℓ v (G n) hvm
  have hc : Continuous (fun y : E => MeanNormalization.normalize ℓ v y) := by
    exact continuous_id.add ((continuous_const.sub ℓ.continuous).smul continuous_const)
  have hF : Tendsto F atTop (𝓝 z) := by
    simpa only [F, Function.comp_def, MeanNormalization.normalize, hℓz,
      sub_self, zero_smul, add_zero]
      using (hc.tendsto z).comp hG
  refine ⟨F, hFV, hFm, ?_⟩
  have he := (hF.comp (Filter.tendsto_add_atTop_nat 1)).sub
    ((P.continuous.tendsto z).comp hF)
  change Tendsto (fun n => F (n + 1) - P (F n)) atTop (𝓝 0)
  simpa only [Function.comp_def, hz, sub_self] using he

/-- Exact equivalence: a contracting evolution does not make the arithmetic
approximation obligation disappear. -/
theorem vanishing_repair_orbit_iff_mem_closure
    (V : Submodule ℝ E) (P : E →L[ℝ] E) (ℓ : E →L[ℝ] ℝ) (z : E) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hz : P z = z) (hℓz : ℓ z = 1)
    (hcontract : ∀ x, ℓ x = 0 → ‖P x‖ ≤ q * ‖x‖) :
    HasVanishingRepairOrbit V P ℓ ↔ z ∈ V.topologicalClosure :=
  ⟨mem_closure_of_vanishing_repair_orbit V P ℓ z hq0 hq1 hz hℓz hcontract,
    vanishing_repair_orbit_of_mem_closure V P ℓ z hz hℓz⟩

end RiemannResearch.Analysis.ContractiveRepair
