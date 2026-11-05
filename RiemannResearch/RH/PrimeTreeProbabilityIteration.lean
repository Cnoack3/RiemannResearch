/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeProbabilityMixture
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Geometric translation series for the conductor law
Iteration of the exact translated density identity in Section 4.2 of the
prime-tree paper. Each term is the law of the finite-depth variable shifted
by a fixed integer multiple of the negative log conductor. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.PrimeTreeMellinLaws

def shiftEvent (D j : ℕ) (S : Set ℝ) : Set ℝ :=
  (fun t : ℝ => t - (j : ℝ) * Real.log D) ⁻¹' S

theorem law_event_geometric_prefix (D : ℕ) (hD : 1 < D) (σ : ℝ) (hσ : 0 < σ)
    (hσ' : σ < 1) {S : Set ℝ} (hS : MeasurableSet S) (k : ℕ) :
    (normalizedLaw (logWeight σ)).real S =
      (∑ j ∈ Finset.range k, (1 - missingMass D σ) * (missingMass D σ) ^ j *
        (normalizedLaw (logDepthWeight D σ)).real (shiftEvent D j S)) +
      (missingMass D σ) ^ k * (normalizedLaw (logWeight σ)).real (shiftEvent D k S) := by
  induction k with
  | zero => simp [shiftEvent]
  | succ k ih =>
    have hm : MeasurableSet (shiftEvent D k S) := (measurable_id.sub measurable_const) hS
    have e := law_event_mixture D hD σ hσ hσ' hm
    have he : (fun t : ℝ => t - Real.log D) ⁻¹' shiftEvent D k S = shiftEvent D (k + 1) S := by
      ext t
      change (t - Real.log D - (k : ℝ) * Real.log D ∈ S) ↔
        (t - ((k + 1 : ℕ) : ℝ) * Real.log D ∈ S)
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      ring_nf
    rw [he] at e
    rw [Finset.sum_range_succ, pow_succ]
    calc
      _ = _ := ih
      _ = _ := by rw [e]; ring

/-- Countable probability mixture. Its weights are exactly the masses of
Geom(1−δ) on 0,1,… with δ = D^(σ−1). -/
theorem law_event_geometric_hasSum (D : ℕ) (hD : 1 < D) (σ : ℝ) (hσ : 0 < σ)
    (hσ' : σ < 1) {S : Set ℝ} (hS : MeasurableSet S) :
    HasSum (fun j : ℕ => (1 - missingMass D σ) * (missingMass D σ) ^ j *
      (normalizedLaw (logDepthWeight D σ)).real (shiftEvent D j S))
      ((normalizedLaw (logWeight σ)).real S) := by
  have hDr : (1 : ℝ) < D := by exact_mod_cast hD
  have hδ0 : 0 ≤ missingMass D σ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hδ1 : missingMass D σ < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hDr (sub_neg.mpr hσ')
  letI := normalizedLaw_isProbability (integrable_logWeight σ hσ hσ')
    (fun t => mul_nonneg (Int.fract_nonneg (Real.exp t)) (Real.exp_pos _).le)
    (integral_logWeight_pos σ hσ hσ')
  have ht : Tendsto (fun k : ℕ => missingMass D σ ^ k *
      (normalizedLaw (logWeight σ)).real (shiftEvent D k S)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => mul_nonneg (pow_nonneg hδ0 k) measureReal_nonneg) _
      (tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1)
    exact fun k => mul_le_of_le_one_right (pow_nonneg hδ0 _) measureReal_le_one
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k =>
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hδ1.le) (pow_nonneg hδ0 k)) measureReal_nonneg) _).mpr
  have hc : Tendsto (fun _ : ℕ => (normalizedLaw (logWeight σ)).real S) atTop
      (𝓝 ((normalizedLaw (logWeight σ)).real S)) := tendsto_const_nhds
  have hl := hc.sub ht
  simp only [sub_zero] at hl
  apply hl.congr'
  apply Eventually.of_forall
  intro k
  have e := law_event_geometric_prefix D hD σ hσ hσ' hS k
  dsimp only
  linarith

end RiemannResearch.RH.PrimeTreeMellinLaws
