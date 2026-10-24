/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SignedEnergyAverages
import RiemannResearch.Analysis.GeometricHeadSelection
import Mathlib.Analysis.SpecificLimits.Normed
import RiemannResearch.RH.ParetoReciprocalEnergyAverages
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ParetoLegalApproximationClosure

/-!
# Actual legal approximation from reciprocal-energy divergence

Source: user-provided `RH_Averaging_Limit_Research_Agenda_2026-10-24`,
Priority 3. The explicit finite weighted syntheses are legal, converge to the
actual constant target, and place it in the closed legal subspace. The only
asymptotic arithmetic input is the stated reciprocal-energy divergence.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto

open RiemannResearch.Analysis

/-- An actual finite legal sequence converges to the actual constant target
under reciprocal-energy divergence. The selector uses only the executable
amplitude certificates, and no uniform unweighted energy bound is assumed. -/
theorem online_reciprocal_legal_closure
    (S : Submodule ℝ ThresholdHilbert) (F : ℕ → ThresholdHilbert)
    (U : ℕ → ℕ) (A : ℕ → ℝ)
    (hlegal : ∀ N, F N ∈ S) (hA : ∀ i, 1 ≤ A i)
    (henergy : ∀ i, ‖F (exactHeadSelection U i) - hilbertOne‖ ^ 2 ≤ A i)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (F N) n - 1| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (F N) n = 1)
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop) :
    (∀ m, reciprocalEnergyAverage (fun i => F (exactHeadSelection U i)) A m ∈ S) ∧
      Tendsto (reciprocalEnergyAverage (fun i => F (exactHeadSelection U i)) A)
        atTop (𝓝 hilbertOne) ∧
      hilbertOne ∈ S.topologicalClosure := by
  let r : ℕ → ThresholdHilbert := fun N => F N - hilbertOne
  have hseq (N n : ℕ) (hn : 0 < n) :
      hilbertSequence (r N) n = hilbertSequence (F N) n - 1 := by
    change hilbertSequenceLinear (F N - hilbertOne) n = _
    rw [map_sub]
    change hilbertSequence (F N) n - hilbertSequence hilbertOne n = _
    rw [hilbertOne_sequence]
    simp only [zeroAnchor, if_neg (Nat.ne_of_gt hn)]
  have hrphysical : ∀ N n, 0 < n →
      |hilbertSequence (r N) n| ≤ (U N : ℝ) := by
    intro N n hn
    rw [hseq N n hn]
    exact hphysical N n hn
  have hrhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (r N) n = 0 := by
    intro N n hn hnN
    rw [hseq N n hn, hhead N n hn hnN, sub_self]
  have hres := online_reciprocal_energy_average_tendsto r U A hA henergy
    hrphysical hrhead hmass
  have ht : Tendsto (reciprocalEnergyAverage (fun i => F (exactHeadSelection U i)) A)
      atTop (𝓝 hilbertOne) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have he := Metric.tendsto_nhds.mp hres ε hε
    filter_upwards [eventually_gt_atTop 0, he] with m hm hem
    have hpositive : 0 < ∑ i ∈ Finset.range m, (A i)⁻¹ :=
      reciprocalEnergyMass_pos A (fun i => lt_of_lt_of_le zero_lt_one (hA i)) hm
    have hid := reciprocalEnergyAverage_sub (fun i => F (exactHeadSelection U i))
      A hilbertOne m (ne_of_gt hpositive)
    change dist (reciprocalEnergyAverage (fun i => F (exactHeadSelection U i)) A m)
      hilbertOne < ε
    rw [dist_eq_norm, ← hid]
    change dist (reciprocalEnergyAverage (fun i => F (exactHeadSelection U i) - hilbertOne)
      A m) 0 < ε at hem
    simpa only [dist_zero_right] using hem
  have hmem : ∀ m, reciprocalEnergyAverage (fun i => F (exactHeadSelection U i)) A m ∈ S :=
    reciprocalEnergyAverage_mem S _ A (fun i => hlegal _)
  refine ⟨hmem, ht, ?_⟩
  change hilbertOne ∈ closure (S : Set ThresholdHilbert)
  exact isClosed_closure.mem_of_tendsto ht
    (Filter.Eventually.of_forall fun m => subset_closure (hmem m))

/-- Conditional RH criterion with no uniform residual norm bound. The
remaining arithmetic obligation is divergence of the selected reciprocal
complete-energy certificates, together with the displayed physical inputs. -/
theorem riemannHypothesis_of_online_reciprocal_energy
    (D : Set ℕ) (hD : ∀ d ∈ D, 0 < d)
    (F : ℕ → ThresholdHilbert) (U : ℕ → ℕ) (A : ℕ → ℝ)
    (hlegal : ∀ N, F N ∈ hilbertLegalSubspace D) (hA : ∀ i, 1 ≤ A i)
    (henergy : ∀ i, ‖F (exactHeadSelection U i) - hilbertOne‖ ^ 2 ≤ A i)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (F N) n - 1| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (F N) n = 1)
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop) :
    RiemannHypothesis := by
  have h1 := (online_reciprocal_legal_closure (hilbertLegalSubspace D) F U A
    hlegal hA henergy hphysical hhead hmass).2.2
  exact riemannHypothesis_of_legal_paretoError D hD
    ((hilbertOne_mem_legalClosure_iff_paretoError D hD).mp h1)

end RiemannResearch.RH.Pareto
