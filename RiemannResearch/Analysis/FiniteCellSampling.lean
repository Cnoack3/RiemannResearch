/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Finite cell sampling and exact importance weights

Source: user-directed zero-ordinate/CRT discussion, 21 October 2026.
The finite regrouping and limit transfer are elementary. Uniform cell
frequencies are explicit hypotheses; no zeta-zero equidistribution theorem
is asserted here. The RH consumer is `RH.QZeroPhaseSampling`.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace RiemannResearch.Analysis.FiniteCellSampling

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

def cellFrequency (s : Finset κ) (A : κ → ι) (a : ι) : ℝ :=
  (∑ t ∈ s, if A t = a then (1 : ℝ) else 0) / (s.card : ℝ)

def sampleMean (s : Finset κ) (A : κ → ι) (h : ι → ℝ) : ℝ :=
  (∑ t ∈ s, h (A t)) / (s.card : ℝ)

/-- Exact regrouping, valid even for an empty sample. -/
theorem sampleMean_eq_cells (s : Finset κ) (A : κ → ι) (h : ι → ℝ) :
    sampleMean s A h = ∑ a, cellFrequency s A a * h a := by
  classical
  unfold sampleMean cellFrequency
  simp_rw [div_mul_eq_mul_div, Finset.sum_mul]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  simp

/-- The density multiplier and empirical relative frequency are retained exactly. -/
theorem weighted_sampleMean_eq (s : Finset κ) (A : κ → ι)
    (c : ℝ) (w h : ι → ℝ) :
    sampleMean s A (fun a => (c * w a) * h a) =
      ∑ a, w a * (c * cellFrequency s A a) * h a := by
  rw [sampleMean_eq_cells]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem sampleMean_tendsto_of_frequencies
    (s : ℕ → Finset κ) (A : κ → ι) (μ h : ι → ℝ)
    (hfreq : ∀ a, Tendsto (fun n => cellFrequency (s n) A a) atTop (𝓝 (μ a))) :
    Tendsto (fun n => sampleMean (s n) A h) atTop (𝓝 (∑ a, μ a * h a)) := by
  simp_rw [sampleMean_eq_cells]
  exact tendsto_finsetSum _ (fun a _ => (hfreq a).mul_const (h a))

/-- Uniform cell frequencies recover an arbitrary finite weighted functional. -/
theorem weighted_sampleMean_tendsto
    (s : ℕ → Finset κ) (A : κ → ι) (c : ℝ) (hc : c ≠ 0)
    (w h : ι → ℝ)
    (hfreq : ∀ a, Tendsto (fun n => cellFrequency (s n) A a) atTop (𝓝 (1 / c))) :
    Tendsto (fun n => sampleMean (s n) A (fun a => (c * w a) * h a))
      atTop (𝓝 (∑ a, w a * h a)) := by
  have ht := sampleMean_tendsto_of_frequencies s A (fun _ => 1 / c)
    (fun a => (c * w a) * h a) hfreq
  convert ht using 1
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  field_simp

/-- A bijective relabeling preserves empirical frequencies exactly. -/
theorem cellFrequency_equiv {ι ν κ : Type*}
    [DecidableEq ι] [DecidableEq ν]
    (e : ι ≃ ν) (s : Finset κ) (A : κ → ι) (b : ν) :
    cellFrequency s (fun j => e (A j)) b = cellFrequency s A (e.symm b) := by
  unfold cellFrequency
  simp only [Equiv.apply_eq_iff_eq_symm_apply]

end RiemannResearch.Analysis.FiniteCellSampling
