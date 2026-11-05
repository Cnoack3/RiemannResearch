/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeProbabilityMixture
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Countable positive mixture along variable radices
This is equation (14) in the prime-tree paper, including the exact mass
remaining after a finite number of stages. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace RiemannResearch.RH.PrimeTreeMellinLaws

def pathProduct (p : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => pathProduct p n * p n

private theorem pathProduct_ge (p : ℕ → ℕ) (hp : ∀ j, 2 ≤ p j) (n : ℕ) :
    n + 1 ≤ pathProduct p n := by
  induction n with
  | zero => simp [pathProduct]
  | succ n ih =>
    have h := Nat.mul_le_mul_left (pathProduct p n) (hp n)
    rw [Nat.mul_two] at h
    change n + 1 + 1 ≤ pathProduct p n * p n
    omega

def pathEvent (p : ℕ → ℕ) (j : ℕ) (S : Set ℝ) : Set ℝ :=
  (fun t : ℝ => t - Real.log (pathProduct p j : ℝ)) ⁻¹' S

private theorem missingMass_mul (D p : ℕ) (σ : ℝ) :
    missingMass (D * p) σ = missingMass D σ * missingMass p σ := by
  simpa only [missingMass, Nat.cast_mul] using
    (Real.mul_rpow (z := σ - 1) (Nat.cast_nonneg D) (Nat.cast_nonneg p))

theorem law_event_path_prefix (p : ℕ → ℕ) (hp : ∀ j, 2 ≤ p j)
    (σ : ℝ) (hσ : 0 < σ) (hσ' : σ < 1) {S : Set ℝ} (hS : MeasurableSet S) (k : ℕ) :
    (normalizedLaw (logWeight σ)).real S =
      (∑ j ∈ Finset.range k, (missingMass (pathProduct p j) σ -
        missingMass (pathProduct p (j + 1)) σ) *
        (normalizedLaw (logDepthWeight (p j) σ)).real (pathEvent p j S)) +
      missingMass (pathProduct p k) σ * (normalizedLaw (logWeight σ)).real
        (pathEvent p k S) := by
  induction k with
  | zero => simp [pathProduct, pathEvent, missingMass]
  | succ k ih =>
    have hm : MeasurableSet (pathEvent p k S) := (measurable_id.sub measurable_const) hS
    have e := law_event_mixture (p k) (hp k) σ hσ hσ' hm
    have hprod : 0 < (pathProduct p k : ℝ) := by
      exact_mod_cast (show 0 < pathProduct p k by have := pathProduct_ge p hp k; omega)
    have hpr : 0 < (p k : ℝ) := by exact_mod_cast (show 0 < p k by have := hp k; omega)
    have he : (fun t : ℝ => t - Real.log (p k : ℝ)) ⁻¹' pathEvent p k S =
        pathEvent p (k + 1) S := by
      ext t
      change (t - Real.log (p k : ℝ) - Real.log (pathProduct p k : ℝ) ∈ S) ↔
        (t - Real.log (pathProduct p (k + 1) : ℝ) ∈ S)
      rw [pathProduct, Nat.cast_mul, Real.log_mul hprod.ne' hpr.ne']
      ring_nf
    rw [he] at e
    have hmass : missingMass (pathProduct p (k + 1)) σ =
        missingMass (pathProduct p k) σ * missingMass (p k) σ :=
      missingMass_mul _ _ _
    rw [Finset.sum_range_succ, hmass]
    calc
      _ = _ := ih
      _ = _ := by rw [e]; ring

/-- Exact normalized probability mixture for every infinite path with arbitrary
integer radices at least 2, including any ascending prime path. -/
theorem law_event_path_hasSum (p : ℕ → ℕ) (hp : ∀ j, 2 ≤ p j)
    (σ : ℝ) (hσ : 0 < σ) (hσ' : σ < 1) {S : Set ℝ} (hS : MeasurableSet S) :
    HasSum (fun j : ℕ => (missingMass (pathProduct p j) σ -
      missingMass (pathProduct p (j + 1)) σ) *
        (normalizedLaw (logDepthWeight (p j) σ)).real (pathEvent p j S))
      ((normalizedLaw (logWeight σ)).real S) := by
  have hlim : Tendsto (pathProduct p) atTop atTop :=
    tendsto_atTop.2 fun a => (eventually_ge_atTop a).mono
      fun n hn => hn.trans ((Nat.le_succ _).trans (pathProduct_ge p hp n))
  have hr : Tendsto (fun n => missingMass (pathProduct p n) σ) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hσ')).comp
      (tendsto_natCast_atTop_atTop.comp hlim)
    simpa only [Function.comp_def, neg_sub, missingMass] using h
  have hnn (d : ℕ) : 0 ≤ missingMass d σ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  letI := normalizedLaw_isProbability (integrable_logWeight σ hσ hσ')
    (fun t => mul_nonneg (Int.fract_nonneg (Real.exp t)) (Real.exp_pos _).le)
    (integral_logWeight_pos σ hσ hσ')
  have ht : Tendsto (fun k : ℕ => missingMass (pathProduct p k) σ *
       (normalizedLaw (logWeight σ)).real (pathEvent p k S)) atTop (𝓝 0) :=
    squeeze_zero (fun k => mul_nonneg (hnn _) measureReal_nonneg)
      (fun k => mul_le_of_le_one_right (hnn _) measureReal_le_one) hr
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j => ?_) _).mpr
  · have hc : Tendsto (fun _ : ℕ => (normalizedLaw (logWeight σ)).real S) atTop
        (𝓝 ((normalizedLaw (logWeight σ)).real S)) := tendsto_const_nhds
    have h := hc.sub ht
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards with n
    have e := law_event_path_prefix p hp σ hσ hσ' hS n
    linarith
  · apply mul_nonneg _ measureReal_nonneg
    rw [show pathProduct p (j + 1) = pathProduct p j * p j from rfl, missingMass_mul]
    have hj : 1 < (p j : ℝ) := by exact_mod_cast (show 1 < p j from hp j)
    exact sub_nonneg.mpr (mul_le_of_le_one_right (hnn _)
      (Real.rpow_lt_one_of_one_lt_of_neg hj (sub_neg.mpr hσ')).le)

end RiemannResearch.RH.PrimeTreeMellinLaws
