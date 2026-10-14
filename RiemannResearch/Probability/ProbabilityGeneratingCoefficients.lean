/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Coefficient convergence from probability generating functions

Source: elementary truncation of a nonnegative probability series. A uniform
tail bound gives coefficient convergence by induction. In particular PGF
convergence on `(0,1)` implies convergence of every count probability.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology Classical

namespace RiemannResearch.Probability

def realPGF (a : ℕ → ℝ) (z : ℝ) : ℝ := ∑' k, a k * z ^ k

theorem pgf_summable (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (hs : HasSum a 1) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun k => a k * z ^ k) := by
  apply hs.summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (ha k) (pow_nonneg hz.1 k)
  · intro k
    exact mul_le_of_le_one_right (ha k) (pow_le_one₀ hz.1 hz.2)

set_option maxHeartbeats 800000 in
-- The series truncation proof elaborates several dependent summability instances.
/-- The exact series tail is positive and bounded by `z ^ (k+1)`. -/
theorem pgf_truncation_bounds (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (hs : HasSum a 1) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    0 ≤ realPGF a z - ∑ j ∈ Finset.range (k + 1), a j * z ^ j ∧
      realPGF a z - ∑ j ∈ Finset.range (k + 1), a j * z ^ j ≤ z ^ (k + 1) := by
  have hsz := pgf_summable a ha hs hz
  have hsTail : Summable (fun j => a (j + (k + 1))) :=
    (summable_nat_add_iff (k + 1)).2 hs.summable
  have hszTail : Summable (fun j => a (j + (k + 1)) * z ^ (j + (k + 1))) :=
    (summable_nat_add_iff (k + 1)).2 hsz
  have hsplit := hsz.sum_add_tsum_nat_add (k + 1)
  have hid : realPGF a z - ∑ j ∈ Finset.range (k + 1), a j * z ^ j =
      ∑' j, a (j + (k + 1)) * z ^ (j + (k + 1)) := by
    dsimp [realPGF]
    linarith only [hsplit]
  rw [hid]
  constructor
  · exact tsum_nonneg (fun j => mul_nonneg (ha _) (pow_nonneg hz.1 _))
  · have hmass : (∑' j, a (j + (k + 1))) ≤ 1 := by
      have hh := hs.summable.sum_add_tsum_nat_add (k + 1)
      rw [hs.tsum_eq] at hh
      have hh0 : 0 ≤ ∑ j ∈ Finset.range (k + 1), a j :=
        Finset.sum_nonneg (fun j _ => ha j)
      linarith only [hh, hh0]
    calc
      (∑' j, a (j + (k + 1)) * z ^ (j + (k + 1))) ≤
          ∑' j, a (j + (k + 1)) * z ^ (k + 1) := by
        apply hszTail.tsum_le_tsum _ (hsTail.mul_right _)
        intro j
        apply mul_le_mul_of_nonneg_left _ (ha _)
        rw [pow_add]
        exact mul_le_of_le_one_left (pow_nonneg hz.1 _) (pow_le_one₀ hz.1 hz.2)
      _ = (∑' j, a (j + (k + 1))) * z ^ (k + 1) := hsTail.tsum_mul_right _
      _ ≤ z ^ (k + 1) := mul_le_of_le_one_left (pow_nonneg hz.1 _) hmass

/-- Dividing after removing the first `k` coefficients isolates the next
coefficient to within `z`, uniformly over every probability distribution. -/
theorem pgf_normalized_remainder_bounds
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hs : HasSum a 1)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) (k : ℕ) :
    a k ≤ (realPGF a z - ∑ j ∈ Finset.range k, a j * z ^ j) / z ^ k ∧
      (realPGF a z - ∑ j ∈ Finset.range k, a j * z ^ j) / z ^ k ≤ a k + z := by
  obtain ⟨hl, hu⟩ := pgf_truncation_bounds a ha hs ⟨hz0.le, hz1⟩ k
  rw [Finset.sum_range_succ] at hl hu
  have hp : 0 < z ^ k := pow_pos hz0 k
  constructor
  · apply (le_div_iff₀ hp).mpr
    linarith only [hl]
  · apply (div_le_iff₀ hp).mpr
    rw [pow_succ] at hu
    nlinarith only [hu]

/-- Convergence of normalized nonnegative PGFs on `(0,1)` implies convergence
of every coefficient. No compactness, moments, or tightness premise is needed. -/
theorem coefficient_tendsto_of_pgf_tendsto
    (p : ℕ → ℕ → ℝ) (q : ℕ → ℝ)
    (hp : ∀ N k, 0 ≤ p N k) (hq : ∀ k, 0 ≤ q k)
    (hps : ∀ N, HasSum (p N) 1) (hqs : HasSum q 1)
    (hG : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun N => realPGF (p N) z) atTop (𝓝 (realPGF q z)))
    (k : ℕ) : Tendsto (fun N => p N k) atTop (𝓝 (q k)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      apply Metric.tendsto_nhds.2
      intro eps heps
      let z : ℝ := min (eps / 4) (1 / 2)
      have hz0 : 0 < z := lt_min (by linarith) (by norm_num)
      have hz1 : z < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hze : z ≤ eps / 4 := min_le_left _ _
      have hsum : Tendsto (fun N => ∑ j ∈ Finset.range k, p N j * z ^ j)
          atTop (𝓝 (∑ j ∈ Finset.range k, q j * z ^ j)) :=
        tendsto_finsetSum _ (fun j hj =>
          (ih j (Finset.mem_range.mp hj)).mul_const (z ^ j))
      have hR := ((hG z ⟨hz0, hz1⟩).sub hsum).div_const (z ^ k)
      have hclose := (Metric.tendsto_nhds.1 hR) (eps / 2) (by linarith)
      filter_upwards [hclose] with N hN
      obtain ⟨hpl, hpu⟩ := pgf_normalized_remainder_bounds
        (p N) (hp N) (hps N) hz0 hz1.le k
      obtain ⟨hql, hqu⟩ := pgf_normalized_remainder_bounds
        q hq hqs hz0 hz1.le k
      rw [Real.dist_eq, abs_lt] at hN ⊢
      constructor <;> linarith only [hN.1, hN.2, hpl, hpu, hql, hqu, hze, heps]

def poissonWeight (rate : ℝ) (k : ℕ) : ℝ := Real.exp (-rate) * rate ^ k / k.factorial

theorem poissonWeight_nonneg {rate : ℝ} (hr : 0 ≤ rate) (k : ℕ) :
    0 ≤ poissonWeight rate k := by
  dsimp [poissonWeight]
  positivity

theorem poissonWeight_hasSum (rate : ℝ) : HasSum (poissonWeight rate) 1 := by
  unfold poissonWeight
  have hs : HasSum (fun k : ℕ => rate ^ k / (k.factorial : ℝ)) (Real.exp rate) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp rate
  simpa only [poissonWeight, ← mul_div_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    using hs.mul_left (Real.exp (-rate))

theorem poissonWeight_pgf (rate z : ℝ) :
    realPGF (poissonWeight rate) z = Real.exp ((z - 1) * rate) := by
  have hs : HasSum (fun k : ℕ => (rate * z) ^ k / (k.factorial : ℝ))
      (Real.exp (rate * z)) := by
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (rate * z)
  have hsum := hs.mul_left (Real.exp (-rate))
  have he : (fun k => Real.exp (-rate) * ((rate * z) ^ k / (k.factorial : ℝ))) =
      (fun k => poissonWeight rate k * z ^ k) := by
    funext k
    simp only [poissonWeight, mul_pow]
    ring
  rw [he] at hsum
  rw [realPGF, hsum.tsum_eq, ← Real.exp_add]
  congr 1
  ring

/-- A conditional Poisson limit for the complete count mass function. -/
theorem count_mass_tendsto_poisson_of_pgf
    (p : ℕ → ℕ → ℝ) (rate : ℝ) (hr : 0 ≤ rate)
    (hp : ∀ N k, 0 ≤ p N k) (hps : ∀ N, HasSum (p N) 1)
    (hG : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun N => realPGF (p N) z) atTop (𝓝 (Real.exp ((z - 1) * rate))))
    (k : ℕ) :
    Tendsto (fun N => p N k) atTop
      (𝓝 (Real.exp (-rate) * rate ^ k / k.factorial)) := by
  apply coefficient_tendsto_of_pgf_tendsto p (poissonWeight rate) hp
    (poissonWeight_nonneg hr) hps (poissonWeight_hasSum rate) _ k
  intro z hz
  simpa only [poissonWeight_pgf] using hG z hz

theorem pmf_hasSum_real {α : Type*} (p : PMF α) :
    HasSum (fun a => (p a).toReal) 1 := by
  have hh := ENNReal.hasSum_toReal p.tsum_coe_ne_top
  rw [← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe] at hh
  simpa using hh

/-- The series PGF of a finite-law pushforward is its finite generating sum. -/
theorem realPGF_map_finite {α : Type*} [Fintype α]
    (p : PMF α) (f : α → ℕ) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    realPGF (fun k => ((p.map f) k).toReal) z = ∑ a, (p a).toReal * z ^ f a := by
  letI : MeasurableSpace α := ⊤
  have hf : Measurable f := measurable_of_finite f
  have hzMeas : Measurable (fun k : ℕ => z ^ k) := measurable_of_countable _
  have hi : Integrable (fun k : ℕ => z ^ k) (p.map f).toMeasure := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hzMeas.aestronglyMeasurable
    exact ae_of_all _ (fun k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz.1 k)]
      exact pow_le_one₀ hz.1 hz.2)
  calc
    realPGF (fun k => ((p.map f) k).toReal) z =
        ∫ k, z ^ k ∂(p.map f).toMeasure := by
      simpa only [realPGF, smul_eq_mul] using
        (PMF.integral_eq_tsum (p.map f) (fun k => z ^ k) hi).symm
    _ = ∫ a, z ^ f a ∂p.toMeasure := by
      rw [← PMF.toMeasure_map f p hf,
        integral_map hf.aemeasurable hzMeas.aestronglyMeasurable]
    _ = _ := by simp only [PMF.integral_eq_sum, smul_eq_mul]

end RiemannResearch.Probability
