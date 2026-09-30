/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteWeightedEnergyComparison
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Exact weighted scalar energy and normalized pairing decay

Source: elementary finite weighted square expansion and Lagrange's identity
support the exact identities. The normalized pairing proof is the standard
finite-head/tail Cauchy--Schwarz argument for a square-summable survivor and a
divergent source. No signed summand is removed before the finite identities.
The concrete consumer is RH/ParetoFirstSitePrimeAlignment.lean.
-/
namespace RiemannResearch.Analysis.WeightedScalarEnergy
open scoped BigOperators
variable {ι : Type*}
def square (s : Finset ι) (w a : ι → ℝ) : ℝ := ∑ i ∈ s, w i * (a i) ^ 2
def product (s : Finset ι) (w a b : ι → ℝ) : ℝ := ∑ i ∈ s, w i * a i * b i
theorem square_nonneg (s : Finset ι) (w a : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ square s w a :=
  Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
theorem square_sub (s : Finset ι) (w a b : ι → ℝ) (t : ℝ) :
    square s w (fun i => b i - t * a i) =
      square s w b - 2 * t * product s w a b + t ^ 2 * square s w a := by
  unfold square product
  calc
    _ = ∑ i ∈ s, (w i * (b i) ^ 2 - (2 * t) * (w i * a i * b i) + t ^ 2 * (w i * (a i) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
theorem pair_identity (s : Finset ι) (w a b : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2) =
      2 * (square s w a * square s w b - (product s w a b) ^ 2) := by
  have hi (i : ι) :
      (∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2) =
        (w i * (a i) ^ 2) * square s w b +
          (w i * (b i) ^ 2) * square s w a -
          (2 * (w i * a i * b i)) * product s w a b := by
    unfold square product
    calc
      _ = ∑ j ∈ s, ((w i * (a i) ^ 2) * (w j * (b j) ^ 2) +
          (w i * (b i) ^ 2) * (w j * (a j) ^ 2) -
          (2 * (w i * a i * b i)) * (w j * a j * b j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = _ := by simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp_rw [hi]
  unfold square product
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring
theorem gram_nonneg (s : Finset ι) (w a b : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (product s w a b) ^ 2 ≤ square s w a * square s w b := by
  have hn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i * b j - a j * b i) ^ 2 :=
    Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj =>
      mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) (sq_nonneg _)))
  rw [pair_identity] at hn
  linarith
theorem completed_square (s : Finset ι) (w a b : ι → ℝ)
    (hU : square s w a ≠ 0) :
    square s w a + square s w b + 2 * product s w a b =
      (square s w a + product s w a b) ^ 2 / square s w a +
        square s w (fun i => b i - (product s w a b / square s w a) * a i) := by
  rw [square_sub]
  field_simp [hU]
  ring
theorem centered_square_eq (s : Finset ι) (w a b : ι → ℝ)
    (hU : square s w a ≠ 0) :
    square s w (fun i => b i - (product s w a b / square s w a) * a i) =
      (square s w a * square s w b - (product s w a b) ^ 2) / square s w a := by
  rw [square_sub]
  field_simp [hU]
  ring

/-- A square-summable survivor pairs with a divergent source at
o(sqrt(source energy)). A fixed finite head is separated before Cauchy--Schwarz
is used on the tail; no interchange of nonsummable series is involved. -/
theorem normalized_square_pairing_tendsto_zero (a b : ℕ → ℝ)
    (hb : Summable (fun n => (b n) ^ 2))
    (ha : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (a n) ^ 2)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun N => (∑ n ∈ Finset.range N, a n * b n) ^ 2 /
      (∑ n ∈ Finset.range N, (a n) ^ 2)) Filter.atTop (nhds 0) := by
  let U : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, (a n) ^ 2
  let P : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, a n * b n
  let E : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, (b n) ^ 2
  let L : ℝ := ∑' n, (b n) ^ 2
  have hU : Filter.Tendsto U Filter.atTop Filter.atTop := ha
  have hU0 (N : ℕ) : 0 ≤ U N := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hE : Filter.Tendsto E Filter.atTop (nhds L) := hb.hasSum.tendsto_sum_nat
  have hEL (N : ℕ) : E N ≤ L :=
    hb.sum_le_tsum (Finset.range N) (fun n _ => sq_nonneg _)
  change Filter.Tendsto (fun N => (P N) ^ 2 / U N) Filter.atTop (nhds 0)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hE (ε / 4) (by positivity)
  have htailSmall : L - E M < ε / 4 := by
    have h : |E M - L| < ε / 4 := by
      simpa only [dist_eq_norm, Real.norm_eq_abs] using hM M le_rfl
    have hl := (abs_lt.mp h).1
    linarith
  have hhead : Filter.Tendsto (fun N => 2 * (P M) ^ 2 / U N) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := 2 * (P M) ^ 2)).mul
        (tendsto_inv_atTop_zero.comp hU)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hhead (ε / 2) (by positivity)
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp ((Filter.tendsto_atTop.mp hU) 1)
  refine ⟨max M (max K J), fun N hN => ?_⟩
  have hMN : M ≤ N := (le_max_left _ _).trans hN
  have hKN : K ≤ N := (le_max_left K J).trans ((le_max_right M (max K J)).trans hN)
  have hJN : J ≤ N := (le_max_right K J).trans ((le_max_right M (max K J)).trans hN)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hMN
  have hUpos : 0 < U (M + k) := by linarith [hJ (M + k) hJN]
  have hheadSmall : 2 * (P M) ^ 2 / U (M + k) < ε / 2 := by
    have h : |2 * (P M) ^ 2 / U (M + k)| < ε / 2 := by
      simpa only [dist_eq_norm, Real.norm_eq_abs, sub_zero] using hK (M + k) hKN
    exact (le_abs_self _).trans_lt h
  let ua : ℝ := ∑ i ∈ Finset.range k, (a (M + i)) ^ 2
  let eb : ℝ := ∑ i ∈ Finset.range k, (b (M + i)) ^ 2
  let p : ℝ := ∑ i ∈ Finset.range k, a (M + i) * b (M + i)
  have hsplitU : U (M + k) = U M + ua := by
    simp only [U, ua, Finset.sum_range_add]
  have hsplitE : E (M + k) = E M + eb := by
    simp only [E, eb, Finset.sum_range_add]
  have hsplitP : P (M + k) = P M + p := by
    simp only [P, p, Finset.sum_range_add]
  have hua : ua ≤ U (M + k) := by linarith [hU0 M]
  have heb : eb ≤ L - E M := by linarith [hEL (M + k)]
  have heb0 : 0 ≤ eb := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hcs : p ^ 2 ≤ ua * eb :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.range k)
      (fun i => a (M + i)) (fun i => b (M + i))
  have htail : p ^ 2 ≤ U (M + k) * (L - E M) :=
    hcs.trans (mul_le_mul hua heb heb0 (hU0 (M + k)))
  have hnum : (P (M + k)) ^ 2 ≤ 2 * (P M) ^ 2 + 2 * U (M + k) * (L - E M) := by
    rw [hsplitP]
    nlinarith [sq_nonneg (P M - p)]
  have hbound : (P (M + k)) ^ 2 / U (M + k) ≤
      2 * (P M) ^ 2 / U (M + k) + 2 * (L - E M) := by
    calc
      _ ≤ (2 * (P M) ^ 2 + 2 * U (M + k) * (L - E M)) / U (M + k) :=
        div_le_div_of_nonneg_right hnum hUpos.le
      _ = _ := by field_simp [ne_of_gt hUpos]
  have hnonneg : 0 ≤ (P (M + k)) ^ 2 / U (M + k) :=
    div_nonneg (sq_nonneg _) hUpos.le
  have hfinal : (P (M + k)) ^ 2 / U (M + k) < ε := by linarith
  simpa only [dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_of_nonneg hnonneg]
    using hfinal

/-- Weighted version, with signs retained in the mixed sum. -/
theorem normalized_product_tendsto_zero (w a b : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (hb : Summable (fun n => w n * (b n) ^ 2))
    (ha : Filter.Tendsto (fun N => square (Finset.range N) w a)
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun N => (product (Finset.range N) w a b) ^ 2 /
      square (Finset.range N) w a) Filter.atTop (nhds 0) := by
  let a' := fun n => Real.sqrt (w n) * a n
  let b' := fun n => Real.sqrt (w n) * b n
  have hs (f : ℕ → ℝ) (N : ℕ) :
      (∑ n ∈ Finset.range N, (Real.sqrt (w n) * f n) ^ 2) =
        square (Finset.range N) w f := by
    simp only [square, mul_pow, Real.sq_sqrt (hw _)]
  have hp (N : ℕ) :
      (∑ n ∈ Finset.range N, a' n * b' n) = product (Finset.range N) w a b := by
    apply Finset.sum_congr rfl
    intro n hn
    change (Real.sqrt (w n) * a n) * (Real.sqrt (w n) * b n) = _
    calc
      _ = (Real.sqrt (w n)) ^ 2 * a n * b n := by ring
      _ = _ := by rw [Real.sq_sqrt (hw n)]
  have hb' : Summable (fun n => (b' n) ^ 2) := by
    apply hb.congr
    intro n
    dsimp [b']
    rw [mul_pow, Real.sq_sqrt (hw n)]
  have ha' : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (a' n) ^ 2)
      Filter.atTop Filter.atTop := by
    simpa only [a', hs] using ha
  simpa only [hp, a', hs] using normalized_square_pairing_tendsto_zero a' b' hb' ha'

/-- Exact regression completion at an arbitrary slope. -/
theorem regression_square_completion (s : Finset ι) (w a b : ι → ℝ)
    (t : ℝ) (hU : square s w a ≠ 0) :
    square s w (fun i => b i - t * a i) =
      square s w (fun i => b i - (product s w a b / square s w a) * a i) +
        square s w a * (t - product s w a b / square s w a) ^ 2 := by
  rw [square_sub, square_sub]
  field_simp [hU]
  ring

/-- Adding one weighted observation retains the full determinant square. -/
theorem centered_energy_update (U V X w a b : ℝ)
    (hU : U ≠ 0) (hU' : U + w * a ^ 2 ≠ 0) :
    V + w * b ^ 2 - (X + w * a * b) ^ 2 / (U + w * a ^ 2) =
      V - X ^ 2 / U + w * (U * b - X * a) ^ 2 / (U * (U + w * a ^ 2)) := by
  field_simp [hU, hU']
  ring

/-- A reduced weight is at least half of any common lower bound. -/
theorem reduced_weight_lower (u U v : ℝ)
    (hU : 0 < U) (hu : 0 ≤ u) (hUv : v ≤ U) (huv : v ≤ u) :
    v / 2 ≤ u * U / (U + u) := by
  apply (le_div_iff₀ (add_pos_of_pos_of_nonneg hU hu)).mpr
  have h1 := mul_nonneg (sub_nonneg.mpr huv) hU.le
  have h2 := mul_nonneg hu (sub_nonneg.mpr hUv)
  nlinarith

end RiemannResearch.Analysis.WeightedScalarEnergy
