import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Reciprocal summability forced by sparse smooth-scale clusters

This is the counting part of the obstruction to the suggested normalized
Bessel bound for the Pareto repair family. It does not use prime-counting
asymptotics. A square-root bound on the number of primes assigned to each
`3^a*5^b` scale forces convergence of their reciprocal sum. Euler's divergence
then supplies the contradiction in the RH consumer.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.SmoothScale

/-- Finite fiber bounds against a summable majorant imply summability globally. -/
theorem summable_of_finite_fiber_sum_le {ι κ : Type*} [DecidableEq κ] (c : ι → κ)
    (f : ι → ℝ) (g : κ → ℝ) (hf : ∀ i, 0 ≤ f i) (hg0 : ∀ k, 0 ≤ g k)
    (hg : Summable g)
    (hbound : ∀ (s : Finset ι) k, ∑ i ∈ s.filter (fun i => c i = k), f i ≤ g k) :
    Summable f := by
  classical
  apply summable_of_sum_le hf
  intro s
  calc
    ∑ i ∈ s, f i = ∑ k ∈ s.image c, ∑ i ∈ s.filter (fun i => c i = k), f i := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Finset.mem_image_of_mem c hi]
    _ ≤ ∑ k ∈ s.image c, g k := Finset.sum_le_sum (fun k _ => hbound s k)
    _ ≤ ∑' k, g k := hg.sum_le_tsum _ (fun k _ => hg0 k)

noncomputable def inverseSmoothRoot (j : ℕ × ℕ) : ℝ :=
  1 / Real.sqrt ((3 : ℝ)^j.1 * (5 : ℝ)^j.2)

theorem inverseSmoothRoot_nonneg (j : ℕ × ℕ) : 0 ≤ inverseSmoothRoot j := by
  unfold inverseSmoothRoot
  positivity

private theorem sqrt_natPow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    Real.sqrt (x^n) = (Real.sqrt x)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]

theorem inverseSmoothRoot_eq_geometric (j : ℕ × ℕ) :
    inverseSmoothRoot j = (1 / Real.sqrt 3)^j.1 * (1 / Real.sqrt 5)^j.2 := by
  unfold inverseSmoothRoot
  rw [Real.sqrt_mul (by positivity), sqrt_natPow 3 (by norm_num),
    sqrt_natPow 5 (by norm_num)]
  simp only [one_div, mul_inv_rev, inv_pow]
  ring

theorem inverseSmoothRoot_summable : Summable inverseSmoothRoot := by
  have h3 : 1 < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have h5 : 1 < Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have h3' : ‖(1 : ℝ) / Real.sqrt 3‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_lt_one (by positivity)).mpr h3
  have h5' : ‖(1 : ℝ) / Real.sqrt 5‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (div_lt_one (by positivity)).mpr h5
  have hsum := (summable_geometric_of_norm_lt_one h3').mul_of_nonneg
    (summable_geometric_of_norm_lt_one h5') (fun _ => by positivity)
    (fun _ => by positivity)
  exact hsum.congr (fun j => (inverseSmoothRoot_eq_geometric j).symm)

/-- A quadratic cardinal bound controls the reciprocal mass in one cluster. -/
theorem finite_reciprocal_sum_le_sqrt_bound {ι : Type*} (s : Finset ι)
    (v : ι → ℝ) (M D : ℝ) (hM : 0 < M) (hD : 0 ≤ D)
    (hv : ∀ i ∈ s, 0 < v i ∧ M ≤ 2 * v i)
    (hcard : (s.card : ℝ)^2 ≤ D * M) :
    (∑ i ∈ s, 1 / v i) ≤ 2 * Real.sqrt D / Real.sqrt M := by
  have hcard' : (s.card : ℝ) ≤ Real.sqrt D * Real.sqrt M := by
    have h := Real.sqrt_le_sqrt hcard
    simpa only [Real.sqrt_sq_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ s.card by positivity),
      Real.sqrt_mul hD] using h
  calc
    ∑ i ∈ s, 1 / v i ≤ ∑ _i ∈ s, 2 / M := by
      apply Finset.sum_le_sum
      intro i hi
      exact (div_le_div_iff₀ (hv i hi).1 hM).mpr (by simpa using (hv i hi).2)
    _ = (s.card : ℝ) * (2 / M) := by simp
    _ ≤ (Real.sqrt D * Real.sqrt M) * (2 / M) :=
      mul_le_mul_of_nonneg_right hcard' (by positivity)
    _ = 2 * Real.sqrt D / Real.sqrt M := by
      have hm0 : M ≠ 0 := ne_of_gt hM
      have hms0 : Real.sqrt M ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hM)
      have he := congrArg (fun t : ℝ => 2 * Real.sqrt D * t) (Real.sq_sqrt hM.le)
      field_simp
      nlinarith

/-- Smooth-scale square-root cluster bounds force reciprocal summability.
The indexing type is arbitrary; the prime specialization is a separate consumer. -/
theorem reciprocal_summable_of_smooth_cluster_bound {ι : Type*}
    (v : ι → ℝ) (a b : ι → ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hv : ∀ i, 0 < v i ∧ (3 : ℝ)^(a i) * (5 : ℝ)^(b i) ≤ 2 * v i)
    (hcluster : ∀ (s : Finset ι) (j : ℕ × ℕ),
      (∀ i ∈ s, (a i, b i) = j) →
      (s.card : ℝ)^2 ≤ D * ((3 : ℝ)^j.1 * (5 : ℝ)^j.2)) :
    Summable (fun i => 1 / v i) := by
  classical
  apply summable_of_finite_fiber_sum_le (fun i => (a i, b i))
    (fun i => 1 / v i) (fun j => 2 * Real.sqrt D * inverseSmoothRoot j)
    (fun i => by have := (hv i).1; positivity) (fun j => by
      exact mul_nonneg (by positivity) (inverseSmoothRoot_nonneg j))
    (inverseSmoothRoot_summable.mul_left (2 * Real.sqrt D))
  intro s j
  let t := s.filter (fun i => (a i, b i) = j)
  have ht : ∀ i ∈ t, (a i, b i) = j := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hbnd := finite_reciprocal_sum_le_sqrt_bound t v
    ((3 : ℝ)^j.1 * (5 : ℝ)^j.2) D (by positivity) hD
    (fun i hi => ⟨(hv i).1, by
      have he := ht i hi
      have ha := congrArg Prod.fst he
      have hb := congrArg Prod.snd he
      change a i = j.1 at ha
      change b i = j.2 at hb
      simpa only [ha, hb] using (hv i).2⟩)
    (hcluster t j ht)
  simpa only [t, inverseSmoothRoot, div_eq_mul_inv, one_mul] using hbnd

end RiemannResearch.Analysis.SmoothScale
