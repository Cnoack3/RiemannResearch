import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Vanishing corrections to bounded square energy

These statements need only fixed-coordinate convergence, pointwise bounds, and a
uniform finite square-energy bound. They do not assert that unweighted square
energy vanishes.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.BoundedSquareEnergy

/-- A moving finite sum tends to zero under a summable majorant. -/
theorem sum_Icc_tendsto_zero (f : ℕ → ℕ → ℝ) (M : ℕ → ℝ)
    (hM : Summable M) (hM0 : ∀ k, 0 ≤ M k)
    (hlim : ∀ k, 0 < k → Tendsto (fun N => f N k) atTop (𝓝 0))
    (hbound : ∀ N k, k ∈ Finset.Icc 1 N → ‖f N k‖ ≤ M k) :
    Tendsto (fun N => ∑ k ∈ Finset.Icc 1 N, f N k) atTop (𝓝 0) := by
  let F (N k : ℕ) : ℝ := if k ∈ Finset.Icc 1 N then f N k else 0
  have hp (k : ℕ) : Tendsto (fun N => F N k) atTop (𝓝 (0 : ℝ)) := by
    by_cases hk : 0 < k
    · apply (hlim k hk).congr'
      filter_upwards [eventually_ge_atTop k] with N hN
      have hmem : k ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hk, hN⟩
      simp only [F, if_pos hmem]
    · have hk0 : k = 0 := by omega
      simpa [F, hk0] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hb : ∀ᶠ N : ℕ in atTop, ∀ k, ‖F N k‖ ≤ M k := by
    apply Eventually.of_forall
    intro N k
    by_cases hk : k ∈ Finset.Icc 1 N
    · simpa only [F, if_pos hk] using hbound N k hk
    · simpa only [F, if_neg hk, norm_zero] using hM0 k
  have h := tendsto_tsum_of_dominated_convergence hM hp hb
  have he (N : ℕ) : (∑' k, F N k) = ∑ k ∈ Finset.Icc 1 N, f N k := by
    rw [tsum_eq_sum (s := Finset.Icc 1 N) (by intro k hk; simp only [F, if_neg hk])]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [F, if_pos hk]
  simpa only [he, tsum_zero] using h

/-- Pointwise-vanishing uniformly bounded coordinates have vanishing inverse-square energy. -/
theorem weighted_square_tendsto_zero (u : ℕ → ℕ → ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hlim : ∀ k, 0 < k → Tendsto (fun N => u N k) atTop (𝓝 0))
    (hbound : ∀ N k, 0 < k → |u N k| ≤ K) :
    Tendsto (fun N => ∑ k ∈ Finset.Icc 1 N,
      u N k ^ 2 / (k : ℝ) ^ 2) atTop (𝓝 0) := by
  apply sum_Icc_tendsto_zero _ (fun k => K ^ 2 / (k : ℝ) ^ 2)
  · have hs : Summable (fun k : ℕ => ((k : ℝ) ^ 2)⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    simpa only [div_eq_mul_inv] using hs.mul_left (K ^ 2)
  · intro k
    positivity
  · intro k hk
    simpa using ((hlim k hk).pow 2).div_const ((k : ℝ) ^ 2)
  · intro N k hk
    have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
    have hs : u N k ^ 2 ≤ K ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (u N k)) hK).mpr (hbound N k hk0)
      simpa only [sq_abs] using h
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ u N k ^ 2 / (k : ℝ) ^ 2)]
    exact div_le_div_of_nonneg_right hs (sq_nonneg _)

/-- A square dominated by a null sequence is itself a null sequence. -/
theorem tendsto_zero_of_square_le (u v : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (h : ∀ N, u N ^ 2 ≤ v N) :
    Tendsto u atTop (𝓝 0) := by
  have hs : Tendsto (fun N => Real.sqrt (v N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hv)
  have ha : Tendsto (fun N => |u N|) atTop (𝓝 0) :=
    squeeze_zero (fun N => abs_nonneg _) (fun N => Real.abs_le_sqrt (h N)) hs
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by
    simpa only [Real.norm_eq_abs] using ha)

/-- The inverse-linear square correction vanishes even if total energy persists. -/
theorem inverse_linear_square_tendsto_zero (a : ℕ → ℕ → ℝ)
    (hlim : ∀ k, 0 < k → Tendsto (fun N => a N k) atTop (𝓝 0))
    (hbound : ∀ N k, 0 < k → |a N k| ≤ 2)
    (henergy : ∀ N, (∑ k ∈ Finset.Icc 1 N, a N k ^ 2) ≤ 10) :
    Tendsto (fun N => ∑ k ∈ Finset.Icc 1 N, a N k ^ 2 / (k : ℝ))
      atTop (𝓝 0) := by
  have hD := weighted_square_tendsto_zero a 2 (by norm_num) hlim hbound
  apply tendsto_zero_of_square_le _ (fun N => 10 *
    ∑ k ∈ Finset.Icc 1 N, a N k ^ 2 / (k : ℝ) ^ 2)
  · simpa using hD.const_mul 10
  · intro N
    have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
      (fun k => a N k) (fun k => a N k / (k : ℝ))
    have he1 : (∑ k ∈ Finset.Icc 1 N, a N k * (a N k / (k : ℝ))) =
        ∑ k ∈ Finset.Icc 1 N, a N k ^ 2 / (k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have he2 : (∑ k ∈ Finset.Icc 1 N, (a N k / (k : ℝ)) ^ 2) =
        ∑ k ∈ Finset.Icc 1 N, a N k ^ 2 / (k : ℝ) ^ 2 := by
      simp only [div_pow]
    rw [he1, he2] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (henergy N) (by positivity))

/-- The signed inverse-linear mixed correction vanishes by finite Cauchy--Schwarz. -/
theorem inverse_linear_mixed_tendsto_zero (a b : ℕ → ℕ → ℝ)
    (hlim : ∀ k, 0 < k → Tendsto (fun N => b N k) atTop (𝓝 0))
    (hbound : ∀ N k, 0 < k → |b N k| ≤ 1)
    (henergy : ∀ N, (∑ k ∈ Finset.Icc 1 N, a N k ^ 2) ≤ 10) :
    Tendsto (fun N => ∑ k ∈ Finset.Icc 1 N, a N k * b N k / (k : ℝ))
      atTop (𝓝 0) := by
  have hD := weighted_square_tendsto_zero b 1 (by norm_num) hlim hbound
  apply tendsto_zero_of_square_le _ (fun N => 10 *
    ∑ k ∈ Finset.Icc 1 N, b N k ^ 2 / (k : ℝ) ^ 2)
  · simpa using hD.const_mul 10
  · intro N
    have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
      (fun k => a N k) (fun k => b N k / (k : ℝ))
    have he1 : (∑ k ∈ Finset.Icc 1 N, a N k * (b N k / (k : ℝ))) =
        ∑ k ∈ Finset.Icc 1 N, a N k * b N k / (k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have he2 : (∑ k ∈ Finset.Icc 1 N, (b N k / (k : ℝ)) ^ 2) =
        ∑ k ∈ Finset.Icc 1 N, b N k ^ 2 / (k : ℝ) ^ 2 := by
      simp only [div_pow]
    rw [he1, he2] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right (henergy N) (by positivity))

/-- The Pareto-weighted boundary square correction vanishes. -/
theorem pareto_square_tendsto_zero (b : ℕ → ℕ → ℝ)
    (hlim : ∀ k, 0 < k → Tendsto (fun N => b N k) atTop (𝓝 0))
    (hbound : ∀ N k, 0 < k → |b N k| ≤ 1) :
    Tendsto (fun N => ∑ k ∈ Finset.Icc 1 N,
      b N k ^ 2 / ((k : ℝ) * ((k : ℝ) + 1))) atTop (𝓝 0) := by
  have hD := weighted_square_tendsto_zero b 1 (by norm_num) hlim hbound
  apply squeeze_zero (fun N => by positivity) _ hD
  intro N
  apply Finset.sum_le_sum
  intro k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith

/-- Ordinary positive-index partial sums of a summable zero-based sequence. -/
theorem summable_tendsto_sum_Icc (f : ℕ → ℝ) (hf : Summable f) (hzero : f 0 = 0) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n) atTop (𝓝 (∑' n, f n)) := by
  have hu (N : ℕ) : ({0} : Finset ℕ) ∪ Finset.Icc 1 N = Finset.range (N + 1) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc, Finset.mem_range]
    omega
  have hd (N : ℕ) : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 N) := by simp
  have he (N : ℕ) : (∑ n ∈ Finset.range (N + 1), f n) = ∑ n ∈ Finset.Icc 1 N, f n := by
    rw [← hu N, Finset.sum_union (hd N)]
    simp only [Finset.sum_singleton, hzero, zero_add]
  have hsucc : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  simpa only [Function.comp_def, he] using hf.hasSum.tendsto_sum_nat.comp hsucc

theorem summable_square_of_reciprocal_bound (f : ℕ → ℝ) (hzero : f 0 = 0)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, 0 < n → |f n| ≤ C / (n : ℝ)) :
    Summable (fun n => (f n) ^ 2) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
    simpa only [one_div] using
      (Real.summable_nat_pow_inv.mpr (by norm_num) :
        Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹))
  apply (hs.mul_left (C ^ 2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hn : n = 0
  · simp [hn, hzero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hsq := (sq_le_sq₀ (abs_nonneg (f n))
      (div_nonneg hC (Nat.cast_nonneg n))).mpr (hbound n hnpos)
    calc
      (f n) ^ 2 = |f n| ^ 2 := (sq_abs _).symm
      _ ≤ (C / (n : ℝ)) ^ 2 := hsq
      _ = C ^ 2 * (1 / (n : ℝ) ^ 2) := by ring

end RiemannResearch.Analysis.BoundedSquareEnergy
