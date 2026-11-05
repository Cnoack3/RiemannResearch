/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Concentration for triangular arrays of prime-coordinate observables

Source: the proof of formula (5) in C. Noack, *Prime trees, fractional parts,
and zeta zeros* (5 November 2026), and W. Hoeffding, JASA 58 (1963),
pp. 13–30, https://doi.org/10.1080/01621459.1963.10500830. Independence
is required within each row only. The product-measure result permits the
observables to depend on the row and the coordinate, as do the CRT lifts.
-/
noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal NNReal
namespace RiemannResearch.RH.PrimeTreeHaarRows
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

private theorem row_upper_eventually (Y : ℕ → ℕ → Ω → ℝ) (c : ℝ≥0) (hc : 0 < c)
    (hi : ∀ n, iIndepFun (Y n) P)
    (hmgf : ∀ n j, j < n → HasSubgaussianMGF (Y n j) c P)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, (∑ j ∈ Finset.range n, Y n j ω) < (n : ℝ)*ε := by
  let B := fun n : ℕ => {ω | (n : ℝ)*ε ≤ ∑ j ∈ Finset.range n, Y n j ω}
  let r : ℝ := Real.exp (-ε^2/(2*(c : ℝ)))
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hε))
    (mul_pos (by norm_num) hcR))
  have hs : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le hr
  have hb (n : ℕ) : P (B n) ≤ ENNReal.ofReal (r^n) := by
    rw [← ofReal_measureReal (measure_ne_top P _)]
    apply ENNReal.ofReal_le_ofReal
    have hh := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (hi n) (hmgf n)
      (mul_nonneg (Nat.cast_nonneg n) hε.le)
    change P.real {ω | (n : ℝ) * ε ≤ ∑ j ∈ Finset.range n, Y n j ω} ≤ _
    apply hh.trans_eq
    rw [show r ^ n = Real.exp ((n : ℝ) * (-ε^2/(2*(c : ℝ)))) by rw [Real.exp_nat_mul]]
    congr 1
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnR, hcR.ne'] <;> ring
  have hfin : (∑' n, P (B n)) ≠ ∞ := by
    apply ne_of_lt
    have hle : (∑' n, P (B n)) ≤ ∑' n, ENNReal.ofReal (r ^ n) := ENNReal.tsum_le_tsum hb
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => pow_nonneg (Real.exp_pos _).le n) hs] at hle
    exact hle.trans_lt ENNReal.ofReal_lt_top
  simpa only [B, Set.mem_ofPred_eq, not_le] using ae_eventually_notMem hfin

/-- Strong law for arbitrary triangular arrays with row-wise independence
and a single sub-Gaussian bound. The variables may use the same underlying
coordinates across all rows. -/
theorem row_average_ae_zero (Y : ℕ → ℕ → Ω → ℝ) (c : ℝ≥0) (hc : 0 < c)
    (hi : ∀ n, iIndepFun (Y n) P)
    (hmgf : ∀ n j, j < n → HasSubgaussianMGF (Y n j) c P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, Y n j ω)/(n : ℝ)) atTop (𝓝 0) := by
  let V := fun n j ω => -Y n j ω
  have hV (n : ℕ) : iIndepFun (V n) P := (hi n).comp (fun _ x => -x) (fun _ => measurable_neg)
  have hVmgf (n j : ℕ) (hj : j < n) : HasSubgaussianMGF (V n j) c P := (hmgf n j hj).neg
  obtain ⟨v, -, vp, vt⟩ : ∃ v : ℕ → ℝ, StrictAnti v ∧ (∀ i, 0 < v i) ∧ Tendsto v atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have upper := fun i => row_upper_eventually P Y c hc hi hmgf (v i) (vp i)
  have lower := fun i => row_upper_eventually P V c hc hV hVmgf (v i) (vp i)
  filter_upwards [ae_all_iff.2 upper, ae_all_iff.2 lower] with ω hu hl
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨i, hi⟩ : ∃ i, v i < ε := (vt.eventually_lt_const hε).exists
  filter_upwards [hu i, hl i, eventually_gt_atTop (0 : ℕ)] with n hu' hl' hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [V, Finset.sum_neg_distrib] at hl'
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor
  · apply (lt_div_iff₀ hnR).mpr
    nlinarith [mul_pos hnR (sub_pos.mpr hi)]
  · apply (div_lt_iff₀ hnR).mpr
    nlinarith [mul_pos hnR (sub_pos.mpr hi)]

/-- Centered bounded coordinate tests on the countable product satisfy the
strong law even when the test used at each coordinate changes with depth. -/
theorem product_row_average_ae {A : ℕ → Type*} [∀ j, MeasurableSpace (A j)]
    (μ : (j : ℕ) → Measure (A j)) [∀ j, IsProbabilityMeasure (μ j)]
    (X : (n j : ℕ) → A j → ℝ) (hX : ∀ n j, Measurable (X n j))
    (a b : ℝ) (hab : a < b) (hb : ∀ n j x, X n j x ∈ Set.Icc a b) :
    let H := Measure.infinitePi μ
    ∀ᵐ ω ∂H, Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n,
      (X n j (ω j) - ∫ η, X n j (η j) ∂H))/(n : ℝ)) atTop (𝓝 0) := by
  let H := Measure.infinitePi μ
  let F (n j : ℕ) (ω : (i : ℕ) → A i) := X n j (ω j)
  let Y (n j : ℕ) (ω : (i : ℕ) → A i) := F n j ω - ∫ η, F n j η ∂H
  have hF (n j : ℕ) : Measurable (F n j) := (hX n j).comp (measurable_pi_apply j)
  have hi (n : ℕ) : iIndepFun (F n) H := iIndepFun_infinitePi (hX n)
  have hc : 0 < (‖b-a‖₊ / 2)^2 := by
    have hne : b-a ≠ 0 := (sub_pos.mpr hab).ne'
    exact sq_pos_of_pos (div_pos (nnnorm_pos.mpr hne) (by norm_num))
  apply row_average_ae_zero H Y _ hc
  · intro n
    exact (hi n).comp (fun j x => x - ∫ η, F n j η ∂H) (fun _ => measurable_id.sub_const _)
  · intro n j _
    exact hasSubgaussianMGF_of_mem_Icc (hF n j).aemeasurable (ae_of_all _ (fun ω => hb n j (ω j)))

end RiemannResearch.RH.PrimeTreeHaarRows
