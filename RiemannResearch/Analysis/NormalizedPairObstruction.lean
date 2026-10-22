import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! # Normalization estimates and the obstruction from close unit pairs -/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.NormalizedPairObstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact decomposition before the normalization estimate. -/
theorem normalize_difference_identity (x y : E) :
    ‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y) =
      (x - y) + (‖y‖ - ‖x‖) • NormedSpace.normalize y := by
  rw [smul_sub, NormedSpace.norm_smul_normalize, sub_smul,
    NormedSpace.norm_smul_normalize]
  abel

theorem normalize_difference_mul_norm_le (x y : E) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ * ‖x‖ ≤ 2 * ‖x - y‖ := by
  calc
    _ = ‖‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
      ring
    _ = ‖(x - y) + (‖y‖ - ‖x‖) • NormedSpace.normalize y‖ := by
      rw [normalize_difference_identity]
    _ ≤ ‖x - y‖ + ‖(‖y‖ - ‖x‖) • NormedSpace.normalize y‖ := norm_add_le _ _
    _ = ‖x - y‖ + |‖x‖ - ‖y‖| := by
      rw [norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hy, mul_one,
        abs_sub_comm]
    _ ≤ 2 * ‖x - y‖ := by linarith [abs_norm_sub_norm_le x y]

theorem normalize_difference_le (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ≤
      2 * ‖x - y‖ / ‖x‖ :=
  (le_div_iff₀ (norm_pos_iff.mpr hx)).2 (normalize_difference_mul_norm_le x y hy)

theorem normalize_difference_sq_le (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖NormedSpace.normalize x - NormedSpace.normalize y‖ ^ 2 ≤
      4 * ‖x - y‖ ^ 2 / ‖x‖ ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).2
  have h := normalize_difference_mul_norm_le x y hy
  have hs := mul_self_le_mul_self
    (mul_nonneg (norm_nonneg _) (norm_nonneg x)) h
  nlinarith only [hs]

/-- A genuine lower Riesz estimate for every finite signed combination. -/
def UniformLowerRieszBound {ι : Type*} (U : ι → E) (c : ℝ) : Prop :=
  ∀ (s : Finset ι) (a : ι → ℝ),
    c * (∑ i ∈ s, (a i)^2) ≤ ‖∑ i ∈ s, a i • U i‖ ^ 2

theorem pair_lower_of_uniformLowerRieszBound {ι : Type*} (U : ι → E) (c : ℝ)
    (h : UniformLowerRieszBound U c) (i j : ι) (hij : i ≠ j) :
    2 * c ≤ ‖U i - U j‖ ^ 2 := by
  classical
  have hp := h {i, j} (fun k => if k = i then 1 else -1)
  simpa [hij, hij.symm, sub_eq_add_neg, mul_comm] using hp

/-- Arbitrarily close distinct pairs rule out any positive uniform lower
Riesz estimate, even if every vector has norm one. -/
theorem no_uniformLowerRiesz_of_close_pairs {ι : Type*} (U : ι → E)
    (i j : ℕ → ι) (hne : ∀ n, i n ≠ j n)
    (hclose : Tendsto (fun n => ‖U (i n) - U (j n)‖ ^ 2) atTop (𝓝 0)) :
    ¬ ∃ c : ℝ, 0 < c ∧ UniformLowerRieszBound U c := by
  rintro ⟨c, hc, hR⟩
  obtain ⟨n, hn⟩ := (hclose.eventually_lt_const
    (mul_pos (by norm_num : (0 : ℝ) < 2) hc)).exists
  exact not_lt_of_ge (pair_lower_of_uniformLowerRieszBound U c hR _ _ (hne n)) hn

/-- A two-stage cutoff estimate proves a full-sequence limit: first fix a
large cutoff J, and only then let n tend to infinity. -/
theorem tendsto_zero_of_cutoff_bound (u : ℕ → ℝ) (C : ℝ)
    (hu : ∀ n, 0 ≤ u n)
    (hbound : ∀ n J : ℕ, 0 < J →
      u n ≤ C * ((J : ℝ) / ((n : ℝ) + 1) + 1 / (J : ℝ))) :
    Tendsto u atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha (hu n)
  · intro ε hε
    obtain ⟨J, hJ⟩ := exists_nat_gt (max (1 : ℝ) (C / ε))
    have hJ0 : (0 : ℝ) < J := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hJ)
    have hJn : 0 < J := by exact_mod_cast hJ0
    have hCJ : C / (J : ℝ) < ε := by
      apply (div_lt_iff₀ hJ0).2
      have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hJ)
      linarith
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto
        (fun n : ℕ => C * ((J : ℝ) / ((n : ℝ) + 1) + 1 / (J : ℝ)))
        atTop (𝓝 (C / (J : ℝ))) := by
      simpa only [mul_zero, zero_add, mul_one_div, mul_div_assoc] using
        ((ht.const_mul (J : ℝ)).add_const (1 / (J : ℝ))).const_mul C
    filter_upwards [hlim.eventually_lt_const hCJ] with n hn
    exact (hbound n J hJn).trans_lt hn

end RiemannResearch.Analysis.NormalizedPairObstruction
