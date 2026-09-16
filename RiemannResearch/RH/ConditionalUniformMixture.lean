import RiemannResearch.RH.ArithmeticCumulativeEnergy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Exact uniform-interval mixing and conditioning identities

The positive-integer mixing weights have total mass one and give the exact
NB/Pareto marginal when the conditional law is uniform on `1,...,t`.
The finite bias/variance and optimizer compatibility identities retain all
conditional-mean contributions. No uniform arithmetic energy bound is claimed.
-/

namespace RiemannResearch.RH.ArithmeticCumulative
noncomputable section
open scoped BigOperators Topology
open Filter

def mixtureWeight (t : ℕ) : ℝ := 2 / (((t : ℝ) + 1) * ((t : ℝ) + 2))

theorem mixtureWeight_nonneg (t : ℕ) : 0 ≤ mixtureWeight t := by
  unfold mixtureWeight
  positivity

/-- The marginal contribution from a uniform interval telescopes exactly. -/
theorem mixture_density_step (n : ℕ) (hn : 0 < n) :
    mixtureWeight n / (n : ℝ) = weight n - weight (n + 1) := by
  unfold mixtureWeight weight
  push_cast
  have h0 : (n : ℝ) ≠ 0 := by positivity
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem weight_partial_sum (n R : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range R, weight (n + k)) =
      1 / (n : ℝ) - 1 / ((n + R : ℕ) : ℝ) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, weight_eq_sub (n + R) (by omega)]
    push_cast
    ring

theorem weight_tendsto_zero : Tendsto weight atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      h1.comp (Filter.tendsto_add_atTop_nat 1)
  convert h1.mul h2 using 1
  · funext n
    simp [weight, div_eq_mul_inv, mul_inv_rev, mul_comm]
  · simp

theorem hasSum_weight_from (n : ℕ) (hn : 0 < n) :
    HasSum (fun k : ℕ => weight (n + k)) (1 / (n : ℝ)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => weight_nonneg _) _).2
  simp_rw [weight_partial_sum n _ hn]
  have hi : Tendsto (fun k : ℕ => 1 / ((n + k : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Nat.add_comm] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat n)
  simpa only [sub_zero] using tendsto_const_nhds.sub hi

/-- The proposed distribution of the latent interval endpoint is normalized. -/
theorem hasSum_mixtureWeight : HasSum (fun k : ℕ => mixtureWeight (k + 1)) 1 := by
  have h := (hasSum_weight_from 2 (by norm_num)).mul_left 2
  have he : (fun k : ℕ => mixtureWeight (k + 1)) =
      (fun k : ℕ => 2 * weight (2 + k)) := by
    funext k
    unfold mixtureWeight weight
    push_cast
    ring
  rw [he]
  norm_num at h
  exact h

theorem mixture_density_partial_sum (n R : ℕ) (hn : 0 < n) :
    (∑ k ∈ Finset.range R, mixtureWeight (n + k) / ((n + k : ℕ) : ℝ)) =
      weight n - weight (n + R) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, mixture_density_step (n + R) (by omega)]
    simp only [Nat.add_assoc]
    ring

/-- Exact infinite marginal identity: mixing uniform intervals gives the NB weight. -/
theorem hasSum_uniform_mixture_marginal (n : ℕ) (hn : 0 < n) :
    HasSum (fun k : ℕ => mixtureWeight (n + k) / ((n + k : ℕ) : ℝ)) (weight n) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun k => div_nonneg (mixtureWeight_nonneg _) (Nat.cast_nonneg _)) _).2
  simp_rw [mixture_density_partial_sum n _ hn]
  have hw : Tendsto (fun k => weight (n + k)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Nat.add_comm] using weight_tendsto_zero.comp (Filter.tendsto_add_atTop_nat n)
  simpa only [sub_zero] using tendsto_const_nhds.sub hw

theorem uniform_mixture_marginal (n : ℕ) (hn : 0 < n) :
    (∑' k : ℕ, mixtureWeight (n + k) / ((n + k : ℕ) : ℝ)) = weight n :=
  (hasSum_uniform_mixture_marginal n hn).tsum_eq

/-- Exact finite bias/variance identity; normalization and the actual mean are explicit. -/
theorem finite_bias_variance {ι : Type*} (s : Finset ι) (q F : ι → ℝ) (m c : ℝ)
    (hq : ∑ i ∈ s, q i = 1) (hm : ∑ i ∈ s, q i * F i = m) :
    (∑ i ∈ s, q i * (F i - c) ^ 2) =
      (∑ i ∈ s, q i * (F i - m) ^ 2) + (m - c) ^ 2 := by
  have hz : (∑ i ∈ s, q i * (F i - m)) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hq, hm]
    ring
  calc
    _ = ∑ i ∈ s, (q i * (F i - m) ^ 2 +
        2 * (m - c) * (q i * (F i - m)) + (m - c) ^ 2 * q i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hz, hq]
      ring

/-- The conditional-mean term survives taking a mixture of conditional laws. -/
theorem finite_mixture_bias_variance {Z ι : Type*}
    (z : Finset Z) (s : Finset ι) (π : Z → ℝ) (q : Z → ι → ℝ)
    (F : ι → ℝ) (m : Z → ℝ) (c : ℝ)
    (hq : ∀ a ∈ z, ∑ i ∈ s, q a i = 1)
    (hm : ∀ a ∈ z, ∑ i ∈ s, q a i * F i = m a) :
    (∑ a ∈ z, π a * ∑ i ∈ s, q a i * (F i - c) ^ 2) =
      ∑ a ∈ z, π a * ((∑ i ∈ s, q a i * (F i - m a) ^ 2) + (m a - c) ^ 2) := by
  apply Finset.sum_congr rfl
  intro a ha
  rw [finite_bias_variance s (q a) F (m a) c (hq a ha) (hm a ha)]

/-- Normal equations give the exact cost of using a common, nonoptimal correction. -/
theorem optimizer_compatibility_identity {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e localCorrection commonCorrection : E)
    (horth : inner ℝ (e - localCorrection) (commonCorrection - localCorrection) = 0) :
    ‖e - commonCorrection‖ ^ 2 = ‖e - localCorrection‖ ^ 2 +
      ‖commonCorrection - localCorrection‖ ^ 2 := by
  have he : e - commonCorrection =
      (e - localCorrection) - (commonCorrection - localCorrection) := by abel
  rw [he, norm_sub_sq_real, horth]
  ring

/-- The compatibility contribution is nonnegative, not a discardable cancellation. -/
theorem local_optimizer_lower_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e localCorrection commonCorrection : E)
    (horth : inner ℝ (e - localCorrection) (commonCorrection - localCorrection) = 0) :
    ‖e - localCorrection‖ ^ 2 ≤ ‖e - commonCorrection‖ ^ 2 := by
  rw [optimizer_compatibility_identity e localCorrection commonCorrection horth]
  exact le_add_of_nonneg_right (sq_nonneg _)

end
end RiemannResearch.RH.ArithmeticCumulative
