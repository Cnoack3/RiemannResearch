/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ResidueClosureDensity

/-!
# Sampling one fixed arithmetic factor and the full residue closure

Source: user-provided `RH_CRT_Orbit_Exhaustion_and_Doubling_Invariance_2026-09-20(3).md`,
Section 8, and the fixed-factor extension developed in the 9 October 2026 continuation.
Bagchi, Theorem 1, https://arxiv.org/abs/math/0607733, supports the mathematical
RH equivalence in the source. The RH-to-closure direction is not assumed here.

We construct the actual bounded map f(n) ↦ f(a*n), retain its exact physical
weight identity, and prove for each a ≥ 2 that invariance of the full closed
residue span is equivalent to containing the constant and to totality. Invariance
is still an open arithmetic obligation; the endpoint to RH is conditional.
This concerns all residue conductors, not the squarefree-only subspace.
-/

open Filter
open scoped Topology
noncomputable section
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

theorem sampling_weight_identity (a n : ℕ) (ha : 0 < a) :
    positiveWeight n =
      ((a : ℝ)^2 - (a : ℝ) * ((a : ℝ) - 1) / ((n : ℝ) + 1)) *
        positiveWeight (a * n) := by
  by_cases hn : n = 0
  · subst n; norm_num [positiveWeight]
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have haR : (a : ℝ) ≠ 0 := by positivity
    unfold positiveWeight
    push_cast
    field_simp
    ring

theorem sampling_weight_bound (a n : ℕ) (ha : 0 < a) :
    positiveWeight n ≤ (a : ℝ)^2 * positiveWeight (a * n) := by
  have haR : 1 ≤ (a : ℝ) := by exact_mod_cast (show 1 ≤ a by omega)
  rw [sampling_weight_identity a n ha]
  exact mul_le_mul_of_nonneg_right
    (sub_le_self _ (div_nonneg (mul_nonneg (by positivity) (by linarith))
      (by positivity))) (positiveWeight_nonneg _)

private theorem sampled_tsum_le (a : ℕ) (ha : 0 < a) {g : ℕ → ℝ}
    (hg : Summable g) (h0 : ∀ n, 0 ≤ g n) :
    (∑' n, g (a * n)) ≤ ∑' n, g n := by
  have hi : Function.Injective (fun n : ℕ => a * n) := by
    intro x y h
    exact Nat.eq_of_mul_eq_mul_left ha h
  have hs := hg.comp_injective hi
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, g (a * n)) ≤ ∑' n, g n := by
    calc
      _ = ∑ n ∈ (Finset.range N).image (fun k => a * k), g n := by
        rw [Finset.sum_image]
        intro x hx y hy hxy
        exact hi hxy
      _ ≤ _ := hg.sum_le_tsum _ (fun n _ => h0 n)
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat (Eventually.of_forall hb)

theorem argumentSampling_summable (a : ℕ) (ha : 0 < a) (f : ThresholdHilbert) :
    Summable (fun n => positiveWeight n * hilbertSequence f (a * n)^2) := by
  have hi : Function.Injective (fun n : ℕ => a * n) := by
    intro x y h
    exact Nat.eq_of_mul_eq_mul_left ha h
  have hs := (hilbertSequence_square_summable f).comp_injective hi
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
    (fun n => ?_) (hs.mul_left ((a : ℝ)^2))
  simpa only [Function.comp_def, mul_assoc] using
    mul_le_mul_of_nonneg_right (sampling_weight_bound a n ha)
      (sq_nonneg (hilbertSequence f (a * n)))

def hilbertArgumentSampling (a : ℕ) (ha : 0 < a) (f : ThresholdHilbert) :
    ThresholdHilbert :=
  sequenceHilbert (fun n => hilbertSequence f (a * n))
    (argumentSampling_summable a ha f)

@[simp] theorem hilbertArgumentSampling_sequence (a : ℕ) (ha : 0 < a)
    (f : ThresholdHilbert) :
    hilbertSequence (hilbertArgumentSampling a ha f) =
      fun n => hilbertSequence f (a * n) := by
  apply hilbertSequence_sequenceHilbert
  simp

def argumentSamplingLinear (a : ℕ) (ha : 0 < a) :
    ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := hilbertArgumentSampling a ha
  map_add' f g := by
    apply hilbertSequence_injective
    simp only [hilbertArgumentSampling_sequence, hilbertSequence_add]
    rfl
  map_smul' c f := by
    apply hilbertSequence_injective
    simp only [hilbertArgumentSampling_sequence, hilbertSequence_smul]
    rfl

theorem hilbertArgumentSampling_norm_sq_le (a : ℕ) (ha : 0 < a)
    (f : ThresholdHilbert) :
    ‖hilbertArgumentSampling a ha f‖^2 ≤ (a : ℝ)^2 * ‖f‖^2 := by
  rw [hilbert_norm_weighted_sq, hilbertArgumentSampling_sequence,
    hilbert_norm_weighted_sq]
  have hi : Function.Injective (fun n : ℕ => a * n) := by
    intro x y h
    exact Nat.eq_of_mul_eq_mul_left ha h
  have hs := (hilbertSequence_square_summable f).comp_injective hi
  calc
    _ ≤ ∑' n, (a : ℝ)^2 *
        (positiveWeight (a * n) * hilbertSequence f (a * n)^2) :=
      (argumentSampling_summable a ha f).tsum_le_tsum
        (fun n => by
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right (sampling_weight_bound a n ha)
              (sq_nonneg (hilbertSequence f (a * n)))) (hs.mul_left _)
    _ = (a : ℝ)^2 * ∑' n, positiveWeight (a * n) * hilbertSequence f (a * n)^2 :=
      hs.tsum_mul_left _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sampled_tsum_le a ha (hilbertSequence_square_summable f)
        (fun n => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))) (sq_nonneg _)

theorem hilbertArgumentSampling_norm_le (a : ℕ) (ha : 0 < a)
    (f : ThresholdHilbert) :
    ‖hilbertArgumentSampling a ha f‖ ≤ (a : ℝ) * ‖f‖ := by
  have h := hilbertArgumentSampling_norm_sq_le a ha f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg f))).mp
  simpa only [mul_pow] using h

def argumentSamplingContinuous (a : ℕ) (ha : 0 < a) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (argumentSamplingLinear a ha).mkContinuous (a : ℝ)
    (hilbertArgumentSampling_norm_le a ha)

@[simp] theorem argumentSamplingContinuous_apply (a : ℕ) (ha : 0 < a)
    (f : ThresholdHilbert) :
    argumentSamplingContinuous a ha f = hilbertArgumentSampling a ha f := rfl

private theorem sampling_point_norm_sq (n : ℕ) :
    ‖paretoPointHilbert n‖^2 = positiveWeight (n + 1) := by
  rw [← real_inner_self_eq_norm_sq, inner_paretoPoint,
    hilbertGibbsPhysical_paretoPoint, positiveWeight_succ]
  simp

theorem hilbertArgumentSampling_point (a : ℕ) (ha : 0 < a) (n : ℕ) :
    hilbertArgumentSampling a ha (paretoPointHilbert (a * (n + 1) - 1)) =
      paretoPointHilbert n := by
  apply hilbertSequence_injective
  rw [hilbertArgumentSampling_sequence, hilbertSequence_paretoPoint,
    hilbertSequence_paretoPoint]
  funext k
  have ha1 : 1 ≤ a * (n + 1) := by
    have hp : 0 < a * (n + 1) := by positivity
    omega
  have he : a * k = a * (n + 1) - 1 + 1 ↔ k = n + 1 := by
    rw [Nat.sub_add_cancel ha1]
    exact ⟨Nat.eq_of_mul_eq_mul_left ha, fun h => congrArg (a * ·) h⟩
  simp only [paretoPointSequence, he]

/-- The upper bound is sharp; the exact norm is the sampling factor. -/
theorem argumentSamplingContinuous_norm (a : ℕ) (ha : 0 < a) :
    ‖argumentSamplingContinuous a ha‖ = (a : ℝ) := by
  apply le_antisymm
  · exact (argumentSamplingContinuous a ha).opNorm_le_bound (by positivity)
      (hilbertArgumentSampling_norm_le a ha)
  · have hb (n : ℕ) :
        (a : ℝ)^2 - (a : ℝ) * ((a : ℝ) - 1) / ((n : ℝ) + 2) ≤
          ‖argumentSamplingContinuous a ha‖^2 := by
      have h := (argumentSamplingContinuous a ha).le_opNorm
        (paretoPointHilbert (a * (n + 1) - 1))
      have hsq := (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
      rw [mul_pow, argumentSamplingContinuous_apply, hilbertArgumentSampling_point,
        sampling_point_norm_sq, sampling_point_norm_sq] at hsq
      have hi : a * (n + 1) - 1 + 1 = a * (n + 1) :=
        Nat.sub_add_cancel (by
          have hp : 0 < a * (n + 1) := by positivity
          omega)
      rw [hi] at hsq
      have hp : 0 < positiveWeight (a * (n + 1)) := by
        unfold positiveWeight
        positivity
      have hprod := (sampling_weight_identity a (n + 1) ha).symm.le.trans hsq
      norm_num only [Nat.cast_add, Nat.cast_one, add_assoc] at hprod
      nlinarith
    have hd : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
    have hi := tendsto_inv_atTop_zero.comp hd
    have ht : Tendsto (fun n : ℕ =>
        (a : ℝ)^2 - (a : ℝ) * ((a : ℝ) - 1) / ((n : ℝ) + 2))
        atTop (𝓝 ((a : ℝ)^2)) := by
      simpa only [Function.comp_def, mul_zero, sub_zero, div_eq_mul_inv] using
        tendsto_const_nhds.sub (hi.const_mul ((a : ℝ) * ((a : ℝ) - 1)))
    have hsq := le_of_tendsto ht (Eventually.of_forall hb)
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq

def argumentSamplingIterate (a : ℕ) (ha : 0 < a) (k : ℕ)
    (f : ThresholdHilbert) : ThresholdHilbert :=
  (argumentSamplingContinuous a ha : ThresholdHilbert → ThresholdHilbert)^[k] f

@[simp] theorem argumentSamplingIterate_sequence (a : ℕ) (ha : 0 < a)
    (k : ℕ) (f : ThresholdHilbert) :
    hilbertSequence (argumentSamplingIterate a ha k f) =
      fun n => hilbertSequence f (a^k * n) := by
  induction k with
  | zero => simp [argumentSamplingIterate]
  | succ k ih =>
    have he : argumentSamplingIterate a ha (k + 1) f =
        argumentSamplingContinuous a ha (argumentSamplingIterate a ha k f) :=
      Function.iterate_succ_apply' _ _ _
    rw [he, argumentSamplingContinuous_apply, hilbertArgumentSampling_sequence, ih]
    funext n
    simp only [pow_succ, Nat.mul_assoc]

def powerSampledResidue (a : ℕ) (ha : 0 < a) (k : ℕ) : ThresholdHilbert :=
  argumentSamplingIterate a ha k
    (normalizedResidueHilbert (a^k + 1) (by positivity))

@[simp] theorem powerSampledResidue_sequence (a : ℕ) (ha : 0 < a) (k n : ℕ) :
    hilbertSequence (powerSampledResidue a ha k) n =
      residueFraction (a^k + 1) (a^k * n) := by
  simp [powerSampledResidue, normalizedResidueHilbert_sequence]

/-- The reversed orbit converges in the complete physical norm for every fixed a ≥ 2. -/
theorem powerSampledResidue_tendsto_one (a : ℕ) (ha : 2 ≤ a) :
    Tendsto (powerSampledResidue a (by omega)) atTop (𝓝 hilbertOne) := by
  apply hilbert_tendsto_one_of_bounded_coordinates
  · intro k n
    rw [powerSampledResidue_sequence]
    unfold residueFraction
    constructor
    · positivity
    · apply le_of_lt
      apply (div_lt_one (by positivity : (0 : ℝ) < ((a^k + 1 : ℕ) : ℝ))).mpr
      exact_mod_cast Nat.mod_lt (a^k * n) (by positivity : 0 < a^k + 1)
  · have haR : (1 : ℝ) < a := by exact_mod_cast (show 1 < a by omega)
    have hd : Tendsto (fun k : ℕ => ((a^k + 1 : ℕ) : ℝ)) atTop atTop := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
        (tendsto_pow_atTop_atTop_of_one_lt haR).atTop_add
          (tendsto_const_nhds (x := (1 : ℝ)))
    have hi := tendsto_inv_atTop_zero.comp hd
    intro n hn
    have hl : Tendsto (fun k : ℕ => 1 - (n : ℝ) * ((a^k + 1 : ℕ) : ℝ)⁻¹)
        atTop (𝓝 1) := by
      simpa only [Function.comp_def, mul_zero, sub_zero] using
        tendsto_const_nhds.sub (hi.const_mul (n : ℝ))
    apply (tendsto_congr' ?_).mpr hl
    filter_upwards [hd.eventually (eventually_gt_atTop (n : ℝ))] with k hk
    rw [powerSampledResidue_sequence, reverseResidue_head _ _ hn (by exact_mod_cast hk)]
    rw [div_eq_mul_inv]

namespace CoefficientStabilization

def ArgumentSamplingInvariant (a : ℕ) (ha : 0 < a) : Prop :=
  ∀ f : ThresholdHilbert, f ∈ closedSpace →
    hilbertArgumentSampling a ha f ∈ closedSpace

theorem argumentSamplingInvariant_iff_generators (a : ℕ) (ha : 0 < a) :
    ArgumentSamplingInvariant a ha ↔
      ∀ d : ℕ, ∀ hd : 2 ≤ d,
        hilbertArgumentSampling a ha (normalizedResidueHilbert d (by omega)) ∈ closedSpace := by
  constructor
  · intro h d hd
    exact h _ (normalizedResidue_mem_closedSpace _ _)
  · intro h f hf
    let T : Submodule ℝ ThresholdHilbert :=
      closedSpace.comap (argumentSamplingContinuous a ha).toLinearMap
    have hspan : Submodule.span ℝ (Set.range residueAtom) ≤ T := by
      apply Submodule.span_le.mpr
      rintro g ⟨i, rfl⟩
      exact h (i + 2) (by omega)
    have hclosed : IsClosed (T : Set ThresholdHilbert) :=
      (Submodule.isClosed_topologicalClosure _).preimage
        (argumentSamplingContinuous a ha).continuous
    exact ((Submodule.span ℝ (Set.range residueAtom)).topologicalClosure_minimal
      hspan hclosed) hf

theorem argumentSamplingIterate_mem (a : ℕ) (ha : 0 < a)
    (h : ArgumentSamplingInvariant a ha) (k : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ closedSpace) : argumentSamplingIterate a ha k f ∈ closedSpace := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    have he : argumentSamplingIterate a ha (k + 1) f =
        argumentSamplingContinuous a ha (argumentSamplingIterate a ha k f) :=
      Function.iterate_succ_apply' _ _ _
    rw [he, argumentSamplingContinuous_apply]
    exact h _ ih

theorem hilbertOne_mem_of_argumentSampling (a : ℕ) (ha : 2 ≤ a)
    (h : ArgumentSamplingInvariant a (by omega)) : hilbertOne ∈ closedSpace := by
  have hv (k : ℕ) : powerSampledResidue a (by omega) k ∈ closedSpace :=
    argumentSamplingIterate_mem a (by omega) h k _
      (normalizedResidue_mem_closedSpace _ _)
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (powerSampledResidue_tendsto_one a ha) (Eventually.of_forall hv)

/-- Exact closure equivalence, independent of the unformalized RH-to-closure converse. -/
theorem argumentSamplingInvariant_iff_one_mem (a : ℕ) (ha : 2 ≤ a) :
    ArgumentSamplingInvariant a (by omega) ↔ hilbertOne ∈ closedSpace := by
  constructor
  · exact hilbertOne_mem_of_argumentSampling a ha
  · intro h f hf
    rw [closedSpace_eq_top_iff_one_mem.mpr h]
    trivial

theorem argumentSamplingInvariant_iff_total (a : ℕ) (ha : 2 ≤ a) :
    ArgumentSamplingInvariant a (by omega) ↔ closedSpace = ⊤ := by
  rw [argumentSamplingInvariant_iff_one_mem a ha, closedSpace_eq_top_iff_one_mem]

/-- Conditional research reduction: fixed-factor invariance is still Open. -/
theorem riemannHypothesis_of_argumentSampling (a : ℕ) (ha : 2 ≤ a)
    (h : ArgumentSamplingInvariant a (by omega)) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (hilbertOne_mem_of_argumentSampling a ha h))

end CoefficientStabilization
end RiemannResearch.RH.Pareto
