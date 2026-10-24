import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Absolute variation of nested Hilbert projection observations

Source: fifth Ramanujan transfer program, 24 October 2026.
The exact two-vector increment identity yields a full absolute-variation
tail bound by the product of the two unresolved projection energies.
No saturation or arithmetic target-identification hypothesis is needed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ProjectionVariation
open ExhaustiveWalk
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem nested_increment_pairing (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L) (g x : H) :
    inner ℝ g (L.starProjection x - K.starProjection x) =
      inner ℝ (L.starProjection g - K.starProjection g)
        (L.starProjection x - K.starProjection x) := by
  have hL : L.starProjection (L.starProjection x - K.starProjection x) =
      L.starProjection x - K.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr
      (L.sub_mem (L.starProjection_apply_mem x) (hKL (K.starProjection_apply_mem x)))
  have hcomp : K.starProjection (L.starProjection x) = K.starProjection x :=
    congrArg (fun T : H →L[ℝ] H => T x)
      (Submodule.starProjection_comp_starProjection_of_le hKL)
  have hK : K.starProjection (L.starProjection x - K.starProjection x) = 0 := by
    rw [map_sub, hcomp, Submodule.starProjection_eq_self_iff.mpr
      (K.starProjection_apply_mem x), sub_self]
  rw [inner_sub_left, K.inner_starProjection_left_eq_right,
    L.inner_starProjection_left_eq_right, hL, hK, inner_zero_right, sub_zero]

def increment (v : ι → H) (draw : ℕ → ι) (x : H) (n : ℕ) : H :=
  (walkSpan v draw (n + 1)).starProjection x - (walkSpan v draw n).starProjection x

def observation (v : ι → H) (draw : ℕ → ι) (g x : H) (n : ℕ) : ℝ :=
  inner ℝ g ((walkSpan v draw n).starProjection x)

theorem observation_increment (v : ι → H) (draw : ℕ → ι) (g x : H) (n : ℕ) :
    observation v draw g x (n + 1) - observation v draw g x n =
      inner ℝ (increment v draw g n) (increment v draw x n) := by
  rw [observation, observation, ← inner_sub_right]
  exact nested_increment_pairing _ _ (walkSpan_mono v draw (Nat.le_succ n)) g x

theorem increment_energy_sum (v : ι → H) (draw : ℕ → ι) (x : H) (N M : ℕ) :
    (∑ j ∈ Finset.range M, ‖increment v draw x (j + N)‖ ^ 2) =
      walkError v draw x N - walkError v draw x (M + N) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have h := walkError_step v draw x (M + N)
    change walkError v draw x (M + N) =
      walkError v draw x (M + N + 1) + ‖increment v draw x (M + N)‖ ^ 2 at h
    simpa only [Nat.succ_eq_add_one, Nat.add_right_comm M 1 N] using
      (show walkError v draw x N - walkError v draw x (M + N) +
        ‖increment v draw x (M + N)‖ ^ 2 =
          walkError v draw x N - walkError v draw x (M + N + 1) by linarith)

/-- Full absolute variation over a finite block, with both exact energy decrements. -/
theorem finite_variation_sq_le (v : ι → H) (draw : ℕ → ι) (g x : H) (N M : ℕ) :
    (∑ j ∈ Finset.range M,
      |observation v draw g x (j + N + 1) - observation v draw g x (j + N)|) ^ 2 ≤
        (walkError v draw g N - walkError v draw g (M + N)) *
        (walkError v draw x N - walkError v draw x (M + N)) := by
  have hle : (∑ j ∈ Finset.range M,
      |observation v draw g x (j + N + 1) - observation v draw g x (j + N)|) ≤
      ∑ j ∈ Finset.range M, ‖increment v draw g (j + N)‖ * ‖increment v draw x (j + N)‖ := by
    apply Finset.sum_le_sum
    intro j hj
    rw [observation_increment]
    exact abs_real_inner_le_norm _ _
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range M,
      |observation v draw g x (j + N + 1) - observation v draw g x (j + N)| :=
    Finset.sum_nonneg (fun j hj => abs_nonneg _)
  have hsq := mul_self_le_mul_self hnonneg hle
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range M)
    (fun j => ‖increment v draw g (j + N)‖)
    (fun j => ‖increment v draw x (j + N)‖)
  rw [increment_energy_sum, increment_energy_sum] at hcs
  nlinarith

theorem observation_variation_summable (v : ι → H) (draw : ℕ → ι) (g x : H) (N : ℕ) :
    Summable (fun j =>
      |observation v draw g x (j + N + 1) - observation v draw g x (j + N)|) := by
  apply summable_of_sum_range_le (fun j => abs_nonneg _)
    (c := walkError v draw g N + walkError v draw x N + 1)
  intro M
  have hs := finite_variation_sq_le v draw g x N M
  have hg := walkError_antitone v draw g (Nat.le_add_left N M)
  have hx := walkError_antitone v draw x (Nat.le_add_left N M)
  have hgn : 0 ≤ walkError v draw g (M + N) := sq_nonneg _
  have hxn : 0 ≤ walkError v draw x (M + N) := sq_nonneg _
  have hb := mul_le_mul
    (sub_le_self (walkError v draw g N) hgn)
    (sub_le_self (walkError v draw x N) hxn)
    (sub_nonneg.mpr hx) (show 0 ≤ walkError v draw g N from sq_nonneg _)
  have hsn : 0 ≤ ∑ j ∈ Finset.range M,
      |observation v draw g x (j + N + 1) - observation v draw g x (j + N)| :=
    Finset.sum_nonneg (fun j hj => abs_nonneg _)
  nlinarith [sq_nonneg (walkError v draw g N - walkError v draw x N)]

variable [CompleteSpace H]

/-- The total variation after N is bounded by both remaining approximation capacities. -/
theorem variation_tail_sq_le (v : ι → H) (draw : ℕ → ι)
    (hexhaust : Function.Surjective draw) (g x : H) (N : ℕ) :
    (∑' j, |observation v draw g x (j + N + 1) - observation v draw g x (j + N)|) ^ 2 ≤
      (walkError v draw g N - limitingError v g) *
      (walkError v draw x N - limitingError v x) := by
  have hsum := (observation_variation_summable v draw g x N).hasSum.tendsto_sum_nat
  have hg := (walkError_tendsto v draw hexhaust g).comp (tendsto_add_atTop_nat N)
  have hx := (walkError_tendsto v draw hexhaust x).comp (tendsto_add_atTop_nat N)
  exact le_of_tendsto_of_tendsto (hsum.pow 2)
    ((tendsto_const_nhds.sub hg).mul (tendsto_const_nhds.sub hx))
    (Eventually.of_forall (finite_variation_sq_le v draw g x N))

def coordinateRiesz (ℓ : H →L[ℝ] ℝ) : H := (InnerProductSpace.toDual ℝ H).symm ℓ

theorem coordinate_variation_summable (v : ι → H) (draw : ℕ → ι)
    (x : H) (ℓ : H →L[ℝ] ℝ) (N : ℕ) :
    Summable (fun j => |ℓ ((walkSpan v draw (j + N + 1)).starProjection x) -
      ℓ ((walkSpan v draw (j + N)).starProjection x)|) := by
  simpa only [observation, coordinateRiesz, InnerProductSpace.toDual_symm_apply] using
    observation_variation_summable v draw (coordinateRiesz ℓ) x N

theorem coordinate_variation_tail_sq_le (v : ι → H) (draw : ℕ → ι)
    (hexhaust : Function.Surjective draw) (x : H) (ℓ : H →L[ℝ] ℝ) (N : ℕ) :
    (∑' j, |ℓ ((walkSpan v draw (j + N + 1)).starProjection x) -
      ℓ ((walkSpan v draw (j + N)).starProjection x)|) ^ 2 ≤
      (walkError v draw (coordinateRiesz ℓ) N - limitingError v (coordinateRiesz ℓ)) *
      (walkError v draw x N - limitingError v x) := by
  simpa only [observation, coordinateRiesz, InnerProductSpace.toDual_symm_apply] using
    variation_tail_sq_le v draw hexhaust (coordinateRiesz ℓ) x N

end RiemannResearch.Analysis.ProjectionVariation
