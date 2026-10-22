import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Summable tails of nested actual projections

The finite projection identity is reused from ExhaustiveProjectionWalk.
The source-radius strategy follows Section 3 of
RH_Actual_Arithmetic_Advances_2026-10-07.pdf; finite Cauchy preserves a
coefficient-one budget rather than a factor-two bound.  A summable
bound on the old projection's leakage through the next cutoff gives a
summable bound on the next actual projection's complete tail.  The sharp
total budget keeps coefficient one on the surviving projection-energy drop.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ProjectionTailSummability
open RiemannResearch.Analysis.ExhaustiveWalk

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The projection displacement squares telescope exactly on every nested
chain, with the final residual square retained. -/
theorem sum_projection_step_norm_sq
    (W : ℕ → Submodule ℝ H) [∀ n, (W n).HasOrthogonalProjection]
    (hW : Monotone W) (x : H) (J : ℕ) :
    (∑ j ∈ Finset.range J,
      ‖(W (j+1)).starProjection x - (W j).starProjection x‖ ^ 2) =
        ‖x - (W 0).starProjection x‖ ^ 2 -
          ‖x - (W J).starProjection x‖ ^ 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      have he := nested_projection_energy (W J) (W (J+1))
        (hW (Nat.le_succ J)) x
      linarith only [he]

/-- Finite scalar Minkowski in square form. No sign restriction on the
cross terms is imposed or used to erase a correction. -/
theorem sum_sq_add_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, (a i + b i) ^ 2) ≤
      (Real.sqrt (∑ i ∈ s, a i ^ 2) +
        Real.sqrt (∑ i ∈ s, b i ^ 2)) ^ 2 := by
  have hA : 0 ≤ ∑ i ∈ s, a i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ ∑ i ∈ s, b i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => a i * b i) (f := fun i => a i ^ 2)
    (g := fun i => b i ^ 2)
    (by intro i hi; positivity)
    (by intro i hi; positivity)
    (by intro i hi; exact le_of_eq (by ring))
  have hprod : 0 ≤ Real.sqrt (∑ i ∈ s, a i ^ 2) *
      Real.sqrt (∑ i ∈ s, b i ^ 2) := by positivity
  have hcross : (∑ i ∈ s, a i * b i) ≤
      Real.sqrt (∑ i ∈ s, a i ^ 2) *
        Real.sqrt (∑ i ∈ s, b i ^ 2) := by
    have hsquare : |∑ i ∈ s, a i * b i| ^ 2 ≤
        (Real.sqrt (∑ i ∈ s, a i ^ 2) *
          Real.sqrt (∑ i ∈ s, b i ^ 2)) ^ 2 := by
      rw [sq_abs, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
      exact hcs
    exact (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) hprod).mp hsquare)
  have hexpand : (∑ i ∈ s, (a i + b i) ^ 2) =
      (∑ i ∈ s, a i ^ 2) + 2 * (∑ i ∈ s, a i * b i) +
        (∑ i ∈ s, b i ^ 2) := by
    calc
      _ = ∑ i ∈ s, (a i ^ 2 + 2 * (a i * b i) + b i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexpand, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  nlinarith only [hcross]

/-- Every finite total of complete actual tails obeys the square-root
budget. The defect floor is geometric; it need not be zero. -/
theorem projection_tail_sum_le
    (W : ℕ → Submodule ℝ H) [∀ n, (W n).HasOrthogonalProjection]
    (hW : Monotone W) (x : H)
    (T : ℕ → H →ₗ[ℝ] H) (hT : ∀ n z, ‖T n z‖ ≤ ‖z‖)
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n) (hR : Summable R)
    (hleak : ∀ n, ‖T n ((W n).starProjection x)‖ ^ 2 ≤ R n)
    (δ : ℝ) (hδ : ∀ n, δ ≤ ‖x - (W n).starProjection x‖ ^ 2)
    (J : ℕ) :
    (∑ j ∈ Finset.range J, ‖T j ((W (j+1)).starProjection x)‖ ^ 2) ≤
      (Real.sqrt (‖x - (W 0).starProjection x‖ ^ 2 - δ) +
        Real.sqrt (∑' j, R j)) ^ 2 := by
  let a : ℕ → ℝ := fun j =>
    ‖(W (j+1)).starProjection x - (W j).starProjection x‖
  let b : ℕ → ℝ := fun j => ‖T j ((W j).starProjection x)‖
  have hbound (j : ℕ) : ‖T j ((W (j+1)).starProjection x)‖ ≤ a j + b j := by
    have he : T j ((W (j+1)).starProjection x) =
        T j ((W (j+1)).starProjection x - (W j).starProjection x) +
          T j ((W j).starProjection x) := by rw [map_sub]; abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (hT j _) le_rfl)
  have hsum : (∑ j ∈ Finset.range J,
      ‖T j ((W (j+1)).starProjection x)‖ ^ 2) ≤
      (∑ j ∈ Finset.range J, (a j + b j) ^ 2) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (sq_le_sq₀ (norm_nonneg _) (by dsimp [a, b]; positivity)).mpr (hbound j)
  have hA : (∑ j ∈ Finset.range J, a j ^ 2) ≤
      ‖x - (W 0).starProjection x‖ ^ 2 - δ := by
    rw [show (∑ j ∈ Finset.range J, a j ^ 2) =
      ‖x - (W 0).starProjection x‖ ^ 2 -
        ‖x - (W J).starProjection x‖ ^ 2 from
          sum_projection_step_norm_sq W hW x J]
    linarith only [hδ J]
  have hB : (∑ j ∈ Finset.range J, b j ^ 2) ≤ ∑' j, R j := by
    exact (Finset.sum_le_sum (fun j hj => hleak j)).trans
      (hR.sum_le_tsum (Finset.range J) (fun j hj => hR0 j))
  have hsqrt := add_le_add (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
  exact (hsum.trans (sum_sq_add_le (Finset.range J) a b)).trans
    ((sq_le_sq₀ (by positivity) (by positivity)).mpr hsqrt)

/-- Summability of the complete actual tail squares follows from a
discharged summable leakage bound, even if the limit defect is positive. -/
theorem projection_tail_summable
    (W : ℕ → Submodule ℝ H) [∀ n, (W n).HasOrthogonalProjection]
    (hW : Monotone W) (x : H)
    (T : ℕ → H →ₗ[ℝ] H) (hT : ∀ n z, ‖T n z‖ ≤ ‖z‖)
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n) (hR : Summable R)
    (hleak : ∀ n, ‖T n ((W n).starProjection x)‖ ^ 2 ≤ R n)
    (δ : ℝ) (hδ : ∀ n, δ ≤ ‖x - (W n).starProjection x‖ ^ 2) :
    Summable (fun j => ‖T j ((W (j+1)).starProjection x)‖ ^ 2) := by
  apply summable_of_sum_range_le (fun j => sq_nonneg _)
  exact projection_tail_sum_le W hW x T hT R hR0 hR hleak δ hδ

/-- The infinite total has the same sharp budget as each finite total. -/
theorem projection_tail_tsum_le
    (W : ℕ → Submodule ℝ H) [∀ n, (W n).HasOrthogonalProjection]
    (hW : Monotone W) (x : H)
    (T : ℕ → H →ₗ[ℝ] H) (hT : ∀ n z, ‖T n z‖ ≤ ‖z‖)
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n) (hR : Summable R)
    (hleak : ∀ n, ‖T n ((W n).starProjection x)‖ ^ 2 ≤ R n)
    (δ : ℝ) (hδ : ∀ n, δ ≤ ‖x - (W n).starProjection x‖ ^ 2) :
    (∑' j, ‖T j ((W (j+1)).starProjection x)‖ ^ 2) ≤
      (Real.sqrt (‖x - (W 0).starProjection x‖ ^ 2 - δ) +
        Real.sqrt (∑' j, R j)) ^ 2 := by
  apply Real.tsum_le_of_sum_range_le (fun j => sq_nonneg _)
  exact projection_tail_sum_le W hW x T hT R hR0 hR hleak δ hδ

end RiemannResearch.Analysis.ProjectionTailSummability
