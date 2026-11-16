import RiemannResearch.LinearAlgebra.WeightedGreenInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Reciprocal-max Brownian Green kernel with its exact boundary

Source: Christian Noack, *growing_degree_ridge_no_go.pdf*, Section 14.2,
equations (14.13)--(14.14), Drive file 1p5qy1xBllrTpwe96tm6ee2fAcF36IOvK.
The source motivates the kernel and cumulative-charge energy. This file
specializes the existing weighted Green calculus and adds its right inverse
and inverse Dirichlet energy. In a finite truncation the terminal weight is
1/N, not 1/(N(N+1)); dropping it changes the kernel.

No Mellin integral interchange, CRT compatibility, or uniform arithmetic
observability estimate is assumed or claimed here.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.WeightedGreen

theorem tail_telescope (N : ℕ) (v : ℕ → ℝ) (i : ℕ) (hi : i ≤ N) :
    tail N (fun k => v k - v (k + 1)) i = v i - v N := by
  induction N generalizing i with
  | zero =>
    have hi0 : i = 0 := by omega
    subst i
    simp [tail]
  | succ N ih =>
    by_cases hiN : i ≤ N
    · have hsplit :
          tail (N + 1) (fun k => v k - v (k + 1)) i =
          tail N (fun k => v k - v (k + 1)) i + (v N - v (N + 1)) := by
        simp [tail, Finset.sum_range_succ, hiN]
      rw [hsplit, ih i hiN]
      ring
    · have hiN' : i = N + 1 := by omega
      subst i
      rw [tail_right_boundary]
      ring

theorem prefix_initialDifference (v : ℕ → ℝ) (i : ℕ) :
    greenPrefix (initialDifference v) i = v i := by
  induction i with
  | zero => simp [greenPrefix, initialDifference]
  | succ i ih =>
    have hsplit : greenPrefix (initialDifference v) (i + 1) =
        greenPrefix (initialDifference v) i + initialDifference v (i + 1) := by
      simp [greenPrefix, Finset.sum_range_succ]
    rw [hsplit, ih]
    simp [initialDifference]

/-- The missing right inverse holds with the actual right boundary retained. -/
theorem applyGreen_applyInverse (N : ℕ) (w y : ℕ → ℝ)
    (hw : ∀ k, k < N → w k ≠ 0) (hy : y N = 0)
    (i : ℕ) (hi : i ≤ N) :
    applyGreen N w (applyInverse w y) i = y i := by
  have hterm (k : ℕ) (hk : k < N) :
      w k * greenPrefix (applyInverse w y) k = y k - y (k + 1) := by
    change w k * greenPrefix (initialDifference (flux w y)) k = y k - y (k + 1)
    rw [prefix_initialDifference]
    unfold flux
    field_simp [hw k hk]
  calc
    _ = tail N (fun k => y k - y (k + 1)) i := by
      unfold applyGreen tail
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only
      rw [hterm k (Finset.mem_range.mp hk)]
    _ = y i := by rw [tail_telescope N y i hi, hy, sub_zero]

/-- Exact inverse energy, for every prescribed potential with zero boundary. -/
theorem inverse_dirichlet_identity (N : ℕ) (w y : ℕ → ℝ)
    (hw : ∀ k, k < N → w k ≠ 0) (hy : y N = 0) :
    (∑ i ∈ Finset.range N, y i * applyInverse w y i) =
      ∑ i ∈ Finset.range N, (y i - y (i + 1)) ^ 2 / w i := by
  calc
    _ = ∑ i ∈ Finset.range N,
        applyInverse w y i * applyGreen N w (applyInverse w y) i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [applyGreen_applyInverse N w y hw hy i (by simpa using (Finset.mem_range.mp hi).le)]
      ring
    _ = ∑ i ∈ Finset.range N,
        (applyGreen N w (applyInverse w y) i -
          applyGreen N w (applyInverse w y) (i + 1)) ^ 2 / w i :=
      green_dirichlet_identity N w (applyInverse w y) hw
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [applyGreen_applyInverse N w y hw hy i (by omega),
        applyGreen_applyInverse N w y hw hy (i + 1) (by omega)]

end RiemannResearch.LinearAlgebra.WeightedGreen

namespace RiemannResearch.LinearAlgebra.ReciprocalMaxGreen
open WeightedGreen

def time (N i : ℕ) : ℝ := if i < N then 1 / ((i : ℝ) + 1) else 0

def weight (N i : ℕ) : ℝ := time N i - time N (i + 1)

theorem weight_interior (N i : ℕ) (hi : i + 1 < N) :
    weight N i = 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
  have hi' : i < N := by omega
  have h1 : (i : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (i : ℝ) + 2 ≠ 0 := by positivity
  simp only [weight, time, if_pos hi, if_pos hi', Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem weight_boundary (N : ℕ) :
    weight (N + 1) N = 1 / ((N : ℝ) + 1) := by
  simp [weight, time]

theorem weight_pos (N i : ℕ) (hi : i < N) : 0 < weight N i := by
  by_cases hnext : i + 1 < N
  · rw [weight_interior N i hnext]
    positivity
  · have hN : N = i + 1 := by omega
    subst N
    rw [weight_boundary]
    positivity

/-- The finite Green matrix is exactly 1/max(m,n), with one-based m,n. -/
theorem kernel_eq_reciprocal_max (N i j : ℕ) (hi : i < N) (hj : j < N) :
    kernel N (weight N) i j = 1 / ((max i j : ℕ) + 1 : ℝ) := by
  unfold kernel weight
  rw [tail_telescope N (time N) (max i j) (by omega)]
  simp [time, max_lt_iff.mpr ⟨hi, hj⟩]

/-- Finite cumulative-charge identity, including the entire terminal tail. -/
theorem brownian_energy (N : ℕ) (c : ℕ → ℝ) :
    (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
      c i * c j / ((max i j : ℕ) + 1 : ℝ)) =
      (∑ k ∈ Finset.range N,
        greenPrefix c k ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) +
      greenPrefix c N ^ 2 / ((N : ℝ) + 1) := by
  calc
    _ = ∑ i ∈ Finset.range (N + 1),
        c i * applyGreen (N + 1) (weight (N + 1)) c i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [applyGreen_eq_kernel_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [kernel_eq_reciprocal_max _ _ _ (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
      ring
    _ = ∑ k ∈ Finset.range (N + 1),
        weight (N + 1) k * greenPrefix c k * greenPrefix c k :=
      green_bilinear_identity _ _ _ _
    _ = _ := by
      rw [Finset.sum_range_succ, weight_boundary]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        rw [weight_interior _ _ (by have := Finset.mem_range.mp hk; omega)]
        ring
      · ring

/-- Both inverse identities are available for the complete Brownian matrix. -/
theorem brownian_inverse (N : ℕ) (c : ℕ → ℝ) (i : ℕ) (hi : i < N) :
    applyInverse (weight N) (applyGreen N (weight N) c) i = c i :=
  applyInverse_applyGreen N (weight N) c (fun k hk => (weight_pos N k hk).ne') i hi

/-- The precision energy has explicit nearest-neighbor conductances and boundary. -/
theorem brownian_inverse_energy (N : ℕ) (y : ℕ → ℝ) (hy : y (N + 1) = 0) :
    (∑ i ∈ Finset.range (N + 1), y i * applyInverse (weight (N + 1)) y i) =
      (∑ i ∈ Finset.range N,
        ((i : ℝ) + 1) * ((i : ℝ) + 2) * (y i - y (i + 1)) ^ 2) +
      ((N : ℝ) + 1) * y N ^ 2 := by
  rw [inverse_dirichlet_identity _ _ _ (fun i hi => (weight_pos _ _ hi).ne') hy,
    Finset.sum_range_succ, weight_boundary, hy]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [weight_interior _ _ (by have := Finset.mem_range.mp hi; omega)]
    simp only [one_div, div_eq_mul_inv, one_mul, inv_inv]
    ring
  · simp only [sub_zero, one_div, div_eq_mul_inv, one_mul, inv_inv]
    ring

end RiemannResearch.LinearAlgebra.ReciprocalMaxGreen
