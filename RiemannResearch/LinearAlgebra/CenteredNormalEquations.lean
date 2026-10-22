import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Centered finite normal equations and Schur information

Source: the user's Q-residue Gram calculation and standard rank-one linear
algebra. No novelty is asserted for these finite identities.
The statements use solutions of finite linear systems and do not silently
assume that a totalized inverse is invertible. Information is independent
of the solution even for redundant frames.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.CenteredNormalEquations

variable {ι : Type*} [Fintype ι]

def dot (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

def action (A : ι → ι → ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, A i j * x j

def quadratic (A : ι → ι → ℝ) (x : ι → ℝ) : ℝ := dot x (action A x)

def rankOneAdd (C : ι → ι → ℝ) (b : ι → ℝ) (i j : ι) : ℝ :=
  C i j + b i * b j

theorem dot_comm (x y : ι → ℝ) : dot x y = dot y x := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem dot_div (b u : ι → ℝ) (a : ℝ) :
    dot b (fun i => u i / a) = dot b u / a := by
  unfold dot
  calc
    _ = ∑ i, (b i * u i) / a := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [Finset.sum_div]

theorem action_div (C : ι → ι → ℝ) (u : ι → ℝ) (a : ℝ) (i : ι) :
    action C (fun j => u j / a) i = action C u i / a := by
  exact dot_div (C i) u a

theorem action_rankOneAdd (C : ι → ι → ℝ) (b u : ι → ℝ) (i : ι) :
    action (rankOneAdd C b) u i = action C u i + b i * dot b u := by
  unfold action rankOneAdd dot
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem quadratic_rankOneAdd (C : ι → ι → ℝ) (b u : ι → ℝ) :
    quadratic (rankOneAdd C b) u = quadratic C u + (dot b u)^2 := by
  simp only [quadratic, dot, action_rankOneAdd, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The covariance solution supplies the Gram solution by one scalar division. -/
theorem normalized_normal_equations (C : ι → ι → ℝ) (b u : ι → ℝ)
    (hu : ∀ i, action C u i = b i) (hden : 1 + dot b u ≠ 0) (i : ι) :
    action (rankOneAdd C b) (fun j => u j / (1 + dot b u)) i = b i := by
  rw [action_div, action_rankOneAdd, hu]
  field_simp [hden]
  <;> ring

theorem normalized_captured_energy (b u : ι → ℝ) :
    dot b (fun i => u i / (1 + dot b u)) = dot b u / (1 + dot b u) :=
  dot_div b u _

theorem normalized_residual_energy (b u : ι → ℝ)
    (hden : 1 + dot b u ≠ 0) :
    1 - dot b (fun i => u i / (1 + dot b u)) = 1 / (1 + dot b u) := by
  rw [dot_div]
  field_simp [hden]
  <;> ring

/-- A positive-error Gram solution supplies a covariance solution. -/
theorem covariance_of_gram_solution (C : ι → ι → ℝ) (b c : ι → ℝ)
    (hc : ∀ i, action (rankOneAdd C b) c i = b i)
    (he : 1 - dot b c ≠ 0) (i : ι) :
    action C (fun j => c j / (1 - dot b c)) i = b i := by
  have hi := hc i
  rw [action_rankOneAdd] at hi
  have hv : action C c i = b i * (1 - dot b c) := by nlinarith [hi]
  rw [action_div, hv]
  field_simp [he]
  <;> ring

/-- Finite information is nonnegative whenever C is positive semidefinite. -/
theorem information_nonneg (C : ι → ι → ℝ) (b u : ι → ℝ)
    (hC : ∀ x, 0 ≤ quadratic C x) (hu : ∀ i, action C u i = b i) :
    0 ≤ dot b u := by
  have he : quadratic C u = dot b u := by
    unfold quadratic
    rw [show action C u = b from funext hu, dot_comm]
  rw [← he]
  exact hC u

theorem information_denominator_pos (C : ι → ι → ℝ) (b u : ι → ℝ)
    (hC : ∀ x, 0 ≤ quadratic C x) (hu : ∀ i, action C u i = b i) :
    0 < 1 + dot b u := by
  have h := information_nonneg C b u hC hu
  linarith

theorem dot_action_symm (C : ι → ι → ℝ)
    (hC : ∀ i j, C i j = C j i) (x y : ι → ℝ) :
    dot x (action C y) = dot y (action C x) := by
  unfold dot action
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [hC i j]
  ring

/-- Reciprocity needed for the block covariance update. -/
theorem solve_reciprocity (C : ι → ι → ℝ) (b k u z : ι → ℝ)
    (hC : ∀ i j, C i j = C j i)
    (hu : ∀ i, action C u i = b i) (hz : ∀ i, action C z i = k i) :
    dot b z = dot k u := by
  rw [dot_comm b z, ← show action C u = b from funext hu,
    dot_action_symm C hC z u, show action C z = k from funext hz,
    dot_comm u k]

/-- Information is independent of the solution, even for redundant frames. -/
theorem information_eq_of_solutions (C : ι → ι → ℝ) (b u v : ι → ℝ)
    (hC : ∀ i j, C i j = C j i)
    (hu : ∀ i, action C u i = b i) (hv : ∀ i, action C v i = b i) :
    dot b u = dot b v :=
  (solve_reciprocity C b b u v hC hu hv).symm

theorem dot_sub_smul_right (x y z : ι → ℝ) (a : ℝ) :
    dot x (fun i => y i - a * z i) = dot x y - a * dot x z := by
  unfold dot
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem dot_sub_smul_left (x y z : ι → ℝ) (a : ℝ) :
    dot (fun i => x i - a * y i) z = dot x z - a * dot y z := by
  rw [dot_comm, dot_sub_smul_right, dot_comm z x, dot_comm z y]

theorem action_sub_smul (C : ι → ι → ℝ) (x y : ι → ℝ) (a : ℝ) (i : ι) :
    action C (fun j => x j - a * y j) i = action C x i - a * action C y i :=
  dot_sub_smul_right (C i) x y a

/-- Completing the square with a solution of the centered normal equations. -/
theorem quadratic_sub_solution (C : ι → ι → ℝ) (b u a : ι → ℝ) (t : ℝ)
    (hC : ∀ i j, C i j = C j i) (hu : ∀ i, action C u i = b i) :
    quadratic C (fun i => a i - t * u i) =
      quadratic C a - 2 * t * dot b a + t^2 * dot b u := by
  have hCa : action C (fun i => a i - t * u i) =
      fun i => action C a i - t * b i := by
    funext i
    rw [action_sub_smul, hu]
  have hcross : dot u (action C a) = dot a b := by
    rw [dot_action_symm C hC u a, show action C u = b from funext hu]
  unfold quadratic
  rw [hCa, dot_sub_smul_right, dot_sub_smul_left,
    dot_sub_smul_left, hcross, dot_comm a b, dot_comm u b]
  ring

/-- Exact mean-one variance decomposition, retaining the nonnegative remainder. -/
theorem mean_one_variance_decomposition (C : ι → ι → ℝ) (b u a : ι → ℝ)
    (hC : ∀ i j, C i j = C j i) (hu : ∀ i, action C u i = b i)
    (ha : dot b a = 1) (hT : dot b u ≠ 0) :
    quadratic C a = 1 / dot b u +
      quadratic C (fun i => a i - (1 / dot b u) * u i) := by
  rw [quadratic_sub_solution C b u a (1 / dot b u) hC hu, ha]
  field_simp [hT]
  <;> ring

theorem mean_one_variance_lower_bound (C : ι → ι → ℝ) (b u a : ι → ℝ)
    (hsymm : ∀ i j, C i j = C j i)
    (hC : ∀ x, 0 ≤ quadratic C x) (hu : ∀ i, action C u i = b i)
    (ha : dot b a = 1) (hT : dot b u ≠ 0) :
    1 / dot b u ≤ quadratic C a := by
  rw [mean_one_variance_decomposition C b u a hsymm hu ha hT]
  exact le_add_of_nonneg_right (hC _)

theorem mean_one_normalization (b u : ι → ℝ) (hT : dot b u ≠ 0) :
    dot b (fun i => u i / dot b u) = 1 := by
  rw [dot_div, div_self hT]

theorem mean_one_normalized_variance (C : ι → ι → ℝ) (b u : ι → ℝ)
    (hu : ∀ i, action C u i = b i) (hT : dot b u ≠ 0) :
    quadratic C (fun i => u i / dot b u) = 1 / dot b u := by
  have ha : action C (fun i => u i / dot b u) = fun i => b i / dot b u := by
    funext i
    rw [action_div, hu]
  unfold quadratic
  rw [ha, dot_div, dot_comm, dot_div]
  field_simp [hT]
  <;> ring

/-- Scalar Schur-information update; positivity is a separate explicit input. -/
theorem schur_information_identity (T β K B v : ℝ) (hδ : v - B ≠ 0) :
    T - ((β - K) / (v - B)) * K + β * ((β - K) / (v - B)) =
      T + (β - K)^2 / (v - B) := by
  field_simp [hδ]
  <;> ring

theorem schur_information_nondecreasing (T η δ : ℝ) (hδ : 0 < δ) :
    T ≤ T + η^2 / δ := by
  have h := div_nonneg (sq_nonneg η) hδ.le
  linarith

/-- The block covariance solve and its information increment, before inversion. -/
theorem schur_solve_and_information (C : ι → ι → ℝ) (b k u z : ι → ℝ)
    (β v : ℝ) (hC : ∀ i j, C i j = C j i)
    (hu : ∀ i, action C u i = b i) (hz : ∀ i, action C z i = k i)
    (hδ : v - dot k z ≠ 0) :
    let y := (β - dot k u) / (v - dot k z)
    let x := fun i => u i - y * z i
    (∀ i, action C x i + k i * y = b i) ∧
      dot k x + v * y = β ∧
      dot b x + β * y = dot b u + (β - dot k u)^2 / (v - dot k z) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [action_sub_smul, hu, hz]
    ring
  · rw [dot_sub_smul_right]
    field_simp [hδ]
    <;> ring
  · rw [dot_sub_smul_right, solve_reciprocity C b k u z hC hu hz]
    exact schur_information_identity (dot b u) β (dot k u) (dot k z) v hδ

end RiemannResearch.LinearAlgebra.CenteredNormalEquations
