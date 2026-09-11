import Mathlib.Algebra.BigOperators.Field
import Mathlib.NumberTheory.ZetaValues
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Source: user-provided argument in the September 11 RH research conversation.
Finite prefixes of `b_n = e_0 + n e_n` have unique coefficients, but every
mean-one combination has squared approximation error at least `1/2`.
The exact minimum is the reciprocal of the partial sum of reciprocal squares.
The exact minima tend to `6 / π²`, using Mathlib's Basel summation theorem.
This explains why finite independence does not establish the RH approximation target.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.IndependentMeanOneObstruction
noncomputable section

/-- The finite-dimensional realization of a combination of `e₀ + (i+1)eᵢ`.
The `none` coordinate is the mean; the `some i` coordinates are its error. -/
def packet {N : ℕ} (c : Fin N → ℝ) : Option (Fin N) → ℝ
  | none => ∑ i, c i
  | some i => ((i.val : ℝ) + 1) * c i

/-- The independent vectors in the example. -/
def basisVector {N : ℕ} (i : Fin N) : Option (Fin N) → ℝ
  | none => 1
  | some j => if j = i then (j.val : ℝ) + 1 else 0

theorem packet_eq_sum {N : ℕ} (c : Fin N → ℝ) :
    packet c = ∑ i, c i • basisVector i := by
  funext o
  cases o with
  | none => simp [packet, basisVector, Finset.sum_apply]
  | some j => simp [packet, basisVector, Finset.sum_apply, mul_ite, mul_comm]

theorem basisVector_linearIndependent (N : ℕ) :
    LinearIndependent ℝ (@basisVector N) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hp : packet c = 0 := by rw [packet_eq_sum]; exact hc
  have hi := congrFun hp (some i)
  change ((i.val : ℝ) + 1) * c i = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left (by positivity)

/-- Squared Euclidean error relative to the unit vector at `none`. -/
def squaredError {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ((∑ i, c i) - 1) ^ 2 + ∑ i, (((i.val : ℝ) + 1) * c i) ^ 2

/-- Explicit uniqueness of coefficients, the finite linear-independence property. -/
theorem packet_injective (N : ℕ) : Function.Injective (@packet N) := by
  intro c d h
  funext i
  have hi := congrFun h (some i)
  change ((i.val : ℝ) + 1) * c i = ((i.val : ℝ) + 1) * d i at hi
  exact mul_left_cancel₀ (by positivity : (i.val : ℝ) + 1 ≠ 0) hi

/-- The inverse-square normalizing factor. -/
def reciprocalSum (N : ℕ) : ℝ :=
  ∑ i : Fin N, (((i.val : ℝ) + 1)⁻¹) ^ 2

/-- The minimizing coefficients. -/
def optimizer (N : ℕ) (i : Fin N) : ℝ :=
  (((i.val : ℝ) + 1)⁻¹) ^ 2 * (reciprocalSum N)⁻¹

theorem optimizer_mean {N : ℕ} (hS : reciprocalSum N ≠ 0) :
    ∑ i, optimizer N i = 1 := by
  unfold optimizer
  rw [← Finset.sum_mul]
  change reciprocalSum N * (reciprocalSum N)⁻¹ = 1
  exact mul_inv_cancel₀ hS

/-- Exact completion of squares; all signed cross terms have been evaluated. -/
theorem energy_completion {N : ℕ} (c : Fin N → ℝ)
    (hc : ∑ i, c i = 1) (hS : reciprocalSum N ≠ 0) :
    (∑ i, (((i.val : ℝ) + 1) * c i) ^ 2) =
      (reciprocalSum N)⁻¹ +
      ∑ i, (((i.val : ℝ) + 1) * (c i - optimizer N i)) ^ 2 := by
  have hterm (i : Fin N) :
      (((i.val : ℝ) + 1) * (c i - optimizer N i)) ^ 2 =
      (((i.val : ℝ) + 1) * c i) ^ 2 -
      (2 * (reciprocalSum N)⁻¹) * c i +
      ((reciprocalSum N)⁻¹)^2 * (((i.val : ℝ) + 1)⁻¹)^2 := by
    dsimp [optimizer]
    have hi : (i.val : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    <;> ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hsum : (∑ i : Fin N, (((i.val : ℝ) + 1)⁻¹)^2) = reciprocalSum N := rfl
  simp only [← Finset.mul_sum, hc, hsum]
  field_simp
  <;> ring

theorem squaredError_of_mean_one {N : ℕ} (c : Fin N → ℝ)
    (hc : ∑ i, c i = 1) :
    squaredError c = ∑ i, (((i.val : ℝ) + 1) * c i) ^ 2 := by
  simp [squaredError, hc]

theorem optimizer_squaredError {N : ℕ} (hS : reciprocalSum N ≠ 0) :
    squaredError (optimizer N) = (reciprocalSum N)⁻¹ := by
  rw [squaredError_of_mean_one _ (optimizer_mean hS)]
  simpa using energy_completion (optimizer N) (optimizer_mean hS) hS

theorem optimizer_minimizes {N : ℕ} (c : Fin N → ℝ)
    (hc : ∑ i, c i = 1) (hS : reciprocalSum N ≠ 0) :
    (reciprocalSum N)⁻¹ ≤ squaredError c := by
  rw [squaredError_of_mean_one c hc, energy_completion c hc hS]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Elementary telescoping bound, uniform in the number of independent vectors. -/
theorem reciprocalSum_le (N : ℕ) :
    reciprocalSum N ≤ 2 - 2 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp [reciprocalSum]
  | succ N ih =>
      have hrec : reciprocalSum (N + 1) =
          reciprocalSum N + (((N : ℝ) + 1)⁻¹)^2 := by
        simp [reciprocalSum, Fin.sum_univ_castSucc]
      rw [hrec]
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have h1 : (0 : ℝ) < N + 1 := by positivity
      have h2 : (0 : ℝ) < N + 2 := by positivity
      have hstep : (((N : ℝ) + 1)⁻¹)^2 ≤
          2 / ((N : ℝ) + 1) - 2 / ((N : ℝ) + 2) := by
        apply (mul_le_mul_iff_of_pos_right (show 0 < ((N : ℝ) + 1)^2 * (N + 2) by positivity)).mp
        field_simp
        <;> nlinarith
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
      linarith

theorem reciprocalSum_pos {N : ℕ} (hN : 0 < N) : 0 < reciprocalSum N := by
  unfold reciprocalSum
  apply Finset.sum_pos'
  · intro i _
    positivity
  · exact ⟨⟨0, hN⟩, Finset.mem_univ _, by positivity⟩

/-- Independence and mean-one normalization do not force arbitrarily small error. -/
theorem uniform_positive_error {N : ℕ} (c : Fin N → ℝ)
    (hc : ∑ i, c i = 1) : (1 : ℝ) / 2 ≤ squaredError c := by
  have hN : 0 < N := by
    by_contra h
    have : N = 0 := by omega
    subst N
    simpa using hc
  have hS := reciprocalSum_pos hN
  have hupper : reciprocalSum N ≤ 2 := by
    have h := reciprocalSum_le N
    have : (0 : ℝ) ≤ 2 / ((N : ℝ) + 1) := by positivity
    linarith
  have hlower : (1 : ℝ) / 2 ≤ (reciprocalSum N)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hS).2
    nlinarith
  exact hlower.trans (optimizer_minimizes c hc (ne_of_gt hS))

open Filter Topology

/-- The shifted reciprocal-square series has its classical Basel sum. -/
theorem hasSum_reciprocalSquares :
    HasSum (fun n : ℕ => (((n : ℝ) + 1)⁻¹)^2) (Real.pi^2 / 6) := by
  have h := (hasSum_nat_add_iff'
    (f := fun n : ℕ => 1 / (n : ℝ)^2) (g := Real.pi^2 / 6) 1).2 hasSum_zeta_two
  simpa [Nat.cast_add, one_div, inv_pow] using h

/-- The normalizing reciprocal sum tends to the Basel value. -/
theorem reciprocalSum_tendsto :
    Tendsto reciprocalSum atTop (𝓝 (Real.pi^2 / 6)) := by
  have heq : reciprocalSum = (fun N : ℕ => ∑ i ∈ Finset.range N, (((i : ℝ) + 1)⁻¹)^2) := by
    funext N
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => (((n : ℝ) + 1)⁻¹)^2) N
  rw [heq]
  exact hasSum_reciprocalSquares.tendsto_sum_nat

/-- The exact least-squares minima converge to a strictly positive value. -/
theorem minimum_tendsto :
    Tendsto (fun N => (reciprocalSum N)⁻¹) atTop (𝓝 (6 / Real.pi^2)) := by
  have h := reciprocalSum_tendsto.inv₀
    (by positivity : Real.pi^2 / 6 ≠ 0)
  simpa only [inv_div] using h

theorem minimum_limit_pos : (0 : ℝ) < 6 / Real.pi^2 := by positivity

/-- No sequence of mean-one finite combinations approximates the target. -/
theorem no_mean_one_approximation (N : ℕ → ℕ) (c : ∀ j, Fin (N j) → ℝ)
    (hc : ∀ j, ∑ i, c j i = 1) :
    ¬ Tendsto (fun j => squaredError (c j)) atTop (𝓝 0) := by
  intro h
  have hh : (1 : ℝ) / 2 ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds h
      (fun j => uniform_positive_error (c j) (hc j))
  norm_num at hh

end
end RiemannResearch.Analysis.IndependentMeanOneObstruction
