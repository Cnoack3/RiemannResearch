import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite resolvent certificates with exact Radau remainders

Source: the user-provided exact optimizer cancellation argument of 2026-10-08.
The certificate is a completion of the square for `1 / (1 + x)` against a
positive finite measure. The two endpoint modifications are multiplication of
the measure by `x` and by `q - x`. Both full nonnegative remainders are retained.

The normal-equation theorems assume supplied coefficients satisfy two finite
linear equations. They do not assert an inverse matrix exists or that an
arbitrary list of four real numbers is a positive moment sequence. There is no
numerical table in this development.
-/

noncomputable section

namespace RiemannResearch.Analysis.FiniteResolventRadau

open scoped BigOperators

variable {ι : Type*}

def moment (s : Finset ι) (w x : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ s, w i * x i ^ n

def resolvent (s : Finset ι) (w x : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i / (1 + x i)

def linearPolynomial (c₀ c₁ t : ℝ) : ℝ := c₀ + c₁ * t

def variationalValue (s : Finset ι) (w x : ι → ℝ) (c₀ c₁ : ℝ) : ℝ :=
  2 * (∑ i ∈ s, w i * linearPolynomial c₀ c₁ (x i)) -
    ∑ i ∈ s, w i * (1 + x i) * linearPolynomial c₀ c₁ (x i) ^ 2

def squareRemainder (s : Finset ι) (w x : ι → ℝ) (c₀ c₁ : ℝ) : ℝ :=
  ∑ i ∈ s, w i * (1 - (1 + x i) * linearPolynomial c₀ c₁ (x i)) ^ 2 /
    (1 + x i)

theorem scalar_complete_square (w t p : ℝ) (ht : 1 + t ≠ 0) :
    w / (1 + t) - (2 * (w * p) - w * (1 + t) * p ^ 2) =
      w * (1 - (1 + t) * p) ^ 2 / (1 + t) := by
  field_simp [ht]
  ring

/-- The complete equality, including the positive square remainder. -/
theorem complete_square (s : Finset ι) (w x : ι → ℝ) (c₀ c₁ : ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    resolvent s w x - variationalValue s w x c₀ c₁ =
      squareRemainder s w x c₀ c₁ := by
  unfold resolvent variationalValue squareRemainder
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact scalar_complete_square _ _ _ (by linarith [hx i hi])

theorem squareRemainder_nonneg (s : Finset ι) (w x : ι → ℝ) (c₀ c₁ : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) :
    0 ≤ squareRemainder s w x c₀ c₁ := by
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (mul_nonneg (hw i hi) (sq_nonneg _)) (by linarith [hx i hi])

theorem variationalValue_le_resolvent (s : Finset ι) (w x : ι → ℝ)
    (c₀ c₁ : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) :
    variationalValue s w x c₀ c₁ ≤ resolvent s w x := by
  have he := complete_square s w x c₀ c₁ hx
  have hr := squareRemainder_nonneg s w x c₀ c₁ hw hx
  linarith

theorem linear_sum_eq (s : Finset ι) (w x : ι → ℝ) (c₀ c₁ : ℝ) :
    (∑ i ∈ s, w i * linearPolynomial c₀ c₁ (x i)) =
      c₀ * moment s w x 0 + c₁ * moment s w x 1 := by
  unfold moment linearPolynomial
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [pow_zero, pow_one]
  ring

theorem quadratic_sum_eq (s : Finset ι) (w x : ι → ℝ) (c₀ c₁ : ℝ) :
    (∑ i ∈ s, w i * (1 + x i) * linearPolynomial c₀ c₁ (x i) ^ 2) =
      c₀ ^ 2 * (moment s w x 0 + moment s w x 1) +
      2 * c₀ * c₁ * (moment s w x 1 + moment s w x 2) +
      c₁ ^ 2 * (moment s w x 2 + moment s w x 3) := by
  unfold moment linearPolynomial
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [pow_zero, pow_one]
  ring

/-- If `(G + J)c = v`, the variational value is exactly `vᵀc`.
No invertibility premise is concealed in this theorem. -/
theorem variationalValue_eq_of_normal_equations (s : Finset ι) (w x : ι → ℝ)
    (c₀ c₁ : ℝ)
    (h₀ : (moment s w x 0 + moment s w x 1) * c₀ +
      (moment s w x 1 + moment s w x 2) * c₁ = moment s w x 0)
    (h₁ : (moment s w x 1 + moment s w x 2) * c₀ +
      (moment s w x 2 + moment s w x 3) * c₁ = moment s w x 1) :
    variationalValue s w x c₀ c₁ = c₀ * moment s w x 0 + c₁ * moment s w x 1 := by
  unfold variationalValue
  rw [linear_sum_eq, quadratic_sum_eq]
  have e₀ := congrArg (fun z : ℝ => c₀ * z) h₀
  have e₁ := congrArg (fun z : ℝ => c₁ * z) h₁
  nlinarith only [e₀, e₁]

/-- Determinant of the two-by-two matrix `G + J`. -/
def normalDeterminant (a₀ a₁ a₂ a₃ : ℝ) : ℝ :=
  (a₀ + a₁) * (a₂ + a₃) - (a₁ + a₂) ^ 2

def normalCoefficient₀ (a₀ a₁ a₂ a₃ : ℝ) : ℝ :=
  ((a₂ + a₃) * a₀ - (a₁ + a₂) * a₁) / normalDeterminant a₀ a₁ a₂ a₃

def normalCoefficient₁ (a₀ a₁ a₂ a₃ : ℝ) : ℝ :=
  ((a₀ + a₁) * a₁ - (a₁ + a₂) * a₀) / normalDeterminant a₀ a₁ a₂ a₃

/-- Cramer's exact coefficients provide the two normal equations whenever the
displayed determinant is nonzero. Degenerate moment sequences are not silently
assumed invertible. -/
theorem cramer_normal_equations (a₀ a₁ a₂ a₃ : ℝ)
    (hd : normalDeterminant a₀ a₁ a₂ a₃ ≠ 0) :
    (a₀ + a₁) * normalCoefficient₀ a₀ a₁ a₂ a₃ +
        (a₁ + a₂) * normalCoefficient₁ a₀ a₁ a₂ a₃ = a₀ ∧
      (a₁ + a₂) * normalCoefficient₀ a₀ a₁ a₂ a₃ +
        (a₂ + a₃) * normalCoefficient₁ a₀ a₁ a₂ a₃ = a₁ := by
  unfold normalCoefficient₀ normalCoefficient₁
  constructor <;> field_simp [hd] <;> unfold normalDeterminant <;> ring

theorem moment_mul_node (s : Finset ι) (w x : ι → ℝ) (n : ℕ) :
    moment s (fun i => x i * w i) x n = moment s w x (n + 1) := by
  unfold moment
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_succ]
  ring

theorem moment_endpoint_weight (s : Finset ι) (w x : ι → ℝ) (q : ℝ) (n : ℕ) :
    moment s (fun i => (q - x i) * w i) x n =
      q * moment s w x n - moment s w x (n + 1) := by
  unfold moment
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_succ]
  ring

theorem resolvent_mul_node (s : Finset ι) (w x : ι → ℝ)
    (hnorm : (∑ i ∈ s, w i) = 1) (hx : ∀ i ∈ s, 0 ≤ x i) :
    resolvent s (fun i => x i * w i) x = 1 - resolvent s w x := by
  rw [← hnorm]
  unfold resolvent
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : 1 + x i ≠ 0 := by linarith [hx i hi]
  field_simp [hi']
  ring

theorem resolvent_endpoint_weight (s : Finset ι) (w x : ι → ℝ) (q : ℝ)
    (hnorm : (∑ i ∈ s, w i) = 1) (hx : ∀ i ∈ s, 0 ≤ x i) :
    resolvent s (fun i => (q - x i) * w i) x =
      (1 + q) * resolvent s w x - 1 := by
  calc
    _ = (1 + q) * resolvent s w x - (∑ i ∈ s, w i) := by
      unfold resolvent
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : 1 + x i ≠ 0 := by linarith [hx i hi]
      field_simp [hi']
      ring
    _ = _ := by rw [hnorm]

/-- Exact upper Radau remainder for the measure `x dν`. -/
theorem radau_upper_remainder (s : Finset ι) (w x : ι → ℝ) (c₀ c₁ : ℝ)
    (hnorm : (∑ i ∈ s, w i) = 1) (hx : ∀ i ∈ s, 0 ≤ x i) :
    1 - variationalValue s (fun i => x i * w i) x c₀ c₁ - resolvent s w x =
      squareRemainder s (fun i => x i * w i) x c₀ c₁ := by
  have h := complete_square s (fun i => x i * w i) x c₀ c₁ hx
  rw [resolvent_mul_node s w x hnorm hx] at h
  linarith

/-- Exact lower Radau remainder for the measure `(q-x) dν`. -/
theorem radau_lower_remainder (s : Finset ι) (w x : ι → ℝ) (q c₀ c₁ : ℝ)
    (hq : 0 ≤ q) (hnorm : (∑ i ∈ s, w i) = 1) (hx : ∀ i ∈ s, 0 ≤ x i) :
    resolvent s w x -
        (1 + variationalValue s (fun i => (q - x i) * w i) x c₀ c₁) / (1 + q) =
      squareRemainder s (fun i => (q - x i) * w i) x c₀ c₁ / (1 + q) := by
  have h := complete_square s (fun i => (q - x i) * w i) x c₀ c₁ hx
  rw [resolvent_endpoint_weight s w x q hnorm hx] at h
  have hq' : 1 + q ≠ 0 := by linarith
  calc
    _ = ((1 + q) * resolvent s w x - 1 -
      variationalValue s (fun i => (q - x i) * w i) x c₀ c₁) / (1 + q) := by
        field_simp [hq']
        ring
    _ = _ := by rw [h]

/-- Two-sided certificate valid even before the normal equations are solved. -/
theorem radau_bounds (s : Finset ι) (w x : ι → ℝ) (q u₀ u₁ l₀ l₁ : ℝ)
    (hq : 0 ≤ q) (hnorm : (∑ i ∈ s, w i) = 1)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hxq : ∀ i ∈ s, x i ≤ q) :
    (1 + variationalValue s (fun i => (q - x i) * w i) x l₀ l₁) / (1 + q) ≤
        resolvent s w x ∧
      resolvent s w x ≤ 1 - variationalValue s (fun i => x i * w i) x u₀ u₁ := by
  have hu := radau_upper_remainder s w x u₀ u₁ hnorm hx
  have hr₁ := squareRemainder_nonneg s (fun i => x i * w i) x u₀ u₁
    (fun i hi => mul_nonneg (hx i hi) (hw i hi)) hx
  have hl := radau_lower_remainder s w x q l₀ l₁ hq hnorm hx
  have hr₂ := squareRemainder_nonneg s (fun i => (q - x i) * w i) x l₀ l₁
    (fun i hi => mul_nonneg (sub_nonneg.mpr (hxq i hi)) (hw i hi)) hx
  have hd : 0 ≤ squareRemainder s (fun i => (q - x i) * w i) x l₀ l₁ / (1 + q) :=
    div_nonneg hr₂ (by linarith)
  constructor <;> linarith

/-- The complete four-moment Radau certificate, written in the original moments.
The upper normal equations use moments `κ₁,…,κ₄`; the lower equations use
`qκⱼ-κⱼ₊₁`. The two normal-equation providers are explicit hypotheses. -/
theorem radau_four_moment_certificate (s : Finset ι) (w x : ι → ℝ)
    (q u₀ u₁ l₀ l₁ : ℝ)
    (hq : 0 ≤ q) (hnorm : (∑ i ∈ s, w i) = 1)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hxq : ∀ i ∈ s, x i ≤ q)
    (hu₀ : (moment s w x 1 + moment s w x 2) * u₀ +
      (moment s w x 2 + moment s w x 3) * u₁ = moment s w x 1)
    (hu₁ : (moment s w x 2 + moment s w x 3) * u₀ +
      (moment s w x 3 + moment s w x 4) * u₁ = moment s w x 2)
    (hl₀ : ((q * moment s w x 0 - moment s w x 1) +
        (q * moment s w x 1 - moment s w x 2)) * l₀ +
      ((q * moment s w x 1 - moment s w x 2) +
        (q * moment s w x 2 - moment s w x 3)) * l₁ =
      q * moment s w x 0 - moment s w x 1)
    (hl₁ : ((q * moment s w x 1 - moment s w x 2) +
        (q * moment s w x 2 - moment s w x 3)) * l₀ +
      ((q * moment s w x 2 - moment s w x 3) +
        (q * moment s w x 3 - moment s w x 4)) * l₁ =
      q * moment s w x 1 - moment s w x 2) :
    (1 + (l₀ * (q * moment s w x 0 - moment s w x 1) +
        l₁ * (q * moment s w x 1 - moment s w x 2))) / (1 + q) ≤
        resolvent s w x ∧
      resolvent s w x ≤ 1 - (u₀ * moment s w x 1 + u₁ * moment s w x 2) := by
  have hu : variationalValue s (fun i => x i * w i) x u₀ u₁ =
      u₀ * moment s w x 1 + u₁ * moment s w x 2 := by
    simpa only [moment_mul_node] using
      variationalValue_eq_of_normal_equations s (fun i => x i * w i) x u₀ u₁
        (by simpa only [moment_mul_node] using hu₀)
        (by simpa only [moment_mul_node] using hu₁)
  have hl : variationalValue s (fun i => (q - x i) * w i) x l₀ l₁ =
      l₀ * (q * moment s w x 0 - moment s w x 1) +
        l₁ * (q * moment s w x 1 - moment s w x 2) := by
    simpa only [moment_endpoint_weight] using
      variationalValue_eq_of_normal_equations s (fun i => (q - x i) * w i) x l₀ l₁
        (by simpa only [moment_endpoint_weight] using hl₀)
        (by simpa only [moment_endpoint_weight] using hl₁)
  have h := radau_bounds s w x q u₀ u₁ l₀ l₁ hq hnorm hw hx hxq
  rw [hu, hl] at h
  exact h

end RiemannResearch.Analysis.FiniteResolventRadau
