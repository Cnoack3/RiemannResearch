import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite algebra for signed Gaussian explicit-formula matrices

Source: user-provided LandauSingleZeroDetection20261028.md, sections 6--8,
for the intended application.  The declarations below verify finite algebra.
They do not assert the zeta explicit formula, Gaussian integration, convergence
of an infinite prime sum, or unconditional positivity of the signed matrices.
-/

open scoped BigOperators

noncomputable section

namespace RiemannResearch.Analysis.GaussianSignedMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def bilinear (M : ι → ι → ℝ) (x y : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * y j

def quadratic (M : ι → ι → ℝ) (x : ι → ℝ) : ℝ := bilinear M x x

def IsSymmetric (M : ι → ι → ℝ) : Prop := ∀ i j, M i j = M j i

def IsNonnegative (M : ι → ι → ℝ) : Prop := ∀ x, 0 ≤ quadratic M x

theorem bilinear_symm (M : ι → ι → ℝ) (hM : IsSymmetric M)
    (x y : ι → ℝ) : bilinear M x y = bilinear M y x := by
  unfold bilinear
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hM j i]
  ring

theorem quadratic_signed (A P : ι → ι → ℝ) (x : ι → ℝ) :
    quadratic (fun i j => A i j - P i j) x =
      quadratic A x - quadratic P x := by
  simp only [quadratic, bilinear, mul_sub, sub_mul,
    Finset.sum_sub_distrib]

theorem quadratic_sum (A E : ι → ι → ℝ) (x : ι → ℝ) :
    quadratic (fun i j => A i j + E i j) x =
      quadratic A x + quadratic E x := by
  simp only [quadratic, bilinear, mul_add, add_mul,
    Finset.sum_add_distrib]

/-- A uniform entrywise error controls every quadratic direction.
This is a finite-algebra certificate; supplying the error bound is separate. -/
theorem quadratic_entrywise_lower (E : ι → ι → ℝ) (ε : ℝ)
    (hE : ∀ i j, |E i j| ≤ ε) (x : ι → ℝ) :
    -(ε * (∑ i, |x i|) ^ 2) ≤ quadratic E x := by
  have he (i j : ι) : -(ε * |x i| * |x j|) ≤ x i * E i j * x j := by
    have ha : |x i * E i j * x j| ≤ ε * |x i| * |x j| := by
      rw [abs_mul, abs_mul]
      calc
        |x i| * |E i j| * |x j| ≤ |x i| * ε * |x j| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _)) (abs_nonneg _)
        _ = ε * |x i| * |x j| := by ring
    exact le_trans (neg_le_neg ha) (neg_abs_le _)
  have hs : (∑ i, ∑ j, -(ε * |x i| * |x j|)) ≤ quadratic E x := by
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j
  have hid : (∑ i, ∑ j, -(ε * |x i| * |x j|)) =
      -(ε * (∑ i, |x i|) ^ 2) := by
    simp only [Finset.sum_neg_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, pow_two]
    ring
  rw [hid] at hs
  exact hs

theorem nonnegative_plus_entrywise_lower (H E : ι → ι → ℝ)
    (hH : IsNonnegative H) (ε : ℝ) (hE : ∀ i j, |E i j| ≤ ε)
    (x : ι → ℝ) :
    -(ε * (∑ i, |x i|) ^ 2) ≤ quadratic (fun i j => H i j + E i j) x := by
  rw [quadratic_sum]
  have h₁ := hH x
  have h₂ := quadratic_entrywise_lower E ε hE x
  linarith

theorem quadratic_add (M : ι → ι → ℝ) (hM : IsSymmetric M)
    (x y : ι → ℝ) :
    quadratic M (fun i => x i + y i) =
      quadratic M x + 2 * bilinear M x y + quadratic M y := by
  have hxy := bilinear_symm M hM y x
  simp only [bilinear] at hxy
  simp only [quadratic, bilinear, add_mul, mul_add,
    Finset.sum_add_distrib]
  linarith

def hankel (n : ℕ) (μ : ℕ → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => μ (i.val + j.val)

theorem hankel_symmetric (n : ℕ) (μ : ℕ → ℝ) :
    IsSymmetric (hankel n μ) := by
  intro i j
  simp only [hankel, Nat.add_comm]

def evaluate (n : ℕ) (c : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * x ^ i.val

theorem evaluate_sq (n : ℕ) (c : Fin n → ℝ) (x : ℝ) :
    evaluate n c x ^ 2 =
      ∑ i, ∑ j, c i * x ^ (i.val + j.val) * c j := by
  simp only [evaluate, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- A linear functional on polynomials gives the exact Hankel form.
The Gaussian explicit-formula functional is defined on precisely this domain. -/
def coefficientPolynomial (n : ℕ) (c : Fin n → ℝ) : Polynomial ℝ :=
  ∑ i, c i • Polynomial.X ^ i.val

theorem coefficientPolynomial_square (n : ℕ) (c : Fin n → ℝ) :
    coefficientPolynomial n c ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n,
        (c i * c j) • (Polynomial.X : Polynomial ℝ) ^ (i.val + j.val) := by
  simp only [coefficientPolynomial, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm (Polynomial.X ^ j.val)]

theorem polynomialFunctional_square (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (n : ℕ) (c : Fin n → ℝ) :
    L (coefficientPolynomial n c ^ 2) =
      quadratic (hankel n (fun k => L ((Polynomial.X : Polynomial ℝ) ^ k))) c := by
  rw [coefficientPolynomial_square]
  simp only [map_sum, map_smul, smul_eq_mul, quadratic, bilinear, hankel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring


/-- Exact completion with a supplied solution of the normal equations.
The linear term is written as `B(s,z)`; choosing `Cs=b` gives the usual
Schur complement `α-bᵀC⁻¹b`.  No invertibility or positivity is asserted. -/
theorem affine_completion (M : ι → ι → ℝ) (hM : IsSymmetric M)
    (α : ℝ) (s z : ι → ℝ) :
    α + 2 * bilinear M s z + quadratic M z =
      α - quadratic M s + quadratic M (fun i => s i + z i) := by
  rw [quadratic_add M hM]
  ring

theorem affine_lower_bound (M : ι → ι → ℝ) (hM : IsSymmetric M)
    (hpos : IsNonnegative M) (α : ℝ) (s z : ι → ℝ) :
    α - quadratic M s ≤ α + 2 * bilinear M s z + quadratic M z := by
  rw [affine_completion M hM]
  have h := hpos (fun i => s i + z i)
  linarith

/-- The pole factor, in the shifted polynomial coordinate `w=z-τ`. -/
def poleFactor (τ w : ℝ) : ℝ := (w + τ) ^ 2 + 1 / 4

theorem poleFactor_sq (τ w : ℝ) :
    poleFactor τ w ^ 2 =
      w ^ 4 + 4 * τ * w ^ 3 + (6 * τ ^ 2 + 1 / 2) * w ^ 2 +
      (4 * τ ^ 3 + τ) * w + (τ ^ 2 + 1 / 4) ^ 2 := by
  unfold poleFactor
  ring

/-- Five-diagonal moment transform after multiplication by the pole factor. -/
def poleReducedMoment (μ : ℕ → ℝ) (τ : ℝ) (k : ℕ) : ℝ :=
  μ (k + 4) + 4 * τ * μ (k + 3) +
    (6 * τ ^ 2 + 1 / 2) * μ (k + 2) +
    (4 * τ ^ 3 + τ) * μ (k + 1) + (τ ^ 2 + 1 / 4) ^ 2 * μ k

theorem poleReducedMoment_eval (τ w : ℝ) (k : ℕ) :
    poleReducedMoment (fun j => w ^ j) τ k =
      w ^ k * poleFactor τ w ^ 2 := by
  rw [poleFactor_sq]
  simp only [poleReducedMoment, pow_add]
  ring

theorem poleReducedMoment_signed (A P : ℕ → ℝ) (τ : ℝ) (k : ℕ) :
    poleReducedMoment (fun j => A j - P j) τ k =
      poleReducedMoment A τ k - poleReducedMoment P τ k := by
  unfold poleReducedMoment
  ring

/-- Polynomial factor whose evaluation is `((w + τ)^2 + 1/4)`. -/
def polePolynomial (τ : ℝ) : Polynomial ℝ :=
  Polynomial.X ^ 2 + (2 * τ) • Polynomial.X +
    Polynomial.C (τ ^ 2 + 1 / 4)

theorem polePolynomial_eval (τ w : ℝ) :
    (polePolynomial τ).eval w = poleFactor τ w := by
  simp only [polePolynomial, poleFactor, Polynomial.smul_eq_C_mul,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  ring

theorem monicQuadratic_square (a b : ℝ) :
    ((Polynomial.X : Polynomial ℝ) ^ 2 + b • Polynomial.X + Polynomial.C a) ^ 2 =
      Polynomial.X ^ 4 + (2 * b) • Polynomial.X ^ 3 +
      (b ^ 2 + 2 * a) • Polynomial.X ^ 2 +
      (2 * a * b) • Polynomial.X + (a ^ 2) • 1 := by
  simp only [Polynomial.smul_eq_C_mul, Polynomial.C_add,
    Polynomial.C_mul, Polynomial.C_pow, map_ofNat]
  ring

theorem polePolynomial_sq (τ : ℝ) :
    polePolynomial τ ^ 2 =
      Polynomial.X ^ 4 + (4 * τ) • Polynomial.X ^ 3 +
      (6 * τ ^ 2 + 1 / 2) • Polynomial.X ^ 2 +
      (4 * τ ^ 3 + τ) • Polynomial.X + (τ ^ 2 + 1 / 4) ^ 2 • 1 := by
  unfold polePolynomial
  rw [monicQuadratic_square]
  have h₁ : 2 * (2 * τ) = 4 * τ := by ring
  have h₂ : (2 * τ) ^ 2 + 2 * (τ ^ 2 + 1 / 4) = 6 * τ ^ 2 + 1 / 2 := by ring
  have h₃ : 2 * (τ ^ 2 + 1 / 4) * (2 * τ) = 4 * τ ^ 3 + τ := by ring
  rw [h₁, h₂, h₃]

theorem poleReducedMoment_polynomialFunctional
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (τ : ℝ) (k : ℕ) :
    poleReducedMoment (fun j => L ((Polynomial.X : Polynomial ℝ) ^ j)) τ k =
      L (Polynomial.X ^ k * polePolynomial τ ^ 2) := by
  have hf : (Polynomial.X : Polynomial ℝ) ^ k * polePolynomial τ ^ 2 =
      Polynomial.X ^ (k + 4) +
      (4 * τ) • Polynomial.X ^ (k + 3) +
      (6 * τ ^ 2 + 1 / 2) • Polynomial.X ^ (k + 2) +
      (4 * τ ^ 3 + τ) • Polynomial.X ^ (k + 1) +
      (τ ^ 2 + 1 / 4) ^ 2 • Polynomial.X ^ k := by
    rw [polePolynomial_sq]
    simp only [pow_add, pow_one, mul_add, mul_smul_comm, mul_one]
  rw [hf]
  simp only [poleReducedMoment, map_add, map_smul, smul_eq_mul]

def multiplyFunctional (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (D : Polynomial ℝ) : Polynomial ℝ →ₗ[ℝ] ℝ where
  toFun p := L (D * p)
  map_add' p q := by rw [mul_add, map_add]
  map_smul' r p := by simp only [mul_smul_comm, map_smul, RingHom.id_apply]

/-- The exact constrained Hankel matrix after pole-factor multiplication. -/
theorem poleReduced_quadratic (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (τ : ℝ) (n : ℕ) (c : Fin n → ℝ) :
    L ((polePolynomial τ * coefficientPolynomial n c) ^ 2) =
      quadratic (hankel n (poleReducedMoment
        (fun k => L ((Polynomial.X : Polynomial ℝ) ^ k)) τ)) c := by
  have hm (k : ℕ) :
      multiplyFunctional L (polePolynomial τ ^ 2) (Polynomial.X ^ k) =
        poleReducedMoment (fun j => L ((Polynomial.X : Polynomial ℝ) ^ j)) τ k := by
    rw [poleReducedMoment_polynomialFunctional]
    change L (polePolynomial τ ^ 2 * Polynomial.X ^ k) = _
    rw [mul_comm]
  have h := polynomialFunctional_square
    (multiplyFunctional L (polePolynomial τ ^ 2)) n c
  simp only [hm] at h
  change L (polePolynomial τ ^ 2 * coefficientPolynomial n c ^ 2) = _ at h
  rw [mul_pow]
  exact h

/-- A negative value supplies a direction contradicting matrix positivity. -/
theorem not_nonnegative_of_negative (M : ι → ι → ℝ) (x : ι → ℝ)
    (hx : quadratic M x < 0) : ¬ IsNonnegative M := by
  intro h
  exact (not_lt_of_ge (h x)) hx

end RiemannResearch.Analysis.GaussianSignedMatrix
