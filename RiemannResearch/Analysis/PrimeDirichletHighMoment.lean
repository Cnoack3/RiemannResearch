import RiemannResearch.Analysis.PrimeMomentDiagonal
import RiemannResearch.Analysis.DirichletMeanSquare
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continuous high moments of finite prime Dirichlet polynomials

The prime-factor diagonal is developed in the sibling module. The
Montgomery–Vaughan inequality is already proved in the repository. This is the Dirichlet-polynomial ingredient of Tsang's
high-moment method, not a theorem about the argument of the zeta function.
Source: K.-M. Tsang, Some Ω-theorems for the Riemann zeta-function,
Acta Arith. 46 (1986), Section 4, https://matwbn.icm.edu.pl/ksiazki/aa/aa46/aa4646.pdf.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.PrimeMoment

/-- The multiplicative phase on positive integer frequencies. -/
def dirichletPhase (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp ((((Real.log (n : ℝ)) : ℂ) * Complex.I) * (t : ℂ))

theorem dirichletPhase_eq_phase (t : ℝ) (n : ℕ) :
    dirichletPhase t n =
      RiemannResearch.Analysis.ZeroOrdinate.phase (Real.log (n : ℝ)) t := by
  unfold dirichletPhase RiemannResearch.Analysis.ZeroOrdinate.phase
  congr 1
  push_cast
  ring

theorem dirichletPhase_tupleProduct {α : Type*} [Fintype α]
    (p : α → ℕ) (hp : ∀ x, 0 < p x) (k : ℕ) (f : Fin k → α) (t : ℝ) :
    dirichletPhase t (tupleProduct p f) = ∏ i, dirichletPhase t (p (f i)) := by
  classical
  have hlog : Real.log ((tupleProduct p f : ℕ) : ℝ) =
      ∑ i, Real.log (p (f i) : ℝ) := by
    simp only [tupleProduct, Nat.cast_prod]
    apply Real.log_prod
    intro i hi
    exact_mod_cast (hp (f i)).ne'
  unfold dirichletPhase
  rw [hlog]
  simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

/-- Exact grouped power expansion, without discarding nonresonant terms. -/
theorem primeDirichlet_pow_expansion {α : Type*} [Fintype α]
    (p : α → ℕ) (hp : ∀ x, Nat.Prime (p x))
    (a : α → ℂ) (k X : ℕ) (hX : ∀ x, p x ≤ X) (t : ℝ) :
    (∑ x, a x * dirichletPhase t (p x)) ^ k =
      ∑ n ∈ Finset.Icc 1 (X ^ k), primePowerCoefficient p a k n *
        dirichletPhase t n := by
  apply primePolynomial_pow_expansion
  · exact fun f => tupleProduct_mem_Icc p hp X hX f
  · exact fun f => dirichletPhase_tupleProduct p (fun x => (hp x).pos) k f t

/-- The full signed high-moment identity, retaining the off-diagonal term. -/
theorem integral_primeDirichlet_norm_pow_eq_diagonal_add
    {α : Type*} [Fintype α]
    (p : α → ℕ) (hp : ∀ x, Nat.Prime (p x))
    (a : α → ℂ) (k X : ℕ) (hX : ∀ x, p x ≤ X) (A B : ℝ) :
    ((∫ t in A..B, ‖∑ x, a x * dirichletPhase t (p x)‖ ^ (2 * k) : ℝ) : ℂ) =
      (((B - A) * ∑ n ∈ Finset.Icc 1 (X ^ k),
        ‖primePowerCoefficient p a k n‖ ^ 2 : ℝ) : ℂ) +
      RiemannResearch.Analysis.DirichletMeanSquare.offDiagonal
        (fun n : ↥(Finset.Icc 1 (X ^ k)) => primePowerCoefficient p a k (n : ℕ))
        (fun n : ↥(Finset.Icc 1 (X ^ k)) => Real.log (n : ℕ)) A B := by
  classical
  let S : Finset ℕ := Finset.Icc 1 (X ^ k)
  let b : S → ℂ := fun n => primePowerCoefficient p a k (n : ℕ)
  have hpoly (t : ℝ) :
      RiemannResearch.Analysis.DirichletMeanSquare.polynomial b
        (fun n : S => Real.log (n : ℕ)) t =
          (∑ x, a x * dirichletPhase t (p x)) ^ k := by
    rw [primeDirichlet_pow_expansion p hp a k X hX t]
    simp only [RiemannResearch.Analysis.DirichletMeanSquare.polynomial,
      ← dirichletPhase_eq_phase, b]
    exact Finset.sum_coe_sort S
      (fun n : ℕ => primePowerCoefficient p a k n * dirichletPhase t n)
  have h :=
    RiemannResearch.Analysis.DirichletMeanSquare.integral_norm_sq_eq_diagonal_add
      b (fun n : S => Real.log (n : ℕ)) A B
  simp_rw [hpoly, norm_pow, ← pow_mul, Nat.mul_comm k 2] at h
  have hsum : (∑ n : S, ‖b n‖ ^ 2) =
      ∑ n ∈ Finset.Icc 1 (X ^ k), ‖primePowerCoefficient p a k n‖ ^ 2 :=
    Finset.sum_coe_sort S (fun n : ℕ => ‖primePowerCoefficient p a k n‖ ^ 2)
  rw [hsum] at h
  simpa only [b, S] using h

/-- An unconditional continuous high-moment bound for an arbitrary finite
polynomial supported on distinct primes at most `X`. -/
theorem integral_primeDirichlet_norm_pow_le {α : Type*} [Fintype α]
    (p : α → ℕ) (hp : ∀ x, Nat.Prime (p x)) (hinj : Function.Injective p)
    (a : α → ℂ) (k X : ℕ) (hX : ∀ x, p x ≤ X)
    (A B : ℝ) (hAB : A ≤ B) :
    (∫ t in A..B, ‖∑ x, a x * dirichletPhase t (p x)‖ ^ (2 * k)) ≤
      (B - A + 52 * (X : ℝ) ^ k) * (k.factorial : ℝ) *
        (∑ x, ‖a x‖ ^ 2) ^ k := by
  classical
  let S : Finset ℕ := Finset.Icc 1 (X ^ k)
  let b : S → ℂ := fun n => primePowerCoefficient p a k (n : ℕ)
  have hmean :=
    RiemannResearch.Analysis.DirichletMeanSquare.integral_log_polynomial_norm_sq_le
      b (fun n : S => (n : ℕ)) Subtype.val_injective
      (fun n => (Finset.mem_Icc.mp n.property).1)
      (X ^ k) (fun n => (Finset.mem_Icc.mp n.property).2) A B
  have hpoly (t : ℝ) :
      RiemannResearch.Analysis.DirichletMeanSquare.polynomial b
        (fun n : S => Real.log (n : ℕ)) t =
          (∑ x, a x * dirichletPhase t (p x)) ^ k := by
    rw [primeDirichlet_pow_expansion p hp a k X hX t]
    simp only [RiemannResearch.Analysis.DirichletMeanSquare.polynomial,
      ← dirichletPhase_eq_phase, b]
    exact Finset.sum_coe_sort S
      (fun n : ℕ => primePowerCoefficient p a k n * dirichletPhase t n)
  have hnorm (t : ℝ) :
      ‖RiemannResearch.Analysis.DirichletMeanSquare.polynomial b
        (fun n : S => Real.log (n : ℕ)) t‖ ^ 2 =
          ‖∑ x, a x * dirichletPhase t (p x)‖ ^ (2 * k) := by
    rw [hpoly, norm_pow, ← pow_mul, Nat.mul_comm k 2]
  simp_rw [hnorm] at hmean
  have hdiag : (∑ n : S, ‖b n‖ ^ 2) ≤
      (k.factorial : ℝ) * (∑ x, ‖a x‖ ^ 2) ^ k := by
    change (∑ n : S, ‖primePowerCoefficient p a k (n : ℕ)‖ ^ 2) ≤ _
    rw [Finset.sum_coe_sort S (fun n : ℕ => ‖primePowerCoefficient p a k n‖ ^ 2)]
    exact sum_primePowerCoefficient_sq_le p hp hinj a k S
  have hlength : 0 ≤ B - A + 52 * ((X ^ k : ℕ) : ℝ) := by
    have : 0 ≤ B - A := sub_nonneg.mpr hAB
    positivity
  have h := hmean.trans (mul_le_mul_of_nonneg_left hdiag hlength)
  simpa only [Nat.cast_pow, mul_assoc] using h

/-- In the short-polynomial range the continuous moment has Gaussian
factorial growth, with an explicit absolute factor. -/
theorem integral_primeDirichlet_norm_pow_le_of_short_length
    {α : Type*} [Fintype α]
    (p : α → ℕ) (hp : ∀ x, Nat.Prime (p x)) (hinj : Function.Injective p)
    (a : α → ℂ) (k X : ℕ) (hX : ∀ x, p x ≤ X)
    (A B : ℝ) (hAB : A ≤ B) (hshort : 52 * (X : ℝ) ^ k ≤ B - A) :
    (∫ t in A..B, ‖∑ x, a x * dirichletPhase t (p x)‖ ^ (2 * k)) ≤
      2 * (B - A) * (k.factorial : ℝ) * (∑ x, ‖a x‖ ^ 2) ^ k := by
  refine (integral_primeDirichlet_norm_pow_le p hp hinj a k X hX A B hAB).trans ?_
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · linarith
    · exact Nat.cast_nonneg _
  · exact pow_nonneg (Finset.sum_nonneg (fun x hx => sq_nonneg _)) _

end RiemannResearch.Analysis.PrimeMoment
