import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Finite prime-power return Green matrices and exact endpoint correction

This module proves the inverse of the finite geometric AR(1) matrix by
explicit row multiplication. It then specializes to r = 1 / sqrt(p) and
proves that the inverse of the compressed geometric Green matrix is the
finite differential minus both endpoint coordinate projectors. Matrices
have n+1 sites, so n=0 includes the singleton case without an exception.

Source: user-provided argument,
RH_Exact_Arithmetic_Channel_Effects_2026-09-07.md, Section 7, and
arithmetic_audit_agent.md, Section 4. These sources support the statements
and the direct-multiplication proof strategy.

This finite algebraic theorem does not by itself construct the infinite
Green operator, prove its analytic compression identity, or identify a
signed Weil form. Those are separate analytical statements.
-/

namespace RiemannResearch.RH.PrimePowerReturn
noncomputable section
open scoped BigOperators
/-- Natural distance, written using truncated subtraction. -/
def natGap (i j : ℕ) : ℕ := (i-j)+(j-i)
def returnKernel (r : ℝ) (i j : ℕ) : ℝ := r ^ natGap i j

theorem returnKernel_recurrence (r : ℝ) (i j : ℕ) (hi : 0 < i) :
    (1+r^2)*returnKernel r i j - r*returnKernel r (i-1) j -
      r*returnKernel r (i+1) j = (1-r^2)*(if i=j then 1 else 0) := by
  rcases lt_trichotomy i j with h | h | h
  · have e0 : natGap i j = (j-i-1)+1 := by unfold natGap; omega
    have em : natGap (i-1) j = ((j-i-1)+1)+1 := by unfold natGap; omega
    have ep : natGap (i+1) j = j-i-1 := by unfold natGap; omega
    simp only [returnKernel, e0, em, ep, pow_succ, if_neg (by omega : i ≠ j)]
    ring
  · subst j
    have em : natGap (i-1) i = 1 := by unfold natGap; omega
    have ep : natGap (i+1) i = 1 := by unfold natGap; omega
    simp only [returnKernel, em, ep, pow_one]
    simp [natGap]
    ring
  · have e0 : natGap i j = (i-j-1)+1 := by unfold natGap; omega
    have em : natGap (i-1) j = i-j-1 := by unfold natGap; omega
    have ep : natGap (i+1) j = ((i-j-1)+1)+1 := by unfold natGap; omega
    simp only [returnKernel, e0, em, ep, pow_succ, if_neg (by omega : i ≠ j)]
    ring

theorem returnKernel_left (r : ℝ) (j : ℕ) :
    returnKernel r 0 j-r*returnKernel r 1 j = (1-r^2)*(if 0=j then 1 else 0) := by
  cases j with
  | zero => simp [returnKernel, natGap]; ring
  | succ j =>
    have e : natGap 1 (j+1) = j := by unfold natGap; omega
    simp [returnKernel, natGap, pow_succ]
    ring

theorem returnKernel_right (r : ℝ) (i j : ℕ) (h : j ≤ i) :
    r*returnKernel r (i+1) j = r^2*returnKernel r i j := by
  have e : natGap (i+1) j = natGap i j+1 := by unfold natGap; omega
  simp only [returnKernel, e, pow_succ]
  ring

def ar1Diagonal (n : ℕ) (r : ℝ) (i : ℕ) : ℝ :=
  1+r^2-(if i=0 then r^2 else 0)-(if i=n then r^2 else 0)

theorem returnKernel_finite_row (n : ℕ) (r : ℝ) (i j : ℕ)
    (hi : i ≤ n) (hj : j ≤ n) :
    ar1Diagonal n r i * returnKernel r i j -
      (if 0 < i then r*returnKernel r (i-1) j else 0) -
      (if i < n then r*returnKernel r (i+1) j else 0) =
        (1-r^2)*(if i=j then 1 else 0) := by
  by_cases hn : n=0
  · subst n
    have hi0 : i=0 := by omega
    have hj0 : j=0 := by omega
    subst i; subst j
    simp [ar1Diagonal, returnKernel, natGap]
  · by_cases hi0 : i=0
    · subst i
      have hn0 : 0 < n := by omega
      simpa [ar1Diagonal, hn, hn0, Ne.symm hn] using returnKernel_left r j
    · have hip : 0 < i := by omega
      by_cases hin : i=n
      · subst i
        have hrec := returnKernel_recurrence r n j hip
        have bdy := returnKernel_right r n j hj
        simp only [ar1Diagonal, if_neg hn, if_pos hip,
          lt_self_iff_false, if_false, ite_true]
        linear_combination hrec + bdy
      · have hil : i < n := by omega
        simpa [ar1Diagonal, hi0, hin, hip, hil] using returnKernel_recurrence r i j hip

/-- The finite AR(1) covariance on n+1 consecutive sites. -/
def finiteAR1 (n : ℕ) (r : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => returnKernel r i.val j.val

/-- The explicit tridiagonal numerator of the inverse. Both endpoint
subtractions occur even on a one-site chain. -/
def ar1Tridiagonal (n : ℕ) (r : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i k =>
    (if k=i then ar1Diagonal n r i.val else 0) -
    (if h : 0 < i.val then
      if k=⟨i.val-1, by omega⟩ then r else 0 else 0) -
    (if h : i.val < n then
      if k=⟨i.val+1, by omega⟩ then r else 0 else 0)

theorem ar1Tridiagonal_mul_apply (n : ℕ) (r : ℝ) (i j : Fin (n+1)) :
    (ar1Tridiagonal n r * finiteAR1 n r) i j =
      ar1Diagonal n r i.val * returnKernel r i.val j.val -
      (if 0 < i.val then r*returnKernel r (i.val-1) j.val else 0) -
      (if i.val < n then r*returnKernel r (i.val+1) j.val else 0) := by
  by_cases h0 : 0 < i.val <;> by_cases hn : i.val < n <;>
    simp [ar1Tridiagonal, Matrix.mul_apply, sub_mul,
      Finset.sum_sub_distrib, h0, hn, ite_mul, finiteAR1]

theorem ar1Tridiagonal_mul (n : ℕ) (r : ℝ) :
    ar1Tridiagonal n r * finiteAR1 n r = (1-r^2) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) := by
  ext i j
  rw [ar1Tridiagonal_mul_apply]
  have h := returnKernel_finite_row n r i.val j.val (by omega) (by omega)
  simpa [Matrix.smul_apply, Matrix.one_apply, Fin.ext_iff] using h


/-- A directly checked left inverse, with the only required scalar
nonsingularity condition. -/
theorem ar1Precision_mul (n : ℕ) (r : ℝ) (hr : 1-r^2 ≠ 0) :
    ((1-r^2)⁻¹ • ar1Tridiagonal n r) * finiteAR1 n r = 1 := by
  rw [smul_mul_assoc, ar1Tridiagonal_mul, smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem finiteAR1_inverse (n : ℕ) (r : ℝ) (hr : 1-r^2 ≠ 0) :
    (finiteAR1 n r)⁻¹ = (1-r^2)⁻¹ • ar1Tridiagonal n r :=
  Matrix.inv_eq_left_inv (ar1Precision_mul n r hr)

theorem finiteAR1_det_ne_zero (n : ℕ) (r : ℝ) (hr : 1-r^2 ≠ 0) :
    (finiteAR1 n r).det ≠ 0 := by
  intro h
  have hh := congrArg Matrix.det (ar1Precision_mul n r hr)
  simp [Matrix.det_mul, h] at hh

theorem ar1Tridiagonal_apply (n : ℕ) (r : ℝ) (i j : Fin (n+1)) :
    ar1Tridiagonal n r i j =
      (if i=j then ar1Diagonal n r i.val else 0) -
      (if i.val=j.val+1 then r else 0) -
      (if i.val+1=j.val then r else 0) := by
  have hp (h : 0 < i.val) :
      (j.val=i.val-1) ↔ i.val=j.val+1 := by omega
  have hq : (j.val=i.val+1) ↔ i.val+1=j.val := eq_comm
  have hd : (j.val=i.val) ↔ i.val=j.val := eq_comm
  by_cases h0 : 0 < i.val <;> by_cases hn : i.val < n
  · simp [ar1Tridiagonal, h0, hn, Fin.ext_iff, hp h0, hq, hd]
  · have he : i.val+1 ≠ j.val := by omega
    simp [ar1Tridiagonal, h0, hn, Fin.ext_iff, hp h0, he, hd]
  · have he : i.val ≠ j.val+1 := by omega
    simp [ar1Tridiagonal, h0, hn, Fin.ext_iff, he, hq, hd]
  · have he : i.val ≠ j.val+1 := by omega
    have hf : i.val+1 ≠ j.val := by omega
    simp [ar1Tridiagonal, h0, hn, Fin.ext_iff, he, hf, hd]


/-- The compressed full-line geometric Green matrix, written entrywise
as r^|i-j|/(p-1), where r=1/sqrt(p). -/
def compressedPrimeGreen (n : ℕ) (p : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  (p-1)⁻¹ • finiteAR1 n (Real.sqrt p)⁻¹

/-- The finite compression of (p+1)I-sqrt(p)(U+U*). -/
def finitePrimeDifferential (n : ℕ) (p : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => (if i=j then p+1 else 0) -
    (if i.val=j.val+1 then Real.sqrt p else 0) -
    (if i.val+1=j.val then Real.sqrt p else 0)

/-- A diagonal coordinate projector; the two endpoint projectors
coincide, and are both counted, for n=0. -/
def endpointProjector (n k : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => if i.val=k ∧ j.val=k then 1 else 0

theorem prime_scaled_tridiagonal (n : ℕ) (p : ℝ) (hp : 1 < p) :
    p • ar1Tridiagonal n (Real.sqrt p)⁻¹ =
      finitePrimeDifferential n p - endpointProjector n 0 - endpointProjector n n := by
  have hp0 : 0 ≤ p := by linarith
  have hpne : p ≠ 0 := by linarith
  have hsne : Real.sqrt p ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith)
  have hr : p*(Real.sqrt p)⁻¹ = Real.sqrt p := by
    calc
      p*(Real.sqrt p)⁻¹ = (Real.sqrt p)^2*(Real.sqrt p)⁻¹ := by rw [Real.sq_sqrt hp0]
      _ = Real.sqrt p := by field_simp
  have hr2 : p*((Real.sqrt p)⁻¹)^2 = 1 := by
    rw [inv_pow, Real.sq_sqrt hp0, mul_inv_cancel₀ hpne]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, ar1Tridiagonal_apply,
    Matrix.sub_apply, finitePrimeDifferential, endpointProjector]
  by_cases hij : i=j
  · subst j
    simp only [ite_true, and_self,
      show ¬i.val=i.val+1 by omega, show ¬i.val+1=i.val by omega,
      if_false, sub_zero, ar1Diagonal]
    split_ifs <;> nlinarith [hr2]
  · have he0 : ¬(i.val=0 ∧ j.val=0) := by
      intro h; apply hij; apply Fin.ext; omega
    have hen : ¬(i.val=n ∧ j.val=n) := by
      intro h; apply hij; apply Fin.ext; omega
    simp only [if_neg hij, if_neg he0, if_neg hen, sub_zero]
    split_ifs <;> nlinarith [hr]

theorem prime_scaled_tridiagonal_mul_green (n : ℕ) (p : ℝ) (hp : 1 < p) :
    (p • ar1Tridiagonal n (Real.sqrt p)⁻¹) * compressedPrimeGreen n p = 1 := by
  have hp0 : 0 ≤ p := by linarith
  have hpne : p ≠ 0 := by linarith
  have hm : p-1 ≠ 0 := by linarith
  have hscale : p*((p-1)⁻¹*(1-((Real.sqrt p)⁻¹)^2)) = 1 := by
    rw [inv_pow, Real.sq_sqrt hp0]
    field_simp
  rw [compressedPrimeGreen, smul_mul_assoc, mul_smul_comm,
    ar1Tridiagonal_mul, smul_smul, smul_smul, mul_assoc, hscale, one_smul]

/-- The exact endpoint correction for every nonempty finite chain. The
case n=0 is the one-site identity p-1=(p+1)-2. -/
theorem compressedPrimeGreen_inverse (n : ℕ) (p : ℝ) (hp : 1 < p) :
    (compressedPrimeGreen n p)⁻¹ =
      finitePrimeDifferential n p - endpointProjector n 0 - endpointProjector n n := by
  rw [← prime_scaled_tridiagonal n p hp]
  exact Matrix.inv_eq_left_inv (prime_scaled_tridiagonal_mul_green n p hp)

/-- Nonsingularity is proved from the explicit inverse, not assumed. -/
theorem compressedPrimeGreen_det_ne_zero (n : ℕ) (p : ℝ) (hp : 1 < p) :
    (compressedPrimeGreen n p).det ≠ 0 := by
  intro h
  have hh := congrArg Matrix.det (prime_scaled_tridiagonal_mul_green n p hp)
  simp [Matrix.det_mul, h] at hh


theorem compressedPrimeGreen_apply (n : ℕ) (p : ℝ) (i j : Fin (n+1)) :
    compressedPrimeGreen n p i j =
      (Real.sqrt p)⁻¹ ^ natGap i.val j.val / (p-1) := by
  simp [compressedPrimeGreen, finiteAR1, returnKernel, div_eq_mul_inv, mul_comm]

@[simp] theorem compressedPrimeGreen_inverse_singleton (p : ℝ) (hp : 1 < p) :
    (compressedPrimeGreen 0 p)⁻¹ 0 0 = p-1 := by
  rw [compressedPrimeGreen_inverse 0 p hp]
  simp [finitePrimeDifferential, endpointProjector, Matrix.sub_apply]

end
end RiemannResearch.RH.PrimePowerReturn
