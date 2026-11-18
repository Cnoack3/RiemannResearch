import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

/-!
# Jacobi's determinant derivative from the finite Leibniz formula

The column-replacement formula also holds at singular matrices. The inverse
is introduced only at a point with nonzero determinant. This is the matrix
calculus used to differentiate periodic Dirichlet Gram determinants.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.GramLogarithmicDerivative
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

theorem det_hasDerivAt {M : 𝕜 → Matrix ι ι 𝕜} {M' : Matrix ι ι 𝕜} {s : 𝕜}
    (h : ∀ i j, HasDerivAt (fun u => M u i j) (M' i j) s) :
    HasDerivAt (fun u => (M u).det) ((M s).adjugate * M').trace s := by
  classical
  let sign (σ : Equiv.Perm ι) : 𝕜 := ((Equiv.Perm.sign σ : ℤˣ) : ℤ)
  let term (σ : Equiv.Perm ι) (j : ι) : 𝕜 :=
    (∏ k ∈ Finset.univ.erase j, M s (σ k) k) * M' (σ j) j
  have hd (σ : Equiv.Perm ι) : HasDerivAt
      (fun u => sign σ * ∏ i, M u (σ i) i) (sign σ * ∑ j, term σ j) s := by
    simpa only [term, smul_eq_mul] using
      (HasDerivAt.fun_finsetProd (fun i (_ : i ∈ Finset.univ) => h (σ i) i)).const_mul (sign σ)
  have hc (j : ι) :
      ((M s).updateCol j (fun i => M' i j)).det = ∑ σ, sign σ * term σ j := by
    rw [Matrix.det_apply']
    apply Finset.sum_congr rfl
    intro σ _
    congr 1
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    unfold term
    simp only [Matrix.updateCol_self]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    exact Matrix.updateCol_ne (Finset.ne_of_mem_erase hk)
  have htr : ((M s).adjugate * M').trace = ∑ j, ((M s).updateCol j (fun i => M' i j)).det := by
    simp only [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hsum := HasDerivAt.fun_sum (fun σ (_ : σ ∈ Finset.univ) => hd σ)
  have hfun : (fun u => (M u).det) = fun u => ∑ σ, sign σ * ∏ i, M u (σ i) i :=
    funext (fun u => Matrix.det_apply' (M u))
  rw [hfun, htr]
  simp_rw [hc]
  simp_rw [Finset.mul_sum] at hsum
  rw [Finset.sum_comm]
  exact hsum

theorem det_logDeriv {M : 𝕜 → Matrix ι ι 𝕜} {M' : Matrix ι ι 𝕜} {s : 𝕜}
    (h : ∀ i j, HasDerivAt (fun u => M u i j) (M' i j) s) (hdet : (M s).det ≠ 0) :
    deriv (fun u => (M u).det) s / (M s).det = ((M s)⁻¹ * M').trace := by
  have hu := isUnit_iff_ne_zero.mpr hdet
  have hadj : (M s).adjugate = (M s).det • (M s)⁻¹ := by
    calc
      _ = ((M s)⁻¹ * M s) * (M s).adjugate := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  rw [(det_hasDerivAt h).deriv, hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  exact mul_div_cancel_left₀ _ hdet

end RiemannResearch.Analysis.GramLogarithmicDerivative
