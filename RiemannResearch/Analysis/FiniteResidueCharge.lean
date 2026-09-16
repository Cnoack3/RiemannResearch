import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Finite charge identity for residue moments
Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`.
Interpolation coefficients are constructed at distinct squared nodes. This
module does not claim that the Laplace expansion or support count is formalized.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteResidueCharge
variable {ι : Type*} [Fintype ι]

def moment (b n : ι → ℝ) (j : ℕ) : ℝ := ∑ i, b i * n i ^ (2*j)
def constantTerm (b n : ι → ℝ) : ℝ := 1-(1/2:ℝ)*(∑ i, b i*n i)

theorem charge_identity (b n : ι → ℝ) (c : ℕ → ℝ) (k : ℕ)
    (hzero : ∑ i, b i = 0)
    (hinterp : ∀ i, n i = c 0 + ∑ j ∈ Finset.range k, c (j+1)*n i^(2*(j+1))) :
    1 = constantTerm b n +
      (1/2:ℝ)*∑ j ∈ Finset.range k, c (j+1)*moment b n (j+1) := by
  have he : (∑ i, b i*n i) =
      ∑ j ∈ Finset.range k, c (j+1)*moment b n (j+1) := by
    calc
      _ = ∑ i, b i * (c 0 + ∑ j ∈ Finset.range k, c (j+1)*n i^(2*(j+1))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hinterp i]
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hzero, zero_mul, zero_add]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        unfold moment
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  unfold constantTerm
  rw [he]
  ring

/-- If the constant charge vanishes, a nonzero finite moment must remain.
The interpolation coefficients are not bounded by this algebraic result. -/
theorem exists_nonzero_moment (b n : ι → ℝ) (c : ℕ → ℝ) (k : ℕ)
    (hzero : ∑ i, b i = 0)
    (hinterp : ∀ i, n i = c 0 + ∑ j ∈ Finset.range k, c (j+1)*n i^(2*(j+1)))
    (ha : constantTerm b n = 0) :
    ∃ j < k, moment b n (j+1) ≠ 0 := by
  by_contra h
  push Not at h
  have he := charge_identity b n c k hzero hinterp
  have hs : (∑ j ∈ Finset.range k, c (j+1)*moment b n (j+1)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [h j (Finset.mem_range.mp hj), mul_zero]
  rw [ha, hs] at he
  norm_num at he

/-- The interpolation coefficients are constructed, rather than postulated,
when the squared nodes are distinct. -/
theorem interpolation_coefficients (n : ι → ℝ)
    (hinj : Function.Injective (fun i => (n i)^2)) (hs : 0 < Fintype.card ι) :
    ∃ c : ℕ → ℝ, ∀ i, n i = c 0 +
      ∑ j ∈ Finset.range (Fintype.card ι-1), c (j+1)*n i^(2*(j+1)) := by
  classical
  let P := Lagrange.interpolate Finset.univ (fun i => (n i)^2) n
  have hi : Set.InjOn (fun i => (n i)^2) (↑(Finset.univ : Finset ι)) :=
    hinj.injOn
  have hd : P.natDegree ≤ Fintype.card ι-1 :=
    Polynomial.natDegree_le_of_degree_le (by
      simpa only [Finset.card_univ] using Lagrange.degree_interpolate_le n hi)
  have hlt : P.natDegree < Fintype.card ι := by omega
  refine ⟨P.coeff, fun i => ?_⟩
  have he := Polynomial.eval₂_eq_sum_range' (RingHom.id ℝ) hlt ((n i)^2)
  change P.eval ((n i)^2) =
    ∑ j ∈ Finset.range (Fintype.card ι), P.coeff j * ((n i)^2)^j at he
  have hv : P.eval ((n i)^2) = n i :=
    Lagrange.eval_interpolate_at_node n hi (Finset.mem_univ i)
  rw [hv] at he
  conv_lhs => rw [he]
  conv_lhs =>
    rw [show Fintype.card ι = (Fintype.card ι-1)+1 by omega, Finset.sum_range_succ']
  simp only [pow_zero, mul_one, ← pow_mul]
  ring

/-- Finite moment forcing, with no coefficient-conditioning claim. -/
theorem finite_moment_forcing (b n : ι → ℝ)
    (hinj : Function.Injective (fun i => (n i)^2))
    (hs : 0 < Fintype.card ι) (hzero : ∑ i, b i = 0)
    (ha : constantTerm b n = 0) :
    ∃ j < Fintype.card ι-1, moment b n (j+1) ≠ 0 := by
  obtain ⟨c, hc⟩ := interpolation_coefficients n hinj hs
  exact exists_nonzero_moment b n c _ hzero hc ha

/-- The claimed numerical ceiling for the first odd moment index follows
from the support-size bound. The Taylor/Laplace identification is separate. -/
theorem moment_index_bound (b n : ι → ℝ) (M : ℕ)
    (hinj : Function.Injective (fun i => (n i)^2))
    (hs : 0 < Fintype.card ι) (hsize : Fintype.card ι ≤ 2*M+1)
    (hzero : ∑ i, b i = 0) (ha : constantTerm b n = 0) :
    ∃ j, moment b n (j+1) ≠ 0 ∧ 2*j+1 ≤ 4*M-1 := by
  obtain ⟨j, hj, hm⟩ := finite_moment_forcing b n hinj hs hzero ha
  exact ⟨j, hm, by omega⟩

end RiemannResearch.Analysis.FiniteResidueCharge
