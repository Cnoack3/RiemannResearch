import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.NormNum

/-!
# Forward and backward differences on coefficient l2
Source: the adjoint argument in the user-provided Pareto research note,
Section 2. This is the elementary real coefficient form of I-S and I-S*.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.CoefficientShift

abbrev Space := lp (fun _ : ℕ => ℝ) 2

theorem square_summable (a : Space) : Summable (fun n => (a n) ^ 2) := by
  have h := (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).mp a.property
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

def ofSquareSummable (a : ℕ → ℝ) (ha : Summable (fun n => a n ^ 2)) : Space :=
  ⟨a, memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
    Real.norm_eq_abs, sq_abs] using ha)⟩

def cons (A : ℝ) (a : Space) : Space :=
  ofSquareSummable (fun n => match n with | 0 => A | k + 1 => a k) (by
    apply (summable_nat_add_iff 1).mp
    simpa using square_summable a)

def leftShift (a : Space) : Space :=
  ofSquareSummable (fun n => a (n + 1))
    ((summable_nat_add_iff 1).mpr (square_summable a))

def rightShift (a : Space) : Space := cons 0 a

@[simp] theorem cons_zero (A : ℝ) (a : Space) : cons A a 0 = A := rfl
@[simp] theorem cons_succ (A : ℝ) (a : Space) (n : ℕ) : cons A a (n + 1) = a n := rfl
@[simp] theorem leftShift_apply (a : Space) (n : ℕ) : leftShift a n = a (n + 1) := rfl

def forwardDifference (a : Space) : Space := a - rightShift a
def backwardDifference (a : Space) : Space := a - leftShift a

@[simp] theorem backwardDifference_apply (a : Space) (n : ℕ) :
    backwardDifference a n = a n - a (n + 1) := rfl

theorem shift_inner (a b : Space) :
    inner ℝ (rightShift a) b = inner ℝ a (leftShift b) := by
  have hs := (lp.hasSum_inner (𝕜 := ℝ) (rightShift a) b).summable
  rw [lp.inner_eq_tsum, hs.tsum_eq_zero_add, lp.inner_eq_tsum]
  simp only [rightShift, cons_zero, cons_succ, inner_zero_left, zero_add, leftShift_apply]

theorem forward_backward_inner (a b : Space) :
    inner ℝ (forwardDifference a) b = inner ℝ a (backwardDifference b) := by
  simp only [forwardDifference, backwardDifference, inner_sub_left,
    inner_sub_right, shift_inner]

/-- Density removes every vector orthogonal to the differenced dictionary. -/
theorem backwardDifference_orthogonal_dense {ι : Type*} (v : ι → Space)
    (hdense : (Submodule.span ℝ (Set.range (fun i => forwardDifference (v i)))).topologicalClosure = ⊤)
    (b : Space) (hb : ∀ i, inner ℝ (backwardDifference b) (v i) = 0) : b = 0 := by
  let K := Submodule.span ℝ (Set.range (fun i => forwardDifference (v i)))
  have horth : b ∈ Kᗮ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [forward_backward_inner, real_inner_comm]
      exact hb i
    | zero => simp
    | add x y hx hy ihx ihy => simp [inner_add_left, ihx, ihy]
    | smul c x hx ih => simp [inner_smul_left, ih]
  have hdouble : b ∈ Kᗮᗮ := by
    rw [Submodule.orthogonal_orthogonal_eq_closure]
    change b ∈ (Submodule.span ℝ (Set.range (fun i => forwardDifference (v i)))).topologicalClosure
    rw [hdense]
    trivial
  exact (inner_self_eq_zero.mp (hdouble b horth))

end RiemannResearch.Analysis.CoefficientShift
