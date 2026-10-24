import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import RiemannResearch.Probability.DeterminantalSpectralCount
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Determinant bounds from a trace defect and a spectral gap

Source: elementary scalar logarithm bounds and Mathlib's Hermitian spectral
factorization. The application is conditioning on projected orthonormal probes
in the actual Q-Hilbert space. A uniform spectral gap is an explicit hypothesis;
this module does not prove that gap for arbitrary moving arithmetic probes.
-/

noncomputable section
open scoped BigOperators Classical

namespace RiemannResearch.LinearAlgebra.DeterminantTrace

/-- A scalar lower bound, uniform on `[ε,1]`. -/
theorem neg_defect_div_le_log {ε x : ℝ} (hε : 0 < ε)
    (hx : ε ≤ x) (hx1 : x ≤ 1) : -(1 - x) / ε ≤ Real.log x := by
  have hxpos : 0 < x := hε.trans_le hx
  have hdiv : (1 - x) / x ≤ (1 - x) / ε :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr hx1) hε hx
  have hlog : -(1 - x) / x ≤ Real.log x := by
    calc
      -(1 - x) / x = 1 - x⁻¹ := by field_simp; ring
      _ ≤ Real.log x := Real.one_sub_inv_le_log_of_pos hxpos
  have hneg : -(1 - x) / ε ≤ -(1 - x) / x := by
    simpa only [neg_div] using neg_le_neg hdiv
  exact hneg.trans hlog

/-- No dimension factor occurs: only the total defect and common spectral gap. -/
theorem exp_neg_defect_div_le_prod {ι : Type*} [Fintype ι]
    (x : ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hx : ∀ i, ε ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    Real.exp (-(∑ i, (1 - x i)) / ε) ≤ ∏ i, x i := by
  have he : -(∑ i, (1 - x i)) / ε = ∑ i, (-(1 - x i) / ε) := by
    calc
      _ = (∑ i, (1 - x i)) * (-ε⁻¹) := by ring
      _ = ∑ i, (1 - x i) * (-ε⁻¹) := Finset.sum_mul ..
      _ = _ := by apply Finset.sum_congr rfl; intro i _; ring
  rw [he, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i _
    exact (Real.exp_pos _).le
  · intro i _
    rw [← Real.le_log_iff_exp_le (hε.trans_le (hx i))]
    exact neg_defect_div_le_log hε (hx i) (hx1 i)

/-- The complementary trace is also a necessary control for positive mass. -/
theorem prod_le_exp_neg_defect {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i) :
    (∏ i, x i) ≤ Real.exp (-(∑ i, (1 - x i))) := by
  have he : -(∑ i, (1 - x i)) = ∑ i, (x i - 1) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  rw [he, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i _
    exact hx0 i
  · intro i _
    have h := Real.add_one_le_exp (x i - 1)
    linarith

end RiemannResearch.LinearAlgebra.DeterminantTrace

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- Exact spectral expression for the trace defect. -/
theorem IsHermitian.trace_defect_eq_sum (hA : A.IsHermitian) :
    (1 - A).trace = ∑ i, (1 - hA.eigenvalues i) := by
  rw [Matrix.trace_sub, Matrix.trace_one, hA.trace_eq_sum_eigenvalues]
  simp

/-- Positive contraction determinant lower bound using a spectral gap. -/
theorem PosSemidef.exp_neg_trace_defect_div_le_det
    (hA : A.PosSemidef) (hI : (1 - A).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (hgap : ∀ i, ε ≤ hA.isHermitian.eigenvalues i) :
    Real.exp (-(1 - A).trace / ε) ≤ A.det := by
  rw [hA.isHermitian.trace_defect_eq_sum, hA.isHermitian.det_eq_prod_eigenvalues]
  exact RiemannResearch.LinearAlgebra.DeterminantTrace.exp_neg_defect_div_le_prod
    _ hε hgap (hA.eigenvalues_le_one hI)

/-- An upper exponential bound, retaining the exact trace defect. -/
theorem PosSemidef.det_le_exp_neg_trace_defect (hA : A.PosSemidef) :
    A.det ≤ Real.exp (-(1 - A).trace) := by
  rw [hA.isHermitian.trace_defect_eq_sum, hA.isHermitian.det_eq_prod_eigenvalues]
  exact RiemannResearch.LinearAlgebra.DeterminantTrace.prod_le_exp_neg_defect
    _ hA.eigenvalues_nonneg

/-- Uniformly positive determinant forces a bounded trace defect. -/
theorem PosSemidef.trace_defect_le_neg_log_of_det_ge
    (hA : A.PosSemidef) {δ : ℝ} (hδ : 0 < δ) (hmass : δ ≤ A.det) :
    (1 - A).trace ≤ -Real.log δ := by
  have h := hmass.trans hA.det_le_exp_neg_trace_defect
  have hh := (Real.log_le_iff_le_exp hδ).mpr h
  linarith

end Matrix


noncomputable section
open Filter
open scoped BigOperators Classical

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- A positive contraction's determinant cannot exceed any one eigenvalue. -/
theorem PosSemidef.det_le_eigenvalue (hA : A.PosSemidef)
    (hI : (1 - A).PosSemidef) (i : ι) :
    A.det ≤ hA.isHermitian.eigenvalues i := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  calc
    _ ≤ ∏ j : ι, (if j = i then hA.isHermitian.eigenvalues i else 1) := by
      apply Finset.prod_le_prod
      · intro j _; exact hA.eigenvalues_nonneg j
      · intro j _
        by_cases hj : j = i
        · simp [hj]
        · simpa [hj] using hA.eigenvalues_le_one hI j
    _ = _ := by simp

/-- Positive inclusion mass automatically supplies a spectral gap. -/
theorem PosSemidef.eigenvalue_ge_of_det_ge (hA : A.PosSemidef)
    (hI : (1 - A).PosSemidef) {δ : ℝ} (hmass : δ ≤ A.det) (i : ι) :
    δ ≤ hA.isHermitian.eigenvalues i :=
  hmass.trans (hA.det_le_eigenvalue hI i)

/-- Uniform positive conditioning mass is quantitatively equivalent to a
bounded total trace defect plus a uniform spectral gap. The index type may
vary with the parameter, so this statement allows growing probe families. -/
theorem uniform_det_pos_iff_trace_bound_and_gap
    {α : Type*} {l : Filter α} (ι : α → Type*)
    [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)]
    (A : ∀ a, Matrix (ι a) (ι a) ℝ)
    (hA : ∀ a, (A a).PosSemidef) (hI : ∀ a, (1 - A a).PosSemidef) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ a in l, δ ≤ (A a).det) ↔
      ∃ C ε : ℝ, 0 < ε ∧ ∀ᶠ a in l,
        (1 - A a).trace ≤ C ∧ ∀ i, ε ≤ (hA a).isHermitian.eigenvalues i := by
  constructor
  · rintro ⟨δ, hδ, hm⟩
    refine ⟨-Real.log δ, δ, hδ, ?_⟩
    filter_upwards [hm] with a ha
    exact ⟨(hA a).trace_defect_le_neg_log_of_det_ge hδ ha,
      (hA a).eigenvalue_ge_of_det_ge (hI a) ha⟩
  · rintro ⟨C, ε, hε, hb⟩
    refine ⟨Real.exp (-C / ε), Real.exp_pos _, ?_⟩
    filter_upwards [hb] with a ha
    have hexp : Real.exp (-C / ε) ≤ Real.exp (-(1 - A a).trace / ε) := by
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (neg_le_neg ha.1) hε.le
    exact hexp.trans ((hA a).exp_neg_trace_defect_div_le_det (hI a) hε ha.2)

end Matrix
