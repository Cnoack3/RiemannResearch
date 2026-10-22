import RiemannResearch.Analysis.ContractiveProducts
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exact quadratic defects of contractive products

Source: elementary algebra developed for the user's comparison of finite
Pareto Gram certificates with Burnol's zero product and finite Weil forms.
The multiplication identity retains the complete nonnegative interaction.
No analytic projection identity or assertion of RH is assumed or proved.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.ContractiveProductDefect

def defect (p : ℝ) : ℝ := p + 1 / p - 2

theorem defect_eq_sq_div {p : ℝ} (hp : p ≠ 0) :
    defect p = (1 - p) ^ 2 / p := by
  unfold defect
  field_simp
  ring

theorem defect_nonneg {p : ℝ} (hp : 0 < p) : 0 ≤ defect p := by
  rw [defect_eq_sq_div hp.ne']
  positivity

theorem defect_mul_exact {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    defect (p * q) = defect p + defect q +
      (1 - p) * (1 - q) * (1 + p * q) / (p * q) := by
  unfold defect
  field_simp
  ring

theorem defect_mul_superadditive {p q : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    defect p + defect q ≤ defect (p * q) := by
  rw [defect_mul_exact hp.ne' hq.ne']
  have : 0 ≤ (1 - p) * (1 - q) * (1 + p * q) / (p * q) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1))
        (by positivity)
    · positivity
  linarith

theorem defect_sub_exact {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    defect p - defect q = (q - p) * (1 - p * q) / (p * q) := by
  unfold defect
  field_simp
  ring

theorem defect_antitone {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hq1 : q ≤ 1) :
    defect q ≤ defect p := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hp1 : p ≤ 1 := hpq.trans hq1
  have hpq1 : p * q ≤ 1 := by nlinarith
  have h := defect_sub_exact hp.ne' hq.ne'
  have hnon : 0 ≤ (q - p) * (1 - p * q) / (p * q) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hpq1))
      (mul_pos hp hq).le
  linarith

theorem sum_defect_le_defect_prod {ι : Type*} (S : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ S, 0 < p i) (hp1 : ∀ i ∈ S, p i ≤ 1) :
    ∑ i ∈ S, defect (p i) ≤ defect (∏ i ∈ S, p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => norm_num [defect]
  | @insert a S ha ih =>
    have hS : ∀ i ∈ S, 0 < p i := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hS1 : ∀ i ∈ S, p i ≤ 1 := fun i hi => hp1 i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    apply (add_le_add (le_refl (defect (p a))) (ih hS hS1)).trans
    exact (defect_mul_superadditive (hp a (Finset.mem_insert_self _ _))
        (hp1 a (Finset.mem_insert_self _ _))
        (Finset.prod_pos hS) (Finset.prod_le_one (fun i hi => (hS i hi).le) hS1))

theorem mul_defect_le_defect_pow {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (n : ℕ) :
    (n : ℝ) * defect p ≤ defect (p ^ n) := by
  induction n with
  | zero => norm_num [defect]
  | succ n ih =>
    have hn := defect_mul_superadditive (pow_pos hp n)
      (pow_le_one₀ hp.le hp1) hp hp1
    rw [pow_succ]
    push_cast
    nlinarith

theorem weighted_sum_defect_le_product {ι : Type*} (S : Finset ι)
    (p : ι → ℝ) (m : ι → ℕ)
    (hp : ∀ i ∈ S, 0 < p i) (hp1 : ∀ i ∈ S, p i ≤ 1) :
    ∑ i ∈ S, (m i : ℝ) * defect (p i) ≤
      defect (∏ i ∈ S, p i ^ m i) := by
  calc
    _ ≤ ∑ i ∈ S, defect (p i ^ m i) := Finset.sum_le_sum fun i hi =>
      mul_defect_le_defect_pow (hp i hi) (hp1 i hi) (m i)
    _ ≤ _ := sum_defect_le_defect_prod S _
      (fun i hi => pow_pos (hp i hi) _) (fun i hi => pow_le_one₀ (hp i hi).le (hp1 i hi))

/-- The complete finite interaction telescope, with every remainder retained. -/
theorem defect_partialProduct_exact (p : ℕ → ℝ) (hp : ∀ k, p k ≠ 0) (N : ℕ) :
    defect (Real.partialProduct p N) =
      (∑ k ∈ Finset.range N, defect (p k)) +
      ∑ k ∈ Finset.range N,
        (1 - Real.partialProduct p k) * (1 - p k) *
          (1 + Real.partialProduct p k * p k) / (Real.partialProduct p k * p k) := by
  induction N with
  | zero => norm_num [defect]
  | succ N ih =>
    have hn : Real.partialProduct p N ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun k _ => hp k)
    rw [Real.partialProduct_succ, defect_mul_exact hn (hp N), ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

end RiemannResearch.Analysis.ContractiveProductDefect
