import RiemannResearch.Analysis.ContractiveProductDefect
import RiemannResearch.RH.BurnolZeroProductConvergence

/-!
# A quadratic bound for the total reflected-zero defect

Burnol's product: https://arxiv.org/abs/math/9910055, Theorem 1.2.
The scalar zero discrepancy: https://arxiv.org/abs/math/9810169, page 3.
Here the formal result concerns the actual right-hand zeros and the actual
multiplicity-weighted scalar product. Its analytic identification with the
continuous Nyman projection is not assumed silently.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Burnol
open RiemannResearch.Analysis.ContractiveProductDefect

def quadraticZeroDefectTerm (ρ : RightZero) : ℝ :=
  (Zeta23.zeroMult ρ : ℝ) * defect (factorSq ρ)

theorem quadraticZeroDefectTerm_exact (ρ : RightZero) :
    quadraticZeroDefectTerm ρ = (Zeta23.zeroMult ρ : ℝ) *
      (2 * (ρ : ℂ).re - 1) ^ 2 /
        (Complex.normSq (ρ : ℂ) * Complex.normSq (1 - (ρ : ℂ))) := by
  have hρ : Complex.normSq (ρ : ℂ) ≠ 0 := by simpa using rightZero_ne_zero ρ
  have h1 : Complex.normSq (1 - (ρ : ℂ)) ≠ 0 := by
    simpa using (sub_ne_zero.mpr (Ne.symm (rightZero_ne_one ρ)))
  rw [quadraticZeroDefectTerm, defect_eq_sq_div
    (factorSq_pos (rightZero_ne_zero ρ) (rightZero_ne_one ρ)).ne',
    one_sub_factorSq (rightZero_ne_zero ρ)]
  unfold factorSq
  field_simp

theorem quadraticZeroDefectTerm_nonneg (ρ : RightZero) :
    0 ≤ quadraticZeroDefectTerm ρ := by
  exact mul_nonneg (Nat.cast_nonneg _)
    (defect_nonneg (factorSq_pos (rightZero_ne_zero ρ) (rightZero_ne_one ρ)))

theorem finite_quadraticZeroDefect_le (S : Finset RightZero) :
    ∑ ρ ∈ S, quadraticZeroDefectTerm ρ ≤ defect productSq := by
  calc
    _ ≤ defect (finiteProductSq S) := by
      exact weighted_sum_defect_le_product S (fun ρ => factorSq ρ)
        (fun ρ => Zeta23.zeroMult ρ)
        (fun ρ _ => factorSq_pos (rightZero_ne_zero ρ) (rightZero_ne_one ρ))
        (fun ρ _ => (factorSq_lt_one ρ.property.2).le)
    _ ≤ _ := defect_antitone productSq_pos (productSq_le_finiteProductSq S)
      (finiteProductSq_le_one S)

/-- Any certified lower bound for the scalar product gives a quadratic bound.
Connecting a finite Pareto gain to this lower bound requires the analytic
Burnol projection identity and the isometric embedding. -/
theorem finite_quadraticZeroDefect_le_certificate (S : Finset RightZero)
    {q : ℝ} (hq : 0 < q) (hcert : q ≤ productSq) :
    ∑ ρ ∈ S, quadraticZeroDefectTerm ρ ≤ (1 - q) ^ 2 / q := by
  have h := (finite_quadraticZeroDefect_le S).trans
    (defect_antitone hq hcert productSq_le_one)
  simpa only [defect_eq_sq_div hq.ne'] using h

theorem summable_quadraticZeroDefectTerm : Summable quadraticZeroDefectTerm := by
  exact summable_of_sum_le quadraticZeroDefectTerm_nonneg finite_quadraticZeroDefect_le

def quadraticZeroDefect : ℝ := ∑' ρ : RightZero, quadraticZeroDefectTerm ρ

theorem quadraticZeroDefect_le : quadraticZeroDefect ≤ defect productSq := by
  exact le_of_tendsto summable_quadraticZeroDefectTerm.hasSum
    (Filter.Eventually.of_forall finite_quadraticZeroDefect_le)

theorem quadraticZeroDefect_le_certificate {q : ℝ}
    (hq : 0 < q) (hcert : q ≤ productSq) :
    quadraticZeroDefect ≤ (1 - q) ^ 2 / q := by
  have h := quadraticZeroDefect_le.trans
    (defect_antitone hq hcert productSq_le_one)
  simpa only [defect_eq_sq_div hq.ne'] using h

end RiemannResearch.RH.Burnol
