import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith

/-! The unweighted exact step realization of an absolutely summable sequence. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace RiemannResearch.Analysis

private def natStepCell (n : ℕ) : Set ℝ := Ico (n : ℝ) ((n : ℝ) + 1)

private theorem natStepCell_floor (n : ℕ) {x : ℝ}
    (hx : x ∈ natStepCell n) : ⌊x⌋₊ = n := Nat.floor_eq_on_Ico n x hx

private theorem natStepCell_disjoint : Pairwise (Function.onFun Disjoint natStepCell) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact hij ((natStepCell_floor i hxi).symm.trans (natStepCell_floor j hxj))

private theorem natStepCell_union : (⋃ n, natStepCell n) = Ici (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact (Nat.cast_nonneg n).trans hn.1
  · intro hx
    exact Set.mem_iUnion.mpr ⟨⌊x⌋₊, Nat.floor_le hx, Nat.lt_floor_add_one x⟩

private theorem natStep_integrable_cell (a : ℕ → ℝ) (n : ℕ) :
    IntegrableOn (fun x : ℝ => a ⌊x⌋₊) (natStepCell n) := by
  have hc : IntegrableOn (fun _ : ℝ => a n) (natStepCell n) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => a n)
      (Icc (n : ℝ) ((n : ℝ) + 1))).integrableOn_Icc.mono_set Ico_subset_Icc_self
  apply hc.congr
  filter_upwards [ae_restrict_mem (show MeasurableSet (natStepCell n) from measurableSet_Ico)]
    with x hx
  rw [natStepCell_floor n hx]

private theorem natStep_integral_cell (a : ℕ → ℝ) (n : ℕ) :
    (∫ x in natStepCell n, a ⌊x⌋₊) = a n := by
  calc
    _ = ∫ _x in natStepCell n, a n := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      change a ⌊x⌋₊ = a n
      rw [natStepCell_floor n hx]
    _ = _ := by
      unfold natStepCell
      rw [integral_Ico_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)]
      simp

private theorem natStep_integrable_Ici (a : ℕ → ℝ) (ha : Summable a) :
    IntegrableOn (fun x : ℝ => a ⌊x⌋₊) (Ici 0) := by
  rw [← natStepCell_union]
  apply integrableOn_iUnion_of_summable_integral_norm (natStep_integrable_cell a)
  convert! ha.norm using 1
  funext n
  exact natStep_integral_cell (fun k => ‖a k‖) n

/-- Ordinary Lebesgue integration of the complete unit-cell step function. -/
theorem integral_natStep_Ioi (a : ℕ → ℝ) (ha : Summable a) :
    (∫ x in Ioi (0 : ℝ), a ⌊x⌋₊) = ∑' n, a n := by
  rw [← integral_Ici_eq_integral_Ioi, ← natStepCell_union]
  rw [integral_iUnion (s := natStepCell) (fun _ => measurableSet_Ico)
    natStepCell_disjoint (by simpa only [natStepCell_union] using natStep_integrable_Ici a ha)]
  simp_rw [natStep_integral_cell]

/-- Exact rescaling, for every real positive mesh parameter. -/
theorem integral_scaled_natStep_Ioi (a : ℕ → ℝ) (ha : Summable a)
    (t : ℝ) (ht : 0 < t) :
    (∫ x in Ioi (0 : ℝ), a ⌊t * x⌋₊) = (∑' n, a n) / t := by
  have h := integral_comp_mul_right_Ioi (fun x : ℝ => a ⌊x⌋₊) 0 ht
  simpa only [zero_mul, mul_zero, smul_eq_mul, integral_natStep_Ioi a ha,
    div_eq_mul_inv, mul_comm] using! h

end RiemannResearch.Analysis
