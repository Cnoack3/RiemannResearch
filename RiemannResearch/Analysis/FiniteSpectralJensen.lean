import RiemannResearch.Analysis.FiniteSpectralMomentUpper
import RiemannResearch.Analysis.FiniteSpectralBudget
import RiemannResearch.Analysis.FiniteSpectralDoubleLog
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Jensen lower bound for complete correction-weighted moments

Source: user-requested backwards RH verification, 13 October 2026.
These conditional deductions are independently formalized, without a novelty claim.
No missing arithmetic bound is asserted.
-/

noncomputable section
open Set
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.FiniteSpectralBudget

def reciprocalDoubleLog (x : ℝ) : ℝ := Real.log (1 - Real.log x)

theorem reciprocalDoubleLog_hasDerivAt {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    HasDerivAt reciprocalDoubleLog (-(x * (1 - Real.log x))⁻¹) x := by
  have hb : 0 < 1 - Real.log x := by
    have hl := Real.log_nonpos hx.le hx1
    linarith
  have hd := ((Real.hasDerivAt_log hx.ne').const_sub (1 : ℝ)).log hb.ne'
  change HasDerivAt (fun y : ℝ => Real.log (1 - Real.log y))
    (-(x * (1 - Real.log x))⁻¹) x
  have he : -(x * (1 - Real.log x))⁻¹ = -x⁻¹ / (1 - Real.log x) := by
    simp only [mul_inv_rev, div_eq_mul_inv]
    ring
  rw [he]
  exact hd

theorem reciprocalDoubleLog_deriv_hasDerivAt {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    HasDerivAt (fun y : ℝ => -(y * (1 - Real.log y))⁻¹)
      (-Real.log x / (x * (1 - Real.log x)) ^ 2) x := by
  have hb : 0 < 1 - Real.log x := by
    have hl := Real.log_nonpos hx.le hx1
    linarith
  have hg : HasDerivAt (fun y : ℝ => y * (1 - Real.log y)) (-Real.log x) x := by
    have hp := (hasDerivAt_id x).mul
      ((Real.hasDerivAt_log hx.ne').const_sub (1 : ℝ))
    change HasDerivAt (fun y : ℝ => y * (1 - Real.log y))
      (1 * (1 - Real.log x) + x * (-x⁻¹)) x at hp
    have he : 1 * (1 - Real.log x) + x * (-x⁻¹) = -Real.log x := by
      rw [one_mul, mul_neg, mul_inv_cancel₀ hx.ne']
      ring
    rw [he] at hp
    exact hp
  have hd := (hg.inv (mul_ne_zero hx.ne' hb.ne')).neg
  change HasDerivAt (fun y : ℝ => -(y * (1 - Real.log y))⁻¹)
    (-(-(-Real.log x) / (x * (1 - Real.log x)) ^ 2)) x at hd
  have he : -(-(-Real.log x) / (x * (1 - Real.log x)) ^ 2) =
      -Real.log x / (x * (1 - Real.log x)) ^ 2 := by ring
  rw [he] at hd
  exact hd

theorem reciprocalDoubleLog_convexOn :
    ConvexOn ℝ (Ioc (0 : ℝ) 1) reciprocalDoubleLog := by
  have hc : ContinuousOn reciprocalDoubleLog (Ioc (0 : ℝ) 1) := by
    intro x hx
    exact (reciprocalDoubleLog_hasDerivAt hx.1 hx.2).continuousAt.continuousWithinAt
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := fun x : ℝ => -(x * (1 - Real.log x))⁻¹)
    (f'' := fun x : ℝ => -Real.log x / (x * (1 - Real.log x)) ^ 2)
    (convex_Ioc (0 : ℝ) 1) hc ?_ ?_ ?_
  · intro x hx
    have hm : x ∈ Ioc (0 : ℝ) 1 := interior_subset hx
    exact (reciprocalDoubleLog_hasDerivAt hm.1 hm.2).hasDerivWithinAt
  · intro x hx
    have hm : x ∈ Ioc (0 : ℝ) 1 := interior_subset hx
    exact (reciprocalDoubleLog_deriv_hasDerivAt hm.1 hm.2).hasDerivWithinAt
  · intro x hx
    have hm : x ∈ Ioc (0 : ℝ) 1 := interior_subset hx
    exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos hm.1.le hm.2)) (sq_nonneg _)

/-- Jensen in the raw correction weights; no normalized probabilities required. -/
theorem reciprocalDoubleLog_weighted_jensen {ι : Type*}
    (s : Finset ι) (c x : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (hT : 0 < ∑ i ∈ s, c i)
    (hx : ∀ i ∈ s, 0 < x i ∧ x i ≤ 1) :
    (∑ i ∈ s, c i) *
        Real.log (1 - Real.log ((∑ i ∈ s, c i * x i) / (∑ i ∈ s, c i))) ≤
      ∑ i ∈ s, c i * Real.log (1 - Real.log (x i)) := by
  let T : ℝ := ∑ i ∈ s, c i
  let S : ℝ := ∑ i ∈ s, c i * x i
  let J : ℝ := ∑ i ∈ s, c i * Real.log (1 - Real.log (x i))
  have h := reciprocalDoubleLog_convexOn.map_centerMass_le hc hT hx
  have hn : Real.log (1 - Real.log (S / T)) ≤ J / T := by
    simpa only [Finset.centerMass, smul_eq_mul, Function.comp_apply,
      reciprocalDoubleLog, T, S, J, div_eq_mul_inv, mul_comm] using h
  change T * Real.log (1 - Real.log (S / T)) ≤ J
  calc
    _ = Real.log (1 - Real.log (S / T)) * T := mul_comm _ _
    _ ≤ J := (le_div_iff₀ hT).mp hn

/-- The quotient form used with T=correction and S=optimizerTail. -/
theorem correction_weighted_doubleLog_jensen {ι : Type*}
    (s : Finset ι) (c x : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (hT : 0 < ∑ i ∈ s, c i)
    (hS : 0 < ∑ i ∈ s, c i * x i)
    (hx : ∀ i ∈ s, 0 < x i ∧ x i ≤ 1) :
    (∑ i ∈ s, c i) *
        Real.log (1 + Real.log ((∑ i ∈ s, c i) / (∑ i ∈ s, c i * x i))) ≤
      ∑ i ∈ s, c i * Real.log (1 - Real.log (x i)) := by
  have he :
      1 + Real.log ((∑ i ∈ s, c i) / (∑ i ∈ s, c i * x i)) =
        1 - Real.log ((∑ i ∈ s, c i * x i) / (∑ i ∈ s, c i)) := by
    rw [Real.log_div hT.ne' hS.ne', Real.log_div hS.ne' hT.ne']
    ring
  rw [he]
  exact reciprocalDoubleLog_weighted_jensen s c x hc hT hx

end RiemannResearch.Analysis.FiniteSpectralBudget

namespace RiemannResearch.Analysis.FiniteSpectralBudget
open scoped BigOperators

/-- Exact finite Jensen lower bound for the literal correction and optimizer tail. -/
theorem correctionDoubleLog_ge_jensen {ι : Type*}
    (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hT : 0 < correction s w lam) :
    correction s w lam *
        Real.log (1 + Real.log (correction s w lam / optimizerTail s w lam)) ≤
      correctionDoubleLog s w lam := by
  let c : ι → ℝ := fun i => w i * lam i / (1 + lam i)
  let x : ι → ℝ := fun i => 1 / (1 + lam i)
  have hc : ∀ i ∈ s, 0 ≤ c i := by
    intro i hi
    exact div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (by linarith [hlam i hi])
  have hx : ∀ i ∈ s, 0 < x i ∧ x i ≤ 1 := by
    intro i hi
    have hd : 0 < 1 + lam i := by linarith [hlam i hi]
    constructor
    · exact div_pos zero_lt_one hd
    · apply (div_le_iff₀ hd).mpr
      linarith [hlam i hi]
  have hsumc : (∑ i ∈ s, c i) = correction s w lam := rfl
  have hsumcx : (∑ i ∈ s, c i * x i) = optimizerTail s w lam := by
    unfold optimizerTail
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [c, x]
    have hd : 1 + lam i ≠ 0 := ne_of_gt (by linarith [hlam i hi])
    field_simp [hd]
    <;> ring
  have hcpos : 0 < ∑ i ∈ s, c i := by simpa only [hsumc] using hT
  have hex : ∃ i ∈ s, 0 < c i := by
    by_contra! hh
    have hz : (∑ i ∈ s, c i) ≤ 0 := Finset.sum_nonpos hh
    exact (not_le_of_gt hcpos) hz
  obtain ⟨i, hi, hci⟩ := hex
  have hSpos : 0 < ∑ j ∈ s, c j * x j :=
    lt_of_lt_of_le (mul_pos hci (hx i hi).1)
      (Finset.single_le_sum (fun j hj => mul_nonneg (hc j hj) (hx j hj).1.le) hi)
  have hJ : (∑ i ∈ s, c i * Real.log (1 - Real.log (x i))) =
      correctionDoubleLog s w lam := by
    simp only [x, one_div, Real.log_inv, sub_neg_eq_add]
    rfl
  have hj := correction_weighted_doubleLog_jensen s c x hc hcpos hSpos hx
  rw [hsumc, hsumcx, hJ] at hj
  exact hj

/-- The full source moment satisfies the same lower bound. -/
theorem doubleLog_moment_ge_jensen {ι : Type*}
    (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hT : 0 < correction s w lam) :
    correction s w lam *
        Real.log (1 + Real.log (correction s w lam / optimizerTail s w lam)) ≤
      moment s w lam doubleLog := by
  rw [moment_eq_correctionDoubleLog_add_remainder s w lam hlam]
  exact (correctionDoubleLog_ge_jensen s w lam hw hlam hT).trans
    (le_add_of_nonneg_right (doubleLogRemainder_nonneg s w lam hw hlam))

end RiemannResearch.Analysis.FiniteSpectralBudget

namespace RiemannResearch.Analysis.FiniteSpectralBudget
open scoped BigOperators

theorem optimizerTail_pos_of_correction_pos_jensen {ι : Type*}
    (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hT : 0 < correction s w lam) : 0 < optimizerTail s w lam := by
  have hex : ∃ i ∈ s, 0 < w i * lam i / (1 + lam i) := by
    by_contra! hh
    have hz : correction s w lam ≤ 0 := Finset.sum_nonpos hh
    exact (not_le_of_gt hT) hz
  obtain ⟨i, hi, hci⟩ := hex
  have hd : 0 < 1 + lam i := by linarith [hlam i hi]
  have hp : 0 < w i * lam i := by
    have hh := mul_pos hci hd
    simpa only [div_mul_cancel₀ _ hd.ne'] using hh
  have hterm : 0 < w i * lam i / (1 + lam i) ^ 2 :=
    div_pos hp (sq_pos_of_pos hd)
  change 0 < ∑ j ∈ s, w j * lam j / (1 + lam j) ^ 2
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum (fun j hj =>
      div_nonneg (mul_nonneg (hw j hj) (hlam j hj)) (sq_nonneg (1 + lam j))) hi)

/-- Jensen after replacing the tail by any positive upper envelope. -/
theorem correctionDoubleLog_ge_envelope_jensen {ι : Type*}
    (s : Finset ι) (w lam : ι → ℝ) (sigma : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hT : 0 < correction s w lam) (hsigma : 0 < sigma)
    (hS : optimizerTail s w lam ≤ sigma)
    (hinside : 0 < (1 + Real.log (1 / sigma)) + Real.log (correction s w lam)) :
    correction s w lam *
        Real.log ((1 + Real.log (1 / sigma)) + Real.log (correction s w lam)) ≤
      correctionDoubleLog s w lam := by
  have hSp : 0 < optimizerTail s w lam :=
    optimizerTail_pos_of_correction_pos_jensen s w lam hw hlam hT
  have hratio : correction s w lam / sigma ≤
      correction s w lam / optimizerTail s w lam :=
    div_le_div_of_nonneg_left hT.le hSp hS
  have hlog := Real.log_le_log (div_pos hT hsigma) hratio
  have hid : 1 + Real.log (correction s w lam / sigma) =
      (1 + Real.log (1 / sigma)) + Real.log (correction s w lam) := by
    rw [Real.log_div hT.ne' hsigma.ne']
    simp only [one_div, Real.log_inv]
    ring
  have hinner : (1 + Real.log (1 / sigma)) + Real.log (correction s w lam) ≤
      1 + Real.log (correction s w lam / optimizerTail s w lam) := by
    rw [← hid]
    linarith
  exact (mul_le_mul_of_nonneg_left (Real.log_le_log hinside hinner) hT.le).trans
    (correctionDoubleLog_ge_jensen s w lam hw hlam hT)

end RiemannResearch.Analysis.FiniteSpectralBudget
