import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Tactic.NormNum

/-!
# Indicator uniqueness does not imply signed annihilator uniqueness

Source: user-provided argument and the ensuing two-point counterexample,
September 11, 2026. This supports the logical distinction needed in
RH/ParetoAnnihilatorPositivity: monotone approximation does not imply that
indicators of level sets of an annihilator still annihilate the test space.

On two equally weighted points, testing against constants is equivalent to
having mean zero. No nonempty indicator has mean zero, but (1,-1) does.
-/
namespace RiemannResearch.Analysis.IndicatorAnnihilator
noncomputable section
def twoPointMean (h : Bool → ℝ) : ℝ := (h false + h true) / 2

def signedWitness (b : Bool) : ℝ := if b then -1 else 1

theorem indicator_mean_eq_zero_iff (s : Set Bool) :
    twoPointMean (s.indicator (fun _ => (1 : ℝ))) = 0 ↔ s = ∅ := by
  classical
  constructor
  · intro hs
    have hf : false ∉ s := by
      intro hf
      by_cases ht : true ∈ s <;> norm_num [twoPointMean, Set.indicator_apply, hf, ht] at hs
    have ht : true ∉ s := by
      intro ht
      norm_num [twoPointMean, Set.indicator_apply, hf, ht] at hs
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b
    cases b
    · exact hf
    · exact ht
  · rintro rfl
    simp [twoPointMean]

theorem signedWitness_mean : twoPointMean signedWitness = 0 := by
  norm_num [twoPointMean, signedWitness]

theorem signedWitness_ne_zero : signedWitness ≠ 0 := by
  intro h
  have hf := congrFun h false
  norm_num [signedWitness] at hf

theorem signedWitness_abs_mean :
    twoPointMean (fun b => |signedWitness b|) = 1 := by
  norm_num [twoPointMean, signedWitness]

theorem signedWitness_positive_indicator_mean :
    twoPointMean ({b | 0 < signedWitness b}.indicator (fun _ => (1 : ℝ))) = 1 / 2 := by
  norm_num [twoPointMean, signedWitness, Set.indicator_apply]

theorem mean_zero_not_abs_closed :
    ¬ (∀ h : Bool → ℝ, twoPointMean h = 0 →
      twoPointMean (fun b => |h b|) = 0) := by
  intro hc
  have hx := hc signedWitness signedWitness_mean
  rw [signedWitness_abs_mean] at hx
  norm_num at hx

theorem indicator_uniqueness_does_not_imply_signed_uniqueness :
    (∀ s : Set Bool, twoPointMean (s.indicator (fun _ => (1 : ℝ))) = 0 → s = ∅) ∧
    (∃ h : Bool → ℝ, twoPointMean h = 0 ∧ h ≠ 0) :=
  ⟨fun s => (indicator_mean_eq_zero_iff s).mp,
    signedWitness, signedWitness_mean, signedWitness_ne_zero⟩
end
end RiemannResearch.Analysis.IndicatorAnnihilator
