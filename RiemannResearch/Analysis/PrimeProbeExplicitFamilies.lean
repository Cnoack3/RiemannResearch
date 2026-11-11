import RiemannResearch.Analysis.PrimeProbeBudgetObstruction
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Explicit probes beyond the small absolute FMZ budget

Source: elementary finite characteristic-function calculations from the
November 11, 2026 microscopic-budget investigation. The two-mode and
three-mode families have variance proportional to the square of their
frequency scale and explicit nonconstant microscopic profiles. The exact
two-mode rational pair budget records why the existing absolute criterion
does not apply. Signed spectral weights can give negative variance and
negative two-site repulsion, so replacing positive feature weights by
arbitrary signs is not a DPP construction. No actual-zero asymptotic is used.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate

theorem two_mode_variance (a : ℝ) :
    spectralVariance ![0, a] (fun _ : Fin 2 => (1 / 2 : ℝ)) = a^2 / 4 := by
  simp [spectralVariance, Fin.sum_univ_two]
  ring

theorem two_mode_repulsion (a t : ℝ) :
    probeRepulsion ![0, a] (fun _ : Fin 2 => (1 / 2 : ℝ)) t =
      (1 - Real.cos (a*t)) / 2 := by
  rw [probeRepulsion_exact _ _ (by norm_num [Fin.sum_univ_two])]
  simp [Fin.sum_univ_two, Real.cos_neg]
  ring

theorem two_mode_microscopic (a u : ℝ) (ha : a ≠ 0) :
    probeRepulsion ![0, a] (fun _ : Fin 2 => (1 / 2 : ℝ)) (u/a) =
      (1 - Real.cos u) / 2 := by
  rw [two_mode_repulsion]
  congr 3
  field_simp

theorem two_mode_rationalPairBudget (n : ℕ) (hn : 1 ≤ n) :
    rationalPairBudget ![1,n] (fun _ : Fin 2 => 1)
      (fun _ : Fin 2 => (1/2 : ℝ)) =
      1 + 2 * Real.log n + 3 / 2 * (Real.log n)^2 := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  simp [rationalPairBudget, rationalModeWeight, Fin.sum_univ_two,
    abs_of_nonneg hlog, abs_of_nonneg (add_nonneg hlog hlog)]
  ring

theorem signed_weights_negative_variance (a : ℝ) :
    spectralVariance ![0,a] ![2,-1] = -2 * a^2 := by
  simp [spectralVariance, Fin.sum_univ_two]

theorem three_mode_variance (a : ℝ) :
    spectralVariance ![0,a,2*a] ![1/4,1/2,1/4] = a^2/2 := by
  norm_num [spectralVariance, Fin.sum_univ_succ]
  ring

theorem three_mode_repulsion (a t : ℝ) :
    probeRepulsion ![0,a,2*a] ![1/4,1/2,1/4] t =
      (5 - 4 * Real.cos (a*t) - Real.cos (2*a*t))/8 := by
  rw [probeRepulsion_exact _ _ (by norm_num [Fin.sum_univ_succ])]
  norm_num [Fin.sum_univ_succ, show a-2*a = -a by ring,
    show 2*a-a=a by ring, Real.cos_neg]
  <;> ring

theorem signed_weights_repulsion (a t : ℝ) :
    probeRepulsion ![0,a] ![2,-1] t = -4 * (1 - Real.cos (a*t)) := by
  rw [probeRepulsion_exact _ _ (by norm_num [Fin.sum_univ_two])]
  simp [Fin.sum_univ_two, Real.cos_neg]
  <;> ring

#print axioms two_mode_microscopic
#print axioms two_mode_rationalPairBudget
end RiemannResearch.Analysis.MontgomeryFormFactor
