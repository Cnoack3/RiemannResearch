import RiemannResearch.RH.CountableTiltDetector
import RiemannResearch.RH.WeilExplicitFormula.Statement.Seam
import Mathlib.Tactic.Linarith

/-!
# A detector for the actual nontrivial zeta zeros

Source: the user's standard countability observation and the existing
countable-tilt construction. Countability is supplied by the proved finite
zero windows. This closes a formal assembly gap; it asserts no new growth
estimate and makes no novelty claim.
-/

open MeasureTheory Filter
open scoped Topology
namespace RiemannResearch.RH

/-- Standard countability, using a countable exhaustion by finite windows. -/
theorem zeta_strip_zeros_countable :
    {ρ : ℂ | Zeta23.IsNontrivialZero ρ}.Countable := by
  let W : ℕ → Set ℂ := fun n =>
    {ρ | Zeta23.IsNontrivialZero ρ} ∩
      {ρ | -(n : ℝ) < ρ.im ∧ ρ.im ≤ (n : ℝ)}
  have hW : ∀ n, (W n).Countable := fun n =>
    (Zeta23.ZetaSeam.finite_window_holds (-(n : ℝ)) (n : ℝ)).countable
  refine (Set.countable_iUnion hW).mono ?_
  intro ρ hρ
  obtain ⟨n, hn⟩ := exists_nat_gt |ρ.im|
  apply Set.mem_iUnion.mpr
  refine ⟨n, hρ, ?_, ?_⟩
  · have h := neg_abs_le ρ.im
    linarith
  · exact (le_abs_self ρ.im).trans hn.le

/-- One actual smooth compact polar test detects every nontrivial zeta zero.
No RH or tail-growth assumption is needed for its existence. -/
theorem exists_smooth_compact_actual_zeta_detector :
    ∃ f : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f ∧
      f ≠ 0 ∧ BilateralLaplace.centeredTransform f 0 = 0 ∧
      BilateralLaplace.centeredTransform f 1 = 0 ∧
      ∀ s : ℂ, Zeta23.IsNontrivialZero s →
        BilateralLaplace.centeredTransform f s ≠ 0 := by
  apply exists_smooth_compact_pole_annihilating_countable_detector
    zeta_strip_zeros_countable
  intro ρ hρ
  refine ⟨?_, hρ.not_trivial.2⟩
  intro he
  have hp := hρ.2.1
  simp [he] at hp

end RiemannResearch.RH
