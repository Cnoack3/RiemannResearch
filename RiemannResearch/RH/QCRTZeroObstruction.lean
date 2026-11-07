import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import RiemannResearch.RH.QCRTFiniteCollocation
import RiemannResearch.RH.QMellinTransfer
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact Mellin obstruction to canonical CRT leakage

Source: CRT_Collocation_and_Zero_Growth_2026-11-06, Section 7, and its
orthogonal-leakage refinement. Bagchi (2006), Theorem 2 and the Mellin
calculation in the proof of Theorem 5, support the zero-annihilator strategy.
https://repository.ias.ac.in/968/1/307.pdf

The detector is the existing actual physical Mellin functional. Its norm
after removal of the finite gcd-cell projection is an explicitly defined
operator norm, not an assumed detector provider. Bounding that norm by the
zero-sensitive Euler divisor tail is a separate analytic obligation.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QCRTZeroObstruction
open ZetaTwoHilbert QDivisibilityDensity QCRTFiniteCollocation QMellinTransfer

def tailMellin (L : ℕ) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    QHilbert →L[ℝ] ℂ :=
  (qMellinContinuous s hs).comp
    (ContinuousLinearMap.id ℝ QHilbert - conditionalProjection L)

theorem qMellin_trial_zero (L : ℕ) (f : QHilbert) (hf : f ∈ trialSpace L)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    qMellin f s = 0 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨d, hd, rfl⟩
    exact qMellin_residue_zero d (Nat.pos_of_mem_divisors hd) s (by linarith) hs1 hz
  | zero => exact (qMellinContinuous s hs).map_zero
  | add x y hx hy ihx ihy => rw [qMellin_add x y s hs, ihx, ihy, add_zero]
  | smul c x hx ih => rw [qMellin_smul c x s hs, ih, smul_zero]

/-- Exact signed zero identity with the entire multiples endpoint retained. -/
theorem canonical_mellin_balance (L : ℕ) (hL : 2 ≤ L)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    1 / s = qMellin (qDivisor L) s -
      qMellin ((canonical L hL : QHilbert) - target L) s := by
  have hf := qMellin_trial_zero L _ (canonical L hL).property s hs hs1 hz
  have hone := qMellin_one s hs
  change 1 / s = qMellinContinuous s hs (qDivisor L) -
    qMellinContinuous s hs ((canonical L hL : QHilbert) - target L)
  rw [target, map_sub, map_sub]
  change 1 / s = qMellin (qDivisor L) s -
    (qMellin (canonical L hL) s - (qMellin qOne s - qMellin (qDivisor L) s))
  rw [hf, hone]
  ring

theorem canonical_leakage_projection_zero (L : ℕ) (hL : 2 ≤ L) :
    conditionalProjection L ((canonical L hL : QHilbert) - target L) = 0 := by
  rw [map_sub, canonical_conditional L hL]
  change target L - (cellSpace L).starProjection (target L) = 0
  rw [Submodule.starProjection_eq_self_iff.mpr (target_mem_cell L (by omega)), sub_self]

/-- The exact projected Mellin detector acts only on the complete leakage. -/
theorem canonical_mellin_obstruction (L : ℕ) (hL : 2 ≤ L)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    1 / ‖s‖ ≤ ‖qMellin (qDivisor L) s‖ +
      ‖tailMellin L s hs‖ * Real.sqrt (leakage L hL) := by
  have htail : tailMellin L s hs ((canonical L hL : QHilbert) - target L) =
      qMellin ((canonical L hL : QHilbert) - target L) s := by
    change qMellinContinuous s hs
      (((canonical L hL : QHilbert) - target L) -
        conditionalProjection L ((canonical L hL : QHilbert) - target L)) = _
    rw [canonical_leakage_projection_zero L hL, sub_zero]
    rfl
  have hsqrt : Real.sqrt (leakage L hL) =
      ‖(canonical L hL : QHilbert) - target L‖ :=
    Real.sqrt_sq (norm_nonneg _)
  have hop : ‖qMellin ((canonical L hL : QHilbert) - target L) s‖ ≤
      ‖tailMellin L s hs‖ * ‖(canonical L hL : QHilbert) - target L‖ := by
    rw [← htail]
    exact (tailMellin L s hs).le_opNorm
      ((canonical L hL : QHilbert) - target L)
  calc
    1 / ‖s‖ = ‖(1 : ℂ) / s‖ := by rw [norm_div, norm_one]
    _ = ‖qMellin (qDivisor L) s -
      qMellin ((canonical L hL : QHilbert) - target L) s‖ :=
        congrArg norm (canonical_mellin_balance L hL s hs hs1 hz)
    _ ≤ ‖qMellin (qDivisor L) s‖ +
        ‖qMellin ((canonical L hL : QHilbert) - target L) s‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [hsqrt]
      exact add_le_add le_rfl hop

/-- Conditional research reduction using the actual projected Mellin budget.
The vanishing budget is the explicit open hypothesis. -/
theorem riemannHypothesis_of_vanishing_mellin_budget
    (L : ℕ → ℕ) (hL : ∀ j, 2 ≤ L j)
    (hbudget : ∀ (s : ℂ) (hs : (1 / 2 : ℝ) < s.re), s.re < 1 →
      Tendsto (fun j => ‖qMellin (qDivisor (L j)) s‖ +
        ‖tailMellin (L j) s hs‖ * Real.sqrt (leakage (L j) (hL j)))
        atTop (𝓝 0)) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hslt
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hpos : 0 < 1 / ‖s‖ := one_div_pos.mpr (norm_pos_iff.mpr hs0)
  have he := (hbudget s hs hslt).eventually (gt_mem_nhds hpos)
  obtain ⟨j, hj⟩ := he.exists
  exact (not_lt_of_ge (canonical_mellin_obstruction (L j) (hL j) s hs hs1 hz)) hj

end RiemannResearch.RH.QCRTZeroObstruction
