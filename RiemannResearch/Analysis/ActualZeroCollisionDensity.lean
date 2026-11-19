/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroCollisionMultiplicity
import RiemannResearch.Analysis.ActualZeroCollisionCertificate
import RiemannResearch.Analysis.OrdinateCollisionCertificate
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.ActualZeroOrdinate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Equal ordinates and the density of simple critical zeros

Goldston, Lee, Schettler and Suriajaya, *Pair Correlation Conjecture for
the zeros of the Riemann zeta-function I*, §1, ES1 and its consequence,
https://doi.org/10.1112/mtk.70127. The counts below use all analytic
multiplicity copies in the positive cutoff. A zero off the critical line
has a reflected companion at the same ordinate. A multiple zero has a
second copy there. Either case charges one unit to the collision excess.
-/

noncomputable section
open Filter Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroCollisionCertificate
open ActualZeroOrdinate OrdinateCollisionCertificate

/-- Copies whose zero is both on the critical line and simple. -/
def simpleCriticalCopies (T : ℝ) : Finset (Copies T) := by
  classical
  exact Finset.univ.filter (fun c => c.1.1.re = 1 / 2 ∧ zeroMult c.1.1 = 1)

def simpleCriticalCount (T : ℝ) : ℕ := (simpleCriticalCopies T).card

/-- All critical-line copies, including their analytic multiplicities. -/
def criticalLineCount (T : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun c : Copies T => c.1.1.re = 1 / 2)).card

theorem simpleCriticalCount_le_criticalLineCount (T : ℝ) :
    simpleCriticalCount T ≤ criticalLineCount T := by
  classical
  apply Finset.card_le_card
  intro c hc
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2.1⟩

theorem criticalLineCount_le_count (T : ℝ) : criticalLineCount T ≤ Ncount 0 T := by
  classical
  rw [← card_copies, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- An exceptional copy has a distinct equal-ordinate copy in the same cutoff. -/
theorem exceptional_has_companion (T : ℝ) (c : Copies T)
    (hc : c ∉ simpleCriticalCopies T) :
    ∃ d : Copies T, c ≠ d ∧ copyOrdinate T c = copyOrdinate T d := by
  classical
  by_cases hline : c.1.1.re = 1 / 2
  · have hm : zeroMult c.1.1 ≠ 1 := fun hm =>
      hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hline, hm⟩)
    have hpos := multiplicity_pos c.1.2
    have htwo : 1 < zeroMult c.1.1 := by omega
    by_cases hzero : c.2.val = 0
    · let d : Copies T := ⟨c.1, ⟨1, htwo⟩⟩
      refine ⟨d, ?_, rfl⟩
      intro he
      have hv := congrArg (fun x : Copies T => x.2.val) he
      change c.2.val = 1 at hv
      omega
    · let d : Copies T := ⟨c.1, ⟨0, hpos⟩⟩
      exact ⟨d, fun he => hzero (congrArg (fun x : Copies T => x.2.val) he), rfl⟩
  · exact offCopies_has_companion T c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hline⟩)

/-- Finite loss of simple critical zeros is bounded by the excess of ordered
equal-ordinate pairs over occurrence diagonals. -/
theorem twice_count_le_simpleCriticalCount_add_collision (T : ℝ) :
    2 * Ncount 0 T ≤ simpleCriticalCount T + actualCollision T := by
  classical
  let bad := (Finset.univ : Finset (Copies T)) \ simpleCriticalCopies T
  have hp : bad.card + simpleCriticalCount T = Ncount 0 T := by
    rw [← card_copies, ← Finset.card_univ]
    exact Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
  have hb := selected_count_le_occurrenceExcess (copyOrdinate T) bad
    (fun c hc => exceptional_has_companion T c (Finset.mem_sdiff.mp hc).2)
  have hd := occurrenceCollision_eq_card_add_excess (copyOrdinate T)
  rw [card_copies] at hd
  change 2 * Ncount 0 T ≤ simpleCriticalCount T + occurrenceCollision (copyOrdinate T)
  omega

/-- The ES1 coincident-ordinate asymptotic implies density one both jointly
and for all critical-line zeros. The final ratios use the actual count. -/
theorem density_one_of_collision_limit
    (h : Tendsto (fun T : ℝ => (actualCollision T : ℝ) /
      (T * Real.log T / (2 * Real.pi))) atTop (𝓝 1)) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  let D := fun T : ℝ => T * Real.log T / (2 * Real.pi)
  have hN := tendsto_count_div_mainTerm
  have hd : ∀ᶠ T : ℝ in atTop, 0 < D T := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hl : Tendsto (fun T : ℝ => 2 * ((Ncount 0 T : ℝ) / D T) -
      (actualCollision T : ℝ) / D T) atTop (𝓝 1) := by
    simpa only [mul_one, show (2 : ℝ) - 1 = 1 by norm_num] using (hN.const_mul 2).sub h
  have hs : Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / D T) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hN
    · filter_upwards [hd] with T hT
      have hb : 2 * (Ncount 0 T : ℝ) ≤ (simpleCriticalCount T : ℝ) + actualCollision T := by
        exact_mod_cast twice_count_le_simpleCriticalCount_add_collision T
      rw [← mul_div_assoc, ← sub_div]
      exact div_le_div_of_nonneg_right (by linarith) hT.le
    · filter_upwards [hd] with T hT
      apply div_le_div_of_nonneg_right _ hT.le
      exact_mod_cast (simpleCriticalCount_le_criticalLineCount T).trans (criticalLineCount_le_count T)
  have hc : Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / D T) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hs hN
    · filter_upwards [hd] with T hT
      exact div_le_div_of_nonneg_right (by exact_mod_cast simpleCriticalCount_le_criticalLineCount T) hT.le
    · filter_upwards [hd] with T hT
      exact div_le_div_of_nonneg_right (by exact_mod_cast criticalLineCount_le_count T) hT.le
  have ratios (f : ℝ → ℕ) (hf : Tendsto (fun T : ℝ => (f T : ℝ) / D T) atTop (𝓝 1)) :
      Tendsto (fun T : ℝ => (f T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
    have hlim := hf.div hN (by norm_num : (1 : ℝ) ≠ 0)
    rw [div_one] at hlim
    apply hlim.congr'
    filter_upwards [hd] with T hT
    change (f T : ℝ) / D T / ((Ncount 0 T : ℝ) / D T) = _
    field_simp [hT.ne']
  exact ⟨ratios _ hs, ratios _ hc⟩

end RiemannResearch.Analysis.ActualZeroCollisionCertificate
