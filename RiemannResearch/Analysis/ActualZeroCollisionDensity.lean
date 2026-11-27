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

open scoped BigOperators

/-- The number of heights occupied by exactly one zero occurrence, counting
both analytic multiplicity and horizontal companions in each fibre. -/
def singletonOrdinateCount (T : ℝ) : ℕ := by
  classical
  exact ((actualOrdinateSupport T).filter (fun τ => actualOrdinateMultiplicity T τ = 1)).card

private theorem simpleCriticalCopy_eq_of_critical_at_same_height {T : ℝ} {c d : Copies T}
    (hc : c ∈ simpleCriticalCopies T) (hd : d.1.1.re = 1 / 2)
    (ht : copyOrdinate T c = copyOrdinate T d) : c = d := by
  classical
  have hline : c.1.1.re = 1 / 2 := (Finset.mem_filter.mp hc).2.1
  have hm : zeroMult c.1.1 = 1 := (Finset.mem_filter.mp hc).2.2
  rcases c with ⟨c, i⟩
  rcases d with ⟨d, j⟩
  have hpoint : c = d := Subtype.ext (Complex.ext (hline.trans hd.symm) ht)
  subst d
  have hi := i.isLt
  have hj := j.isLt
  change zeroMult c.1 = 1 at hm
  have hij : i = j := Fin.ext (by omega)
  cases hij
  rfl

/-- At a shared height, a simple critical zero has two further occurrences
from an off-line reflected pair. -/
theorem three_le_multiplicity_of_shared_simpleCritical {T : ℝ} {c d : Copies T}
    (hc : c ∈ simpleCriticalCopies T) (hcd : c ≠ d)
    (ht : copyOrdinate T c = copyOrdinate T d) :
    3 ≤ actualOrdinateMultiplicity T (copyOrdinate T c) := by
  classical
  have hline : c.1.1.re = 1 / 2 := (Finset.mem_filter.mp hc).2.1
  have hoff : d.1.1.re ≠ 1 / 2 := fun hd =>
    hcd (simpleCriticalCopy_eq_of_critical_at_same_height hc hd ht)
  let e : Copies T :=
    ⟨⟨reflect d.1.1, reflect_mem d.1.2⟩, ⟨0, multiplicity_pos (reflect_mem d.1.2)⟩⟩
  have hce : c ≠ e := by
    intro h
    have hr := congrArg (fun x : Copies T => x.1.1.re) h
    change c.1.1.re = (reflect d.1.1).re at hr
    rw [reflect_re] at hr
    exact hoff (by linarith)
  have hde : d ≠ e := by
    intro h
    have hr := congrArg (fun x : Copies T => x.1.1.re) h
    change d.1.1.re = (reflect d.1.1).re at hr
    rw [reflect_re] at hr
    exact hoff (by linarith)
  let F := Finset.univ.filter (fun x : Copies T => copyOrdinate T x = copyOrdinate T c)
  have he : copyOrdinate T e = copyOrdinate T c := (reflect_im d.1.1).trans ht.symm
  have hsub : ({c, d, e} : Finset (Copies T)) ⊆ F := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
  have hthree : ({c, d, e} : Finset (Copies T)).card = 3 := by simp [hcd, hce, hde]
  change 3 ≤ F.card
  simpa only [hthree] using Finset.card_le_card hsub

/-- Three times the simple-critical count is at most the full occurrence
count plus twice the singleton-ordinate count. -/
theorem three_mul_simpleCriticalCount_le (T : ℝ) :
    3 * simpleCriticalCount T ≤ Ncount 0 T + 2 * singletonOrdinateCount T := by
  classical
  let A := (simpleCriticalCopies T).image (copyOrdinate T)
  have hA : A ⊆ actualOrdinateSupport T := by
    intro τ hτ
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hτ
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
  have hcard : A.card = simpleCriticalCount T := by
    apply Finset.card_image_iff.mpr
    intro c hc d hd ht
    exact simpleCriticalCopy_eq_of_critical_at_same_height hc (Finset.mem_filter.mp hd).2.1 ht
  have hrow (τ : ℝ) (hτ : τ ∈ A) :
      3 ≤ actualOrdinateMultiplicity T τ + (if actualOrdinateMultiplicity T τ = 1 then 2 else 0) := by
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hτ
    by_cases hm : actualOrdinateMultiplicity T (copyOrdinate T c) = 1
    · simp [hm]
    · have hd : ∃ d : Copies T, c ≠ d ∧ copyOrdinate T c = copyOrdinate T d := by
        by_contra h
        apply hm
        change (Finset.univ.filter (fun d : Copies T => copyOrdinate T d = copyOrdinate T c)).card = 1
        have hf : Finset.univ.filter (fun d : Copies T => copyOrdinate T d = copyOrdinate T c) = {c} := by
          ext d
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hdc
            by_contra hne
            exact h ⟨d, Ne.symm hne, hdc.symm⟩
          · rintro rfl
            rfl
        rw [hf, Finset.card_singleton]
      obtain ⟨d, hcd, ht⟩ := hd
      simpa [hm] using three_le_multiplicity_of_shared_simpleCritical hc hcd ht
  calc
    3 * simpleCriticalCount T = ∑ _τ ∈ A, (3 : ℕ) := by simp [hcard, Nat.mul_comm]
    _ ≤ ∑ τ ∈ A, (actualOrdinateMultiplicity T τ + (if actualOrdinateMultiplicity T τ = 1 then 2 else 0)) :=
      Finset.sum_le_sum hrow
    _ ≤ ∑ τ ∈ actualOrdinateSupport T, (actualOrdinateMultiplicity T τ +
        (if actualOrdinateMultiplicity T τ = 1 then 2 else 0)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ => Nat.zero_le _)
    _ = Ncount 0 T + 2 * singletonOrdinateCount T := by
      rw [Finset.sum_add_distrib, ← actualCount_eq_sum_ordinateMultiplicity]
      congr 1
      rw [← Finset.sum_filter]
      simp [singletonOrdinateCount, Nat.mul_comm]

/-- An eventual simple-critical proportion transfers to the proportion of
singleton ordinates, in both cases normalized by the full occurrence count. -/
theorem eventually_singletonOrdinate_proportion_lower {a : ℝ}
    (ha : ∀ᶠ T : ℝ in atTop, a ≤ (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) :
    ∀ᶠ T : ℝ in atTop, (3 * a - 1) / 2 ≤
      (singletonOrdinateCount T : ℝ) / (Ncount 0 T : ℝ) := by
  filter_upwards [ha, eventually_count_pos] with T h hN
  have hN' : 0 < (Ncount 0 T : ℝ) := by exact_mod_cast hN
  have hs := (le_div_iff₀ hN').1 h
  have hf : 3 * (simpleCriticalCount T : ℝ) ≤ (Ncount 0 T : ℝ) + 2 * (singletonOrdinateCount T : ℝ) := by
    exact_mod_cast three_mul_simpleCriticalCount_le T
  apply (le_div_iff₀ hN').2
  nlinarith only [hs, hf]

#print axioms three_mul_simpleCriticalCount_le
#print axioms eventually_singletonOrdinate_proportion_lower

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
