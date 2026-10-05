/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroDensityWindow
import RiemannResearch.Analysis.ActualMobiusZeroDetector

/-!
# Exact weighted density windows and detector multiplicities

This is the finite counting bridge used in Chourasiya--Simonic's
Littlewood route, arXiv:2507.15184v2, Section 4 and equation (32):
https://arxiv.org/html/2507.15184v2.
The full threshold excess equals the closed threshold count times its
gap, plus the excess above that threshold and the strict intervening band.
The detector adds explicit mollifier multiplicity, and an arbitrary finite
superset adds an exact nonnegative complement sum. No analytic integral
estimate or equality of the zeta and detector zero sets is assumed.
-/

noncomputable section
open scoped BigOperators


namespace RiemannResearch.Analysis.ActualZeroOrdinate
open Zeta23 InghamMollifier
def rightLogExcessWindow (H T α : ℝ) : ℝ :=
  realSum T (fun ρ => if H < ρ.im then max 0 (ρ.re-α) else 0)
def rightLogExcessAboveWindow (H T σ : ℝ) : ℝ :=
  realSum T (fun ρ => if H < ρ.im ∧ σ ≤ ρ.re then ρ.re-σ else 0)
def rightLogExcessBandWindow (H T α σ : ℝ) : ℝ :=
  realSum T (fun ρ => if H < ρ.im ∧ α < ρ.re ∧ ρ.re < σ then ρ.re-α else 0)
theorem rightLogExcessWindow_nonneg (H T α : ℝ) :
    0 ≤ rightLogExcessWindow H T α := by
  apply realSum_nonneg
  intro ρ hρ
  split_ifs <;> positivity
theorem rightLogExcessAboveWindow_nonneg (H T σ : ℝ) :
    0 ≤ rightLogExcessAboveWindow H T σ := by
  apply realSum_nonneg
  intro ρ hρ
  split_ifs with h
  · exact sub_nonneg.mpr h.2
  · rfl
theorem rightLogExcessBandWindow_nonneg (H T α σ : ℝ) :
    0 ≤ rightLogExcessBandWindow H T α σ := by
  apply realSum_nonneg
  intro ρ hρ
  split_ifs with h
  · exact (sub_pos.mpr h.2.1).le
  · rfl
theorem rightLogExcessWindow_exact (H T α σ : ℝ) (hασ : α ≤ σ) :
    rightLogExcessWindow H T α =
      (σ-α)*rightInclusiveWindow H T σ+
        rightLogExcessAboveWindow H T σ+rightLogExcessBandWindow H T α σ := by
  have hp (ρ : ℂ) :
      (if H < ρ.im then max 0 (ρ.re-α) else 0) =
      (if H < ρ.im ∧ σ ≤ ρ.re then (1 : ℝ) else 0)*(σ-α)+
        (if H < ρ.im ∧ σ ≤ ρ.re then ρ.re-σ else 0)+
        (if H < ρ.im ∧ α < ρ.re ∧ ρ.re < σ then ρ.re-α else 0) := by
    by_cases hh : H < ρ.im
    · by_cases hs : σ ≤ ρ.re
      · have hb : 0 ≤ ρ.re-α := by linarith
        have hn : ¬ρ.re < σ := not_lt_of_ge hs
        simp [hh, hs, hn, max_eq_right hb]
      · have hs' : ρ.re < σ := lt_of_not_ge hs
        by_cases ha : α < ρ.re
        · have hb : 0 ≤ ρ.re-α := by linarith
          simp [hh, hs, hs', ha, max_eq_right hb]
        · have hb : ρ.re-α ≤ 0 := by linarith
          simp [hh, hs, ha, max_eq_left hb]
    · simp [hh]
  have he : rightLogExcessWindow H T α = realSum T (fun ρ =>
      (if H < ρ.im ∧ σ ≤ ρ.re then (1 : ℝ) else 0)*(σ-α)+
        (if H < ρ.im ∧ σ ≤ ρ.re then ρ.re-σ else 0)+
        (if H < ρ.im ∧ α < ρ.re ∧ ρ.re < σ then ρ.re-α else 0)) := by
    unfold rightLogExcessWindow
    congr 1
    funext ρ
    exact hp ρ
  rw [he, realSum_add, realSum_add, realSum_mul_const]
  change rightInclusiveWindow H T σ*(σ-α)+
    rightLogExcessAboveWindow H T σ+rightLogExcessBandWindow H T α σ = _
  ring
theorem rightInclusiveWindow_mul_gap_le (H T α σ : ℝ) (hασ : α ≤ σ) :
    (σ-α)*rightInclusiveWindow H T σ ≤ rightLogExcessWindow H T α := by
  rw [rightLogExcessWindow_exact H T α σ hασ]
  linarith [rightLogExcessAboveWindow_nonneg H T σ,
    rightLogExcessBandWindow_nonneg H T α σ]
theorem rightInclusiveWindow_le_of_logExcess {H T α σ F : ℝ}
    (hασ : α < σ) (hW : rightLogExcessWindow H T α ≤ (σ-α)*F) :
    rightInclusiveWindow H T σ ≤ F := by
  have hg : 0 < σ-α := sub_pos.mpr hασ
  have hb := (rightInclusiveWindow_mul_gap_le H T α σ hασ.le).trans hW
  nlinarith
def detectorLogExcessOnZetaWindow (X : ℕ) (H T α : ℝ) : ℝ :=
  ∑ ρ ∈ cutoff T, ((analyticOrderAt (zetaDetector X) ρ).toNat : ℝ)*
    (if H < ρ.im then max 0 (ρ.re-α) else 0)
def mollifierExtraLogExcessWindow (X : ℕ) (H T α : ℝ) : ℝ :=
  ∑ ρ ∈ cutoff T, ((analyticOrderAt (mollifier X) ρ).toNat : ℝ)*
    (if H < ρ.im then max 0 (ρ.re-α) else 0)
theorem mollifierExtraLogExcessWindow_nonneg (X : ℕ) (H T α : ℝ) :
    0 ≤ mollifierExtraLogExcessWindow X H T α := by
  apply Finset.sum_nonneg
  intro ρ hρ
  split_ifs <;> positivity
theorem detectorLogExcessOnZetaWindow_exact (X : ℕ) (hX : 1 ≤ X) (H T α : ℝ) :
    detectorLogExcessOnZetaWindow X H T α =
      rightLogExcessWindow H T α+mollifierExtraLogExcessWindow X H T α := by
  unfold detectorLogExcessOnZetaWindow rightLogExcessWindow realSum mollifierExtraLogExcessWindow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [zetaDetector_orderNat X hX hρ]
  push_cast
  ring
theorem rightLogExcessWindow_le_detector (X : ℕ) (hX : 1 ≤ X) (H T α : ℝ) :
    rightLogExcessWindow H T α ≤ detectorLogExcessOnZetaWindow X H T α := by
  rw [detectorLogExcessOnZetaWindow_exact X hX]
  linarith [mollifierExtraLogExcessWindow_nonneg X H T α]

/-- The actual zeta points with strictly positive log-excess weight. -/
def activeLogExcessWindow (H T α : ℝ) : Finset ℂ :=
  (cutoff T).filter (fun ρ => H < ρ.im ∧ α < ρ.re)

/-- Weighted analytic detector orders on an arbitrary finite set. -/
def detectorLogExcessFinite (X : ℕ) (D : Finset ℂ) (α : ℝ) : ℝ :=
  ∑ ρ ∈ D, ((analyticOrderAt (zetaDetector X) ρ).toNat : ℝ)*max 0 (ρ.re-α)

theorem detectorLogExcessOnZetaWindow_eq_active (X : ℕ) (H T α : ℝ) :
    detectorLogExcessOnZetaWindow X H T α =
      detectorLogExcessFinite X (activeLogExcessWindow H T α) α := by
  classical
  unfold detectorLogExcessOnZetaWindow detectorLogExcessFinite activeLogExcessWindow
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ρ hρ
  by_cases hh : H < ρ.im
  · by_cases ha : α < ρ.re
    · simp [hh, ha]
    · have he : max 0 (ρ.re-α)=0 := max_eq_left (by linarith)
      simp [hh, ha, he]
  · simp [hh]

/-- Every active actual zeta point lies in the source rectangle when its right
line is at least one. The top height stays closed, and the lower height strict. -/
theorem activeLogExcessWindow_mem_rectangle (X : ℕ) {H T α β : ℝ}
    (hβ : 1 ≤ β) {ρ : ℂ} (hρ : ρ ∈ activeLogExcessWindow H T α) :
    zetaDetector X ρ=0 ∧ α < ρ.re ∧ ρ.re < β ∧ H < ρ.im ∧ ρ.im ≤ T := by
  have hh := Finset.mem_filter.mp hρ
  have hz := mem_cutoff.mp hh.1
  have hdet : zetaDetector X ρ=0 := by
    simp [zetaDetector, Complex.quadraticZeroDetector, hz.1.1]
  exact ⟨hdet, hh.2.2, lt_of_lt_of_le hz.1.2.2 hβ, hh.2.1, hz.2.2⟩

/-- Exact contribution of all detector points outside the active zeta set. -/
theorem detectorLogExcessFinite_exact (X : ℕ) (D : Finset ℂ) (H T α : ℝ)
    (hD : activeLogExcessWindow H T α ⊆ D) :
    detectorLogExcessFinite X D α =
      detectorLogExcessOnZetaWindow X H T α+
        detectorLogExcessFinite X (D \ activeLogExcessWindow H T α) α := by
  classical
  rw [detectorLogExcessOnZetaWindow_eq_active]
  unfold detectorLogExcessFinite
  exact (Finset.sum_sdiff hD).symm.trans (add_comm _ _)

theorem detectorLogExcessOnZetaWindow_le_finite (X : ℕ) (D : Finset ℂ) (H T α : ℝ)
    (hD : activeLogExcessWindow H T α ⊆ D) :
    detectorLogExcessOnZetaWindow X H T α ≤ detectorLogExcessFinite X D α := by
  rw [detectorLogExcessFinite_exact X D H T α hD]
  have he : 0 ≤ detectorLogExcessFinite X (D \ activeLogExcessWindow H T α) α := by
    apply Finset.sum_nonneg
    intro ρ hρ
    positivity
  linarith [he]

end RiemannResearch.Analysis.ActualZeroOrdinate
