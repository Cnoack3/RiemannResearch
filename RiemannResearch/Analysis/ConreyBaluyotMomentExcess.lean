/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroDensityLogExcess
import RiemannResearch.Analysis.ConreyBaluyotDyadicLittlewood
import RiemannResearch.Analysis.ConreyBaluyotMomentContinuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Actual weighted dyadic zero excess from a prescribed-line moment

The zero-free left side is chosen below the prescribed line. Continuity and
arbitrarily thin outward height strips let the extra moment cost tend to zero.
The Littlewood identity retains the signed horizontal and right boundary terms
and the full nonnegative mollifier-zero contribution before taking the bound.

Source for the proof strategy: S. A. C. Baluyot, *On the Zeros of
Riemann's Zeta-function* (2017), Chapter 3,
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .
This implements the linearized moment-to-excess inequality in Lemma 3.2.1.
-/

noncomputable section
open Complex Set
open scoped BigOperators

namespace RiemannResearch.Analysis.ConreyBaluyot

open ActualZeroOrdinate

private theorem rightLogExcessWindow_le_rectangle {T σ l b t₁ t₂ : ℝ}
    {Z : Finset ℂ} {F : ℂ → ℂ} (hlσ : l ≤ σ) (hlb : l ≤ b)
    (hZ : ∀ s, s ∈ Z ↔ s ∈ Rectangle ((l : ℂ) + (t₁ : ℂ) * I)
      ((b : ℂ) + (t₂ : ℂ) * I) ∧ F s = 0)
    (hcover : ∀ s : ℂ, σ ≤ s.re → T ≤ s.im → s.im ≤ 2 * T → riemannZeta s = 0 → s ∈ Z) :
    rightLogExcessWindow T (2 * T) σ ≤
      ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - l) := by
  classical
  have hsub : activeLogExcessWindow T (2 * T) σ ⊆ Z := by
    intro ρ hρ
    obtain ⟨hcut, hH, hβ⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hz, _, hT⟩ := mem_cutoff.mp hcut
    exact hcover ρ hβ.le hH.le hT hz.1
  have hsum : rightLogExcessWindow T (2 * T) σ =
      ∑ ρ ∈ activeLogExcessWindow T (2 * T) σ,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - σ) := by
    unfold rightLogExcessWindow realSum activeLogExcessWindow
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    change (analyticOrderNatAt riemannZeta ρ : ℝ) *
      (if T < ρ.im then max 0 (ρ.re - σ) else 0) = _
    by_cases ht : T < ρ.im
    · by_cases hs : σ < ρ.re
      · simp [ht, hs, max_eq_right (sub_nonneg.mpr hs.le)]
      · simp [ht, hs, max_eq_left (sub_nonpos.mpr (le_of_not_gt hs))]
    · simp [ht]
  rw [hsum]
  calc
    _ ≤ ∑ ρ ∈ activeLogExcessWindow T (2 * T) σ,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - l) := by
      apply Finset.sum_le_sum
      intro ρ _
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro ρ hρ _
      have hr := ((hZ ρ).mp hρ).1.1
      have hre : (((l : ℂ) + (t₁ : ℂ) * I)).re ≤
          (((b : ℂ) + (t₂ : ℂ) * I)).re := by simpa using hlb
      rw [uIcc_of_le hre] at hr
      have hρl : l ≤ ρ.re := by simpa using hr.1
      exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hρl)

/-- The inclusive finite-height weighted zero sum follows from the second
moment on the source line. The selectable left edge stays below that line. -/
theorem exists_uniform_dyadic_logExcess_of_prescribed_line_moment
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) :
    ∃ η B H : ℝ, 0 < η ∧ η < 1 / 4 ∧ 0 ≤ B ∧ 2 ≤ H ∧
      ∀ T σ : ℝ, H ≤ T → 1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
        ∀ E : ℝ,
          mollifiedSecondMoment σ (T ^ θ) ε σ T (2 * T) ≤ T + E →
          rightLogExcessWindow T (2 * T) σ ≤ E / (4 * Real.pi) + B * Real.log T := by
  obtain ⟨η₀, b, D, C, H₀, hη₀, hη₀', hb, hD, hC, hH₀, hrect⟩ :=
    exists_uniform_dyadic_littlewood_normalized_boundary_bound hε hθ
  obtain ⟨η₁, Y, hη₁, _, hY, hend⟩ := exists_uniform_mollifiedSecondMoment_endpoint_transfer hε
  let B := (C / Real.log 2 + 2 * D) / (2 * Real.pi)
  refine ⟨min η₀ η₁, B, max H₀ (Y ^ θ⁻¹),
    lt_min hη₀ hη₁, (min_le_left _ _).trans_lt hη₀', by dsimp [B]; positivity,
    (show 2 ≤ H₀ by linarith).trans (le_max_left _ _), ?_⟩
  intro T σ hT hσ hση E hm
  have hT₀ : H₀ ≤ T := (le_max_left _ _).trans hT
  have hT2 : 2 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hση₀ : σ ≤ 1 / 2 + η₀ := by linarith [min_le_left η₀ η₁]
  have hση₁ : σ ≤ 1 / 2 + η₁ := by linarith [min_le_right η₀ η₁]
  have hσhalf : 1 / 2 < σ := hσ.trans_lt' (by
    have hlog : 0 < Real.log (T ^ θ) := Real.log_pos (Real.one_lt_rpow (by linarith) hθ)
    linarith [one_div_pos.mpr hlog])
  have hσb : σ < b := by linarith
  have hYpow : Y ≤ T ^ θ := by
    calc
      Y = (Y ^ θ⁻¹) ^ θ := (Real.rpow_inv_rpow (by linarith : 0 ≤ Y) hθ.ne').symm
      _ ≤ T ^ θ := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _)
        ((le_max_right _ _).trans hT) hθ.le
  apply le_of_forall_pos_le_add
  intro e he
  let κ := 4 * Real.pi * e
  have hk : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨δ, hδ, hδ', htransfer⟩ := hend T (T ^ θ) (κ / 2) hT2 hYpow (by positivity)
  obtain ⟨r, hr, hnear⟩ :=
    exists_mollifiedSecondMoment_line_neighborhood σ (T ^ θ) ε σ hTpos
      (by linarith : T ≤ 2 * T) (show 0 < κ / 2 by positivity)
  let d := min (r / 2) ((σ - 1 / 2) / 2)
  have hd : 0 < d := lt_min (by positivity) (by linarith)
  have hdr : d < r := (min_le_left _ _).trans_lt (by linarith)
  have hdσ : 1 / 2 ≤ σ - d := by linarith [min_le_right (r / 2) ((σ - 1 / 2) / 2)]
  obtain ⟨t₁, t₂, l, Z, Bot, Top, h1lo, h1hi, h2lo, h2hi, hhalf, hla, _, hlσ,
    h1pos, h12, hborder, hZ, _, _, _, _, _, _, _, _, hdiff, hid, hM, _, hR,
    hcover, _, _⟩ :=
    hrect T hT₀ σ hσ hση₀ δ hδ hδ' (σ - d) σ σ hdσ (by linarith) le_rfl hσb
  have hmnear : mollifiedSecondMoment σ (T ^ θ) ε l T (2 * T) ≤ T + (E + κ / 2) := by
    have hn := hnear l (abs_lt.mpr ⟨by linarith, by linarith⟩)
    linarith
  have hmout : mollifiedSecondMoment σ (T ^ θ) ε l t₁ t₂ ≤ t₂ - t₁ + (E + κ) := by
    have hh := htransfer σ l t₁ t₂ (E + κ / 2) hσ hση₁ (by linarith)
      h1lo.le h1hi.le h2lo.le h2hi.le hmnear
    linarith
  have hleft : ∀ t ∈ Icc t₁ t₂,
      mollifiedZeta σ (T ^ θ) ε ((l : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t ht
    apply hborder
    apply Or.inl
    apply Or.inl
    apply Or.inr
    constructor
    · simp
    · simpa [Set.uIcc_of_le h12.le] using ht
  have hleftLog := integral_log_mollifiedZeta_le_of_moment σ (T ^ θ) ε l
    h1pos h12.le hleft hmout
  have hw := rightLogExcessWindow_le_rectangle hlσ.le
    (show l ≤ b by linarith) hZ hcover
  have hv : -(∫ t in t₁..t₂, Real.log ‖mollifiedZeta σ (T ^ θ) ε
      ((b : ℂ) + (t : ℂ) * I)‖) ≤ C := (neg_le_abs _).trans hR
  have hh := (le_abs_self ((∫ x in l..b, (Top x).im) -
      (∫ x in l..b, (Bot x).im))).trans (by simpa only [Real.norm_eq_abs] using hdiff)
  unfold logRectangleBoundary at hid
  have hbound : (2 * Real.pi) * rightLogExcessWindow T (2 * T) σ ≤
      (E + κ) / 2 + C + 2 * D * Real.log T := by
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_left (hw.trans (le_add_of_nonneg_right hM)) (by positivity)
      _ = _ := hid.symm
      _ ≤ _ := by linarith
  have hlog : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT2
  have hCbound : C ≤ (C / Real.log 2) * Real.log T := by
    calc
      C = (C / Real.log 2) * Real.log 2 :=
        (div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  have hBeq : (2 * Real.pi) * B = C / Real.log 2 + 2 * D := by
    dsimp [B]
    rw [mul_comm, div_mul_cancel₀ _ (by positivity)]
  apply (le_of_mul_le_mul_left ?_ (show 0 < 2 * Real.pi by positivity))
  rw [mul_add, mul_add, ← mul_assoc, hBeq, add_mul]
  have hEeq : 2 * Real.pi * (E / (4 * Real.pi)) = E / 2 := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hEeq]
  dsimp [κ] at hbound
  linarith

end RiemannResearch.Analysis.ConreyBaluyot
