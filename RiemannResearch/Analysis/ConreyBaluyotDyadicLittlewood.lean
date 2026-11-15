/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotLittlewood
import RiemannResearch.Analysis.ComplexLogLiftUniqueness
import RiemannResearch.Analysis.ConreyBaluyotDyadicRectangle
import Mathlib.Tactic.Linarith

/-!
# Actual dyadic Littlewood rectangles with an exact mollifier remainder

Combine the proved good-height rectangle selection with the exact signed
Littlewood identity. All mollifier parameters stay fixed between the two
horizontal edges. On the positive-real right anchor, covering-map uniqueness
identifies the compatible logarithm lifts with the bounded normalized phases.
Outward good heights cover the closed dyadic window, with no limiting passage.
The exact mollifier remainder survives in the resulting multiplicity bound.
-/

noncomputable section
open Complex Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- On the established parameter strip, dyadic rectangles and compatible
logarithm lifts exist with the exact signed zero identity. No zero-free-border
or supplied-phase hypothesis remains in this existence theorem. -/
theorem exists_uniform_dyadic_littlewood_identity
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) :
    ∃ η b H : ℝ, 0 < η ∧ η < 1 / 4 ∧ 2 ≤ b ∧ b + 2 ≤ H ∧
      ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ α β : ℝ,
            1 / 2 < α → α < β → β < b →
              ∃ (t₁ t₂ l r : ℝ) (Z : Finset ℂ) (B U : ℝ → ℂ),
                |t₁ - T| < δ ∧ |t₂ - 2 * T| < δ ∧
                1 / 2 < l ∧ l < α ∧ β < r ∧ r < b ∧
                0 < t₁ ∧ t₁ < t₂ ∧
                (∀ s ∈ RectangleBorder ((l : ℂ) + (t₁ : ℂ) * I)
                    ((r : ℂ) + (t₂ : ℂ) * I),
                  mollifiedZeta σ (T ^ θ) ε s ≠ 0) ∧
                (∀ s, s ∈ Z ↔ s ∈ Rectangle
                  ((l : ℂ) + (t₁ : ℂ) * I) ((r : ℂ) + (t₂ : ℂ) * I) ∧
                    mollifiedZeta σ (T ^ θ) ε s = 0) ∧
                Continuous B ∧ Continuous U ∧
                (∀ x ∈ Icc l r, exp (B x) =
                  mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t₁ : ℂ) * I)) ∧
                (∀ x ∈ Icc l r, exp (U x) =
                  mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t₂ : ℂ) * I)) ∧
                logRectangleBoundary (mollifiedZeta σ (T ^ θ) ε)
                  (fun x => (B x).im) (fun x => (U x).im) l r t₁ t₂ =
                  2 * Real.pi * ((∑ ρ ∈ Z,
                    (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - l)) +
                    ∑ ρ ∈ Z,
                      (analyticOrderNatAt (nonstandardMollifier σ (T ^ θ) ε) ρ : ℝ) *
                        (ρ.re - l)) := by
  obtain ⟨η, b, D, H, hη, hη', hb, _, hH, hrect⟩ :=
    exists_uniform_dyadic_mollifiedZeta_zero_free_rectangle hε hθ
  refine ⟨η, b, H, hη, hη', hb, hH, ?_⟩
  intro T hT σ hσ hση δ hδ hδ' α β hα hαβ hβ
  obtain ⟨t₁, t₂, l, r, ht₁, ht₂, hl, hlα, hβr, hr, ht₁pos, htt,
      hborder, _, _⟩ :=
    hrect T hT σ hσ hση δ hδ hδ' α β hα hαβ hβ
  have hlr : l ≤ r := by linarith
  obtain ⟨Z, B, U, hZ, hBc, hUc, hBe, hUe, hid, _, _, _⟩ :=
    exists_mollifiedZeta_littlewood_identity_with_remainder
      σ (T ^ θ) ε hlr htt.le ht₁pos hborder
  exact ⟨t₁, t₂, l, r, Z, B, U, ht₁, ht₂, hl, hlα, hβr, hr, ht₁pos, htt,
    hborder, hZ, hBc, hUc, hBe, hUe, hid⟩

/-- A principal-normalized logarithm lift inherits the proved horizontal
integral bound. Equality is on the whole interval, not just modulo 2*pi. -/
theorem GoodHorizontalPhase.integral_logLift_bound
    {F : ℂ → ℂ} {a b D T t : ℝ} (h : GoodHorizontalPhase F b D T t)
    (ha : 1 / 2 ≤ a) (hab : a ≤ b) {L : ℝ → ℂ}
    (hLc : Continuous L)
    (he : ∀ x ∈ Icc a b, exp (L x) = F ((x : ℂ) + (t : ℂ) * I))
    (hb : (L b).im = (F ((b : ℂ) + (t : ℂ) * I)).arg) :
    ‖∫ x in a..b, (L x).im‖ ≤ D * Real.log T := by
  obtain ⟨φ, hφ, hφb, hrep, hint⟩ := h
  have hsub : Icc a b ⊆ Icc (1 / 2 : ℝ) b :=
    fun x hx => ⟨ha.trans hx.1, hx.2⟩
  have heq := Complex.logLift_im_eq_phase_on_Icc hab hLc.continuousOn
    (hφ.mono hsub) he (fun x hx => hrep x (hsub hx)) (hb.trans hφb.symm)
  have hi : (∫ x in a..b, (L x).im) = ∫ x in a..b, φ x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact heq x (by simpa only [Set.uIcc_of_le hab] using hx)
  rw [hi]
  exact hint a ⟨ha, hab⟩

/-- Uniform outward dyadic Littlewood rectangles with the same normalized
lifts in the exact identity and both horizontal bounds. The corrected zeta
count includes the full mollifier-zero remainder. No branch-compatibility,
horizontal-budget, or zero-free-border premise is assumed. -/
theorem exists_uniform_dyadic_littlewood_normalized_horizontal_bound
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) :
    ∃ η b D H : ℝ, 0 < η ∧ η < 1 / 4 ∧ 2 ≤ b ∧ 0 < D ∧ b + 2 ≤ H ∧
      ∀ T : ℝ, H ≤ T → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1 / 2 + η →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 → ∀ α : ℝ,
            1 / 2 < α → α < b →
              ∃ (t₁ t₂ l : ℝ) (Z : Finset ℂ) (B U : ℝ → ℂ),
                T - δ < t₁ ∧ t₁ < T ∧ 2 * T < t₂ ∧ t₂ < 2 * T + δ ∧
                1 / 2 < l ∧ l < α ∧ 0 < t₁ ∧ t₁ < t₂ ∧
                (∀ s ∈ RectangleBorder ((l : ℂ) + (t₁ : ℂ) * I)
                    ((b : ℂ) + (t₂ : ℂ) * I),
                  mollifiedZeta σ (T ^ θ) ε s ≠ 0) ∧
                (∀ s, s ∈ Z ↔ s ∈ Rectangle
                  ((l : ℂ) + (t₁ : ℂ) * I) ((b : ℂ) + (t₂ : ℂ) * I) ∧
                    mollifiedZeta σ (T ^ θ) ε s = 0) ∧
                Continuous B ∧ Continuous U ∧
                (∀ x ∈ Icc l b, exp (B x) =
                  mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t₁ : ℂ) * I)) ∧
                (∀ x ∈ Icc l b, exp (U x) =
                  mollifiedZeta σ (T ^ θ) ε ((x : ℂ) + (t₂ : ℂ) * I)) ∧
                B b = log (mollifiedZeta σ (T ^ θ) ε ((b : ℂ) + (t₁ : ℂ) * I)) ∧
                U b = log (mollifiedZeta σ (T ^ θ) ε ((b : ℂ) + (t₂ : ℂ) * I)) ∧
                ‖∫ x in l..b, (B x).im‖ ≤ D * Real.log T ∧
                ‖∫ x in l..b, (U x).im‖ ≤ D * Real.log T ∧
                ‖(∫ x in l..b, (U x).im) - (∫ x in l..b, (B x).im)‖ ≤
                  2 * D * Real.log T ∧
                logRectangleBoundary (mollifiedZeta σ (T ^ θ) ε)
                  (fun x => (B x).im) (fun x => (U x).im) l b t₁ t₂ =
                  2 * Real.pi * ((∑ ρ ∈ Z,
                    (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - l)) +
                    ∑ ρ ∈ Z,
                      (analyticOrderNatAt (nonstandardMollifier σ (T ^ θ) ε) ρ : ℝ) *
                        (ρ.re - l)) ∧
                0 ≤ ∑ ρ ∈ Z,
                  (analyticOrderNatAt (nonstandardMollifier σ (T ^ θ) ε) ρ : ℝ) *
                    (ρ.re - l) ∧
                (∀ s : ℂ, α ≤ s.re → s.re ≤ b → T ≤ s.im → s.im ≤ 2 * T →
                  riemannZeta s = 0 → s ∈ Z) ∧
                ((∑ ρ ∈ Z.filter (fun s => α ≤ s.re ∧ T ≤ s.im ∧ s.im ≤ 2 * T),
                    analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
                  (((∫ t in t₁..t₂,
                      Real.log ‖mollifiedZeta σ (T ^ θ) ε ((l : ℂ) + (t : ℂ) * I)‖) -
                    (∫ t in t₁..t₂,
                      Real.log ‖mollifiedZeta σ (T ^ θ) ε ((b : ℂ) + (t : ℂ) * I)‖) +
                    2 * D * Real.log T) / (2 * Real.pi) -
                    ∑ ρ ∈ Z,
                      (analyticOrderNatAt (nonstandardMollifier σ (T ^ θ) ε) ρ : ℝ) *
                        (ρ.re - l)) / (α - l) := by
  classical
  obtain ⟨η, b, D, H, hη, hη', hb, hD, hH, hrect⟩ :=
    exists_uniform_dyadic_mollifiedZeta_outward_anchor_rectangle hε hθ
  refine ⟨η, b, D, H, hη, hη', hb, hD, hH, ?_⟩
  intro T hT σ hσ hση δ hδ hδ' α hα hαb
  obtain ⟨t₁, t₂, l, ht₁lo, ht₁hi, ht₂lo, ht₂hi, hl, hlα, ht₁pos, htt,
      hborder, hanchor, hphaseB, hphaseU⟩ :=
    hrect T hT σ hσ hση δ hδ hδ' α hα hαb
  have hlb : l ≤ b := by linarith
  obtain ⟨Z, B, U, hZ, hBc, hUc, hBe, hUe, hid, hM, hBb, hUb'⟩ :=
    exists_mollifiedZeta_littlewood_identity_with_remainder
      σ (T ^ θ) ε hlb htt.le ht₁pos hborder
  have hslit : ∀ t ∈ Icc t₁ t₂,
      mollifiedZeta σ (T ^ θ) ε ((b : ℂ) + (t : ℂ) * I) ∈ slitPlane := by
    intro t _
    apply Complex.mem_slitPlane_iff.mpr
    left
    have hh := hanchor ((b : ℂ) + (t : ℂ) * I) (by simp)
    linarith
  have hUb := hUb' hslit
  have hiB := hphaseB.integral_logLift_bound hl.le hlb hBc hBe
    (by rw [hBb]; exact Complex.log_im _)
  have hiU := hphaseU.integral_logLift_bound hl.le hlb hUc hUe
    (by rw [hUb]; exact Complex.log_im _)
  have hsigned :
      ‖(∫ x in l..b, (U x).im) - (∫ x in l..b, (B x).im)‖ ≤
        2 * D * Real.log T := by
    calc
      _ ≤ ‖∫ x in l..b, (U x).im‖ + ‖∫ x in l..b, (B x).im‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  refine ⟨t₁, t₂, l, Z, B, U, ht₁lo, ht₁hi, ht₂lo, ht₂hi, hl, hlα,
    ht₁pos, htt, hborder, hZ, hBc, hUc, hBe, hUe, hBb, hUb, hiB, hiU, hsigned,
    hid, hM, ?_, ?_⟩
  · intro s hsα hsb hsT hs2T hzero
    apply (hZ s).mpr
    constructor
    · apply (mem_Rect (by simpa using hlb) (by simpa using htt.le) s).mpr
      simpa using (show l ≤ s.re ∧ s.re ≤ b ∧ t₁ ≤ s.im ∧ s.im ≤ t₂ from
        ⟨by linarith, hsb, by linarith, by linarith⟩)
    · simp [mollifiedZeta, hzero]
  · let S := Z.filter (fun s => α ≤ s.re ∧ T ≤ s.im ∧ s.im ≤ 2 * T)
    have hmass :
        (α - l) * ((∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
          ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - l) := by
      calc
        _ = ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) * (α - l) := by
          push_cast
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ρ _
          ring
        _ ≤ ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - l) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          exact mul_le_mul_of_nonneg_left
            (sub_le_sub_right (Finset.mem_filter.mp hρ).2.1 l) (Nat.cast_nonneg _)
        _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - l) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro ρ hρ _
          have hr := ((hZ ρ).mp hρ).1.1
          have hre : (((l : ℂ) + (t₁ : ℂ) * I)).re ≤
              (((b : ℂ) + (t₂ : ℂ) * I)).re := by simpa using hlb
          rw [Set.uIcc_of_le hre] at hr
          have hρl : l ≤ ρ.re := by simpa using hr.1
          exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hρl)
    have hboundary :
        logRectangleBoundary (mollifiedZeta σ (T ^ θ) ε)
            (fun x => (B x).im) (fun x => (U x).im) l b t₁ t₂ ≤
          (∫ t in t₁..t₂, Real.log ‖mollifiedZeta σ (T ^ θ) ε
            ((l : ℂ) + (t : ℂ) * I)‖) -
          (∫ t in t₁..t₂, Real.log ‖mollifiedZeta σ (T ^ θ) ε
            ((b : ℂ) + (t : ℂ) * I)‖) + 2 * D * Real.log T := by
      have hh := le_abs_self ((∫ x in l..b, (U x).im) - (∫ x in l..b, (B x).im))
      rw [Real.norm_eq_abs] at hsigned
      unfold logRectangleBoundary
      linarith
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have heq : logRectangleBoundary (mollifiedZeta σ (T ^ θ) ε)
          (fun x => (B x).im) (fun x => (U x).im) l b t₁ t₂ / (2 * Real.pi) =
        (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) * (ρ.re - l)) +
          ∑ ρ ∈ Z,
            (analyticOrderNatAt (nonstandardMollifier σ (T ^ θ) ε) ρ : ℝ) *
              (ρ.re - l) := by
      rw [hid, mul_div_cancel_left₀ _ hpi]
    have hquot := div_le_div_of_nonneg_right hboundary
      (show 0 ≤ 2 * Real.pi by positivity)
    apply (le_div_iff₀ (sub_pos.mpr hlα)).mpr
    change ((∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) * (α - l) ≤ _
    linarith

end RiemannResearch.Analysis.ConreyBaluyot
