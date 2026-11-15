/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotDyadicLittlewood
import RiemannResearch.Analysis.ConreyBaluyotMomentContinuity
import Mathlib.Tactic.Linarith
/-!
# Dyadic zero counts from a moment on one prescribed line

This assembles the established normalized Littlewood rectangle with
continuity of the actual moment and the uniform outward endpoint transfer.
The sole substantive moment premise is now on the original dyadic interval
and one prescribed line. All constants precede T and sigma; slack is arbitrary.

Source: the user-provided Conrey--Baluyot right-boundary continuation and
Baluyot (2017), Section 3.2 for the Littlewood/moment strategy:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .
The quantitative moment and arithmetic estimates remain open.
-/
noncomputable section
open Complex Set
open scoped BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Conditional research reduction from a moment on one prescribed line.
No neighborhood moment, outward endpoint moment or denominator-gap provider
is assumed. Exact signed boundary terms and mollifier multiplicities persist. -/
theorem exists_uniform_dyadic_count_of_prescribed_line_moment
    {ε θ : ℝ} (hε : 0 ≤ ε) (hθ : 0 < θ) :
    ∃ η b D C H : ℝ, 0 < η ∧ η < 1/4 ∧ 2 ≤ b ∧ 0 < D ∧ 0 < C ∧ b+2 ≤ H ∧
      ∀ T σ : ℝ, H ≤ T →
        1/2 + 1 / Real.log (T ^ θ) ≤ σ → σ ≤ 1/2 + η →
        ∀ l₀ α E κ : ℝ, 1/2 < l₀ → l₀ < α → α < b → 0 ≤ E → 0 < κ →
          mollifiedSecondMoment σ (T ^ θ) ε l₀ T (2*T) ≤ T+E →
          ∃ (t₁ t₂ l : ℝ) (Z : Finset ℂ) (B U : ℝ → ℂ),
            T-1/4 < t₁ ∧ t₁ < T ∧ 2*T < t₂ ∧ t₂ < 2*T+1/4 ∧
            1/2 < l ∧ l < α ∧ (α-l₀)/2 ≤ α-l ∧
            0 < t₁ ∧ t₁ < t₂ ∧
            (∀ s ∈ RectangleBorder ((l : ℂ) + (t₁ : ℂ)*I)
                ((b : ℂ) + (t₂ : ℂ)*I), mollifiedZeta σ (T ^ θ) ε s ≠ 0) ∧
            (∀ s, s ∈ Z ↔ s ∈ Rectangle ((l : ℂ)+(t₁ : ℂ)*I)
                ((b : ℂ)+(t₂ : ℂ)*I) ∧ mollifiedZeta σ (T ^ θ) ε s = 0) ∧
            Continuous B ∧ Continuous U ∧
            (∀ x ∈ Icc l b, exp (B x) =
              mollifiedZeta σ (T ^ θ) ε ((x : ℂ)+(t₁ : ℂ)*I)) ∧
            (∀ x ∈ Icc l b, exp (U x) =
              mollifiedZeta σ (T ^ θ) ε ((x : ℂ)+(t₂ : ℂ)*I)) ∧
            B b = log (mollifiedZeta σ (T ^ θ) ε ((b : ℂ)+(t₁ : ℂ)*I)) ∧
            U b = log (mollifiedZeta σ (T ^ θ) ε ((b : ℂ)+(t₂ : ℂ)*I)) ∧
            ‖(∫ x in l..b, (U x).im) - (∫ x in l..b, (B x).im)‖ ≤
              2*D*Real.log T ∧
            logRectangleBoundary (mollifiedZeta σ (T ^ θ) ε)
              (fun x => (B x).im) (fun x => (U x).im) l b t₁ t₂ =
              2*Real.pi * ((∑ ρ ∈ Z,
                (analyticOrderNatAt riemannZeta ρ : ℝ)*(ρ.re-l)) +
                ∑ ρ ∈ Z,
                  (analyticOrderNatAt (nonstandardMollifier σ (T ^ θ) ε) ρ : ℝ)*(ρ.re-l)) ∧
            0 ≤ ∑ ρ ∈ Z,
              (analyticOrderNatAt (nonstandardMollifier σ (T ^ θ) ε) ρ : ℝ)*(ρ.re-l) ∧
            |∫ t in t₁..t₂, Real.log ‖mollifiedZeta σ (T ^ θ) ε
              ((b : ℂ)+(t : ℂ)*I)‖| ≤ C ∧
            (∀ s : ℂ, α ≤ s.re → T ≤ s.im → s.im ≤ 2*T →
              riemannZeta s = 0 → s ∈ Z) ∧
            mollifiedSecondMoment σ (T ^ θ) ε l t₁ t₂ ≤ t₂-t₁+E+κ ∧
            ((∑ ρ ∈ Z.filter (fun s => α ≤ s.re ∧ T ≤ s.im ∧ s.im ≤ 2*T),
              analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
              (((t₂-t₁)*Real.log (1+(E+κ)/(t₂-t₁))/2 + C + 2*D*Real.log T) /
                (2*Real.pi) -
                ∑ ρ ∈ Z,
                  (analyticOrderNatAt (nonstandardMollifier σ (T ^ θ) ε) ρ : ℝ)*(ρ.re-l)) /
                (α-l) := by
  classical
  obtain ⟨η₀, b, D, C, H₀, hη₀, hη₀', hb, hD, hC, hH₀, hrect⟩ :=
    exists_uniform_dyadic_littlewood_normalized_boundary_bound hε hθ
  obtain ⟨η₁, Y, hη₁, hη₁', hY, hend⟩ :=
    exists_uniform_mollifiedSecondMoment_endpoint_transfer hε
  refine ⟨min η₀ η₁, b, D, C, max H₀ (Y ^ θ⁻¹),
    lt_min hη₀ hη₁, (min_le_left _ _).trans_lt hη₀', hb, hD, hC,
    hH₀.trans (le_max_left _ _), ?_⟩
  intro T σ hT hσ hση l₀ α E κ hl₀ hlα hαb hE hκ hm
  have hT₀ : H₀ ≤ T := (le_max_left _ _).trans hT
  have hT2 : 2 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hση₀ : σ ≤ 1/2+η₀ := by linarith [min_le_left η₀ η₁]
  have hση₁ : σ ≤ 1/2+η₁ := by linarith [min_le_right η₀ η₁]
  have hYpow : Y ≤ T ^ θ := by
    calc
      Y = (Y ^ θ⁻¹) ^ θ :=
        (Real.rpow_inv_rpow (by linarith : 0 ≤ Y) hθ.ne').symm
      _ ≤ T ^ θ := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _)
        ((le_max_right _ _).trans hT) hθ.le
  obtain ⟨δ, hδ, hδ', htransfer⟩ := hend T (T ^ θ) (κ/2) hT2 hYpow (by linarith)
  have hcentral : mollifiedSecondMoment σ (T ^ θ) ε l₀ T (2*T) ≤ 2*T-T+E := by
    linarith
  obtain ⟨a, c, ha, hal₀, hl₀c, hcα, hgap, hnear⟩ :=
    exists_mollifiedSecondMoment_admissible_interval σ (T ^ θ) ε hl₀ hlα
      hTpos (by linarith) (show 0 < κ/2 by linarith) hcentral
  obtain ⟨t₁, t₂, l, Z, B, U, h1lo, h1hi, h2lo, h2hi, hl, hal, hlc, hlα',
    h1pos, h12, hborder, hZ, hBc, hUc, hBe, hUe, hBb, hUb,
    hBbound, hUbound, hdiff, hid, hM, hRc, hR, hcover, hold, hcount⟩ :=
    hrect T hT₀ σ hσ hση₀ δ hδ hδ' a c α ha.le (hal₀.trans hl₀c) hcα.le hαb
  have hmnear : mollifiedSecondMoment σ (T ^ θ) ε l T (2*T) ≤ T+(E+κ/2) := by
    have hh := hnear l ⟨hal, hlc⟩
    linarith
  have hmout : mollifiedSecondMoment σ (T ^ θ) ε l t₁ t₂ ≤ t₂-t₁+E+κ := by
    have hh := htransfer σ l t₁ t₂ (E+κ/2) hσ hση₁ (by linarith)
      h1lo.le h1hi.le h2lo.le h2hi.le hmnear
    linarith
  refine ⟨t₁, t₂, l, Z, B, U, by linarith, h1hi, h2lo, by linarith,
    hl, hlα', by linarith, h1pos, h12, hborder, hZ, hBc, hUc,
    hBe, hUe, hBb, hUb, hdiff, hid, hM, hR, hcover, hmout, ?_⟩
  apply hcount (E+κ) (by linarith)
  change mollifiedSecondMoment σ (T ^ θ) ε l t₁ t₂ ≤ t₂-t₁+(E+κ)
  linarith

end RiemannResearch.Analysis.ConreyBaluyot
