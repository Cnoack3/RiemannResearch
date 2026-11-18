/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryGapTailDensity
import RiemannResearch.Analysis.OrdinateWindowVariance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # An integrated positive-gap criterion

The short-window mean already forces the fixed-width lower second moment.
The short-window upper estimate of Goldston–Lee–Schettler–Suriajaya
(arXiv:2503.15449v3, Section 3)
and a scalar integrated positive-gap bound at the same width then characterize
the equal-ordinate count asymptotic.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance
open OrdinateWindowVariance

/-- Shift the ordinates by h and enlarge the support to T+B. This exact
variance identity avoids needing a separate lower bound on the first ordinate. -/
theorem physicalTriangle_eq_shiftedMean_sq_add_windowVariance {T h B : ℝ}
    (hT : 0 < T) (hh : 0 ≤ h) (hB : h ≤ B) :
    T * actualPhysicalTriangleEnergy T h =
      ((Ncount 0 T : ℝ) * h) ^ 2 / (T + B) +
        ∫ t : ℝ, centeredCount (Finset.univ : Finset (Copies T))
          (fun i => copyOrdinate T i + h) (T + B) h
          ((Ncount 0 T : ℝ) * h / (T + B)) t ^ 2 := by
  let s : Finset (Copies T) := Finset.univ
  let x : Copies T → ℝ := fun i => copyOrdinate T i + h
  let m := (Ncount 0 T : ℝ) * h / (T + B)
  have hTB : 0 < T + B := add_pos_of_pos_of_nonneg hT (hh.trans hB)
  have hx : ∀ i ∈ s, h ≤ x i ∧ x i ≤ T + B := by
    intro i _
    obtain ⟨_, hlo, hhi⟩ := mem_cutoff.mp i.1.2
    exact ⟨le_add_of_nonneg_left hlo.le, add_le_add hhi hB⟩
  have hm : (s.card : ℝ) * h = (T + B) * m := by
    dsimp [s, m]
    rw [card_copies, mul_comm (T + B), div_mul_cancel₀ _ hTB.ne']
  have he := (div_eq_iff hTB.ne').mp
    (triangle_eq_mean_sq_add_variance s x (T + B) h m hTB hh hx hm)
  have hdiff (i j : Copies T) : x i - x j = i.1.1.im - j.1.1.im := by
    dsimp [x, copyOrdinate]
    ring
  simp only [hdiff, s] at he
  unfold actualPhysicalTriangleEnergy
  rw [mul_comm T, div_mul_cancel₀ _ hT.ne', he]
  dsimp only [m, x, s]
  field_simp [hTB.ne']

/-- The unconditional fixed-width lower second moment. -/
theorem eventually_physicalTriangle_ge_sq_sub {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      R ^ 2 - ε ≤ actualPhysicalTriangleEnergy T (R / (Real.log T / (2 * Real.pi))) := by
  have hc : Tendsto (fun _ : ℝ => R) atTop (𝓝 R) := tendsto_const_nhds
  have hnum : Tendsto (fun T : ℝ =>
      (((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) * R) ^ 2) atTop (𝓝 (R ^ 2)) := by
    simpa only [one_mul] using (tendsto_count_div_mainTerm.mul hc).pow 2
  have hinv : Tendsto (fun T : ℝ => R / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hden : Tendsto (fun T : ℝ => 1 + R / T) atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hinv
  have hmean : Tendsto (fun T : ℝ =>
      (((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) * R) ^ 2 /
        (1 + R / T)) atTop (𝓝 (R ^ 2)) := by
    change Tendsto ((fun T : ℝ =>
      (((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) * R) ^ 2) /
        (fun T : ℝ => 1 + R / T)) atTop (𝓝 (R ^ 2))
    simpa only [div_one] using hnum.div hden (one_ne_zero : (1 : ℝ) ≠ 0)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.pi),
    hmean.eventually (lt_mem_nhds (sub_lt_self _ hε))] with T hT hlog hmean
  let L := Real.log T / (2 * Real.pi)
  have hT0 := zero_lt_one.trans hT
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hL1 : 1 ≤ L := (le_div_iff₀ (by positivity)).mpr (by simpa only [one_mul] using hlog)
  have hh : 0 ≤ R / L := div_nonneg hR.le hL.le
  have hB : R / L ≤ R := (div_le_iff₀ hL).mpr (by
    nlinarith only [mul_nonneg hR.le (sub_nonneg.mpr hL1)])
  have hTR := add_pos hT0 hR
  have he := physicalTriangle_eq_shiftedMean_sq_add_windowVariance hT0 hh hB
  have hv : 0 ≤ ∫ t : ℝ, centeredCount (Finset.univ : Finset (Copies T))
      (fun i => copyOrdinate T i + R / L) (T + R) (R / L)
      ((Ncount 0 T : ℝ) * (R / L) / (T + R)) t ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hle : ((Ncount 0 T : ℝ) * (R / L)) ^ 2 / (T + R) / T ≤
      actualPhysicalTriangleEnergy T (R / L) := by
    apply (div_le_iff₀ hT0).mpr
    rw [mul_comm (actualPhysicalTriangleEnergy T (R / L)) T, he]
    exact le_add_of_nonneg_right hv
  have hrewrite :
      (((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) * R) ^ 2 /
          (1 + R / T) = ((Ncount 0 T : ℝ) * (R / L)) ^ 2 / (T + R) / T := by
    have haux : 1 + R / T = (T + R) / T := by rw [add_div, div_self hT0.ne']
    rw [haux, show T * Real.log T / (2 * Real.pi) = T * L by dsimp [L]; ring]
    field_simp [hT0.ne', hL.ne', hTR.ne']
    <;> ring
  rw [hrewrite] at hmean
  exact hmean.le.trans hle

/-- A uniform logarithmic envelope at fixed widths supplies the cofinal
moment premise. Equations (3.6)–(3.7) and Proposition 1 of GLSS provide
this envelope externally. The estimate itself remains the hypothesis. -/
theorem cofinalShortWindowSecondMomentUpper_of_logarithmicUpper
    (h : ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 1 ≤ R → ∀ᶠ T : ℝ in atTop,
      actualPhysicalTriangleEnergy T (R / (Real.log T / (2 * Real.pi))) ≤
        R ^ 2 + C * Real.log (R + 2)) :
    CofinalShortWindowSecondMomentUpper := by
  obtain ⟨C, hC, he⟩ := h
  intro ε hε B
  let δ := ε / (3 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hl : Asymptotics.IsLittleO atTop Real.log (fun x : ℝ => x) := by
    simpa only [Real.rpow_one] using isLittleO_log_rpow_atTop (r := 1) zero_lt_one
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (hl.bound hδ)
  let R := max (max B 1) R₀
  have hR1 : 1 ≤ R := (le_max_right B 1).trans (le_max_left _ _)
  have hR' : R₀ ≤ R + 2 := (le_max_right (max B 1) R₀).trans (by linarith)
  have hl' : Real.log (R + 2) ≤ δ * (R + 2) := by
    apply (le_abs_self _).trans
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ R + 2)] using hR₀ _ hR'
  have hbudget : C * Real.log (R + 2) ≤ ε * R := calc
    _ ≤ C * (δ * (R + 2)) := mul_le_mul_of_nonneg_left hl' hC.le
    _ ≤ C * (δ * (3 * R)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hδ.le) hC.le
    _ = _ := by dsimp [δ]; field_simp [hC.ne']
  refine ⟨R, (le_max_left B 1).trans (le_max_left _ _), ?_⟩
  filter_upwards [he R hR1] with T hT
  exact hT.trans (add_le_add_right hbudget _)

/-- A common-width short-window upper bound and a single integrated
positive-gap lower bound, at arbitrarily large fixed widths. -/
def CofinalIntegratedPositiveGapLower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ B : ℝ, ∃ R : ℝ, max B 1 ≤ R ∧ ∀ᶠ T : ℝ in atTop,
    actualPhysicalTriangleEnergy T (R / (Real.log T / (2 * Real.pi))) ≤ R ^ 2 + ε * R ∧
    R ^ 2 - (1 + ε) * R ≤ 2 * (∫ u in (0 : ℝ)..R, positiveGapMass T u)

theorem cofinalIntegratedPositiveGapLower_iff_collision_limit
    (hm : CofinalShortWindowSecondMomentUpper) :
    CofinalIntegratedPositiveGapLower ↔
      Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))
        atTop (𝓝 1) := by
  constructor
  · intro hg
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [tendsto_count_div_mainTerm.eventually (lt_mem_nhds ha),
        eventually_gt_atTop (1 : ℝ)] with T hN hT
      have hC : Ncount 0 T ≤ actualCollision T := by
        rw [actualCollision_eq_count_add_excess T]
        omega
      have hD : 0 ≤ T * Real.log T / (2 * Real.pi) :=
        div_nonneg (mul_nonneg (zero_le_one.trans hT.le) (Real.log_nonneg hT.le)) (by positivity)
      exact hN.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast hC) hD)
    · intro b hb
      let ε := (b - 1) / 3
      have hε : 0 < ε := by dsimp [ε]; linarith
      obtain ⟨R, hR, hw⟩ := hg ε hε 1
      have hR0 : 0 < R := zero_lt_one.trans_le ((le_max_right _ _).trans hR)
      filter_upwards [hw, eventually_gt_atTop (1 : ℝ)] with T ⟨hW, hI⟩ hT
      rw [physicalTriangle_eq_collision_add_positive_gaps hT hR0.le] at hW
      have hC :
          R * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) ≤
            R * (1 + 2 * ε) := by nlinarith only [hW, hI]
      exact (le_of_mul_le_mul_left hC hR0).trans_lt (by dsimp [ε]; linarith)
  · intro h ε hε B
    obtain ⟨R, hR, hW⟩ := hm ε hε (max B 1)
    have hR0 : 0 < R := zero_lt_one.trans_le ((le_max_right _ _).trans hR)
    refine ⟨R, hR, ?_⟩
    have hεR : 0 < (ε / 2) * R := mul_pos (by positivity) hR0
    have hc : 1 < 1 + ε / 2 := by linarith
    filter_upwards [hW, eventually_physicalTriangle_ge_sq_sub hR0 hεR,
      h.eventually (gt_mem_nhds hc), eventually_gt_atTop (1 : ℝ)] with T hW hL hC hT
    refine ⟨hW, ?_⟩
    rw [physicalTriangle_eq_collision_add_positive_gaps hT hR0.le] at hL
    have hC' := mul_le_mul_of_nonneg_left hC.le hR0.le
    nlinarith only [hL, hC']

/-- The same scalar large-width lower tests give both density-one conclusions. -/
theorem density_one_of_cofinalIntegratedPositiveGapLower
    (hm : CofinalShortWindowSecondMomentUpper) (hg : CofinalIntegratedPositiveGapLower) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) :=
  density_one_of_collision_limit ((cofinalIntegratedPositiveGapLower_iff_collision_limit hm).mp hg)

end RiemannResearch.Analysis.MontgomeryPositiveGap
