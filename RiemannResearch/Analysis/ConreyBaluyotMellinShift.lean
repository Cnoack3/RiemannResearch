/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMellinNegativeContour
import RiemannResearch.Analysis.ConreyBaluyotMellinResidues
import RiemannResearch.RH.ChebyshevEnergyCriterion
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
/-!
# Signed negative-contour expansion of the Conrey--Baluyot weight

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function*
(2017), Lemma 3.1.1, equation (3.1.3), pp. 94--95:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The actual kernel is meromorphic with only the two candidate simple poles
in the rectangle. The finite residue identity retains their signed residues.
Uniform horizontal-edge decay and absolute convergence on both vertical lines
give the exact identity on 1/2 < sigma <= 3/4, xi > 0.
The companion negative-contour module supplies an explicit uniform remainder.
No density or RH assertion follows from this identity alone.
-/

open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The Mellin kernel is analytic away from its two candidate poles. -/
theorem analyticAt_mellinKernel_off_poles {σ ξ : ℝ} (hξ : 0 < ξ)
    {z : ℂ} (hz : -1 < z.re) (hz0 : z ≠ 0) (hzp : z ≠ 1 - (2 * σ : ℝ)) :
    AnalyticAt ℂ (mellinKernel σ ξ) z := by
  let U : Set ℂ := {w | -1 < w.re} ∩ {0}ᶜ ∩ {(1 : ℂ) - (2 * σ : ℝ)}ᶜ
  have hU : IsOpen U :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton).inter
      isOpen_compl_singleton
  have hd : DifferentiableOn ℂ (mellinKernel σ ξ) U := by
    intro w hw
    exact (differentiableAt_mellinKernel_off_poles hξ hw.1.1 hw.1.2 hw.2).differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds ⟨⟨hz, hz0⟩, hzp⟩)

/-- Meromorphy on the whole strip, including the candidate poles. -/
theorem meromorphicAt_mellinKernel {σ ξ : ℝ} (hξ : 0 < ξ)
    {z : ℂ} (hz : -1 < z.re) :
    MeromorphicAt (mellinKernel σ ξ) z := by
  have hg : AnalyticAt ℂ (fun w : ℂ => Gamma (w + 1)) z := by
    have hd : DifferentiableOn ℂ (fun w : ℂ => Gamma (w + 1)) {w | -1 < w.re} := by
      intro w hw
      apply DifferentiableAt.differentiableWithinAt
      apply (Complex.differentiableAt_Gamma _ ?_).comp w (differentiableAt_id.add_const 1)
      intro n hn
      have he := congrArg Complex.re hn
      simp at he
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      change -1 < w.re at hw
      linarith
    exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  have hl : MeromorphicAt (fun w : ℂ => riemannZeta ((2 * σ : ℝ) + w)) z :=
    (RiemannResearch.RH.ChebyshevMellin.riemannZeta_meromorphicAt_everywhere _).comp_analyticAt
      (analyticAt_const.add analyticAt_id)
  have hr : MeromorphicAt (fun w : ℂ => riemannZeta (1 + w)) z :=
    (RiemannResearch.RH.ChebyshevMellin.riemannZeta_meromorphicAt_everywhere _).comp_analyticAt
      (analyticAt_const.add analyticAt_id)
  have hp : AnalyticAt ℂ (fun w : ℂ => (ξ : ℂ) ^ w) z := by
    have hne : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ.ne'
    simp only [Complex.cpow_def_of_ne_zero hne]
    fun_prop
  exact ((hg.meromorphicAt.mul (hl.div analyticAt_const.meromorphicAt)).mul hr).mul
    hp.meromorphicAt

private theorem order_ge_neg_one_of_residue_limit {f : ℂ → ℂ} {p c : ℂ}
    (hf : MeromorphicAt f p)
    (hc : Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 c)) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p := by
  have hs : MeromorphicAt (fun z : ℂ => z-p) p := (analyticAt_id.sub analyticAt_const).meromorphicAt
  have ho := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hs.mul hf)).mp ⟨c, hc⟩
  rw [meromorphicOrderAt_mul hs hf, meromorphicOrderAt_id_sub_const] at ho
  apply (WithTop.add_le_add_iff_left (show (1 : WithTop ℤ) ≠ ⊤ by simp)).mp
  simpa using ho

/-- The candidate poles are at most simple, from the proved actual residue limits. -/
theorem hasSimplePolesOn_mellinKernel {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hσhi : σ < 1) (hξ : 0 < ξ) :
    HasSimplePolesOn (mellinKernel σ ξ) {z | -1 < z.re} := by
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    apply order_ge_neg_one_of_residue_limit (meromorphicAt_mellinKernel hξ hz)
    simpa only [sub_zero] using mellinKernel_residue_zero hσ hξ
  by_cases hzp : z = 1 - (2 * σ : ℝ)
  · subst z
    exact order_ge_neg_one_of_residue_limit (meromorphicAt_mellinKernel hξ hz)
      (mellinKernel_residue_secondary hσ hσhi hξ)
  exact le_trans (show ((-1 : ℤ) : WithTop ℤ) ≤ 0 from by decide)
    (analyticAt_mellinKernel_off_poles hξ hz hz0 hzp).meromorphicOrderAt_nonneg


/-- The finite rectangle identity retains the signed secondary residue. -/
theorem rectangleIntegral_mellinKernel {σ ξ T : ℝ}
    (hσ : 1 / 2 < σ) (hσhi : σ ≤ 3 / 4) (hξ : 0 < ξ) (hT : 0 < T) :
    RectangleIntegral' (mellinKernel σ ξ)
      ((-(3 / 4 : ℝ) : ℂ) - T * I) (1 + T * I) =
      1 + secondaryResidueCoefficient σ *
        (ξ : ℂ) ^ ((1 : ℂ) - (2 * σ : ℝ)) := by
  classical
  let a : ℂ := (-(3 / 4 : ℝ) : ℂ) - T * I
  let b : ℂ := 1 + T * I
  let p : ℂ := 1 - (2 * σ : ℝ)
  let S : Finset ℂ := {0, p}
  let R : Set ℂ := Rectangle a b
  let P : Set ℂ := {z | meromorphicOrderAt (mellinKernel σ ξ) z < 0}
  have hab : a.re ≤ b.re := by norm_num [a, b]
  have habi : a.im ≤ b.im := by simp [a, b]; linarith
  have hRre {z : ℂ} (hz : z ∈ R) : -1 < z.re := by
    have hh := (mem_Rect hab habi z).mp hz
    have hh0 := hh.1
    simp [a] at hh0
    linarith
  have h0in : R ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hab, uIoo_of_le habi]
    norm_num [a, b, mem_reProdIm, hT, neg_neg, neg_lt_zero]
  have hpin : R ∈ 𝓝 p := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hab, uIoo_of_le habi]
    simp only [mem_reProdIm, mem_Ioo]
    constructor <;> constructor <;> norm_num [a, b, p] <;> linarith
  have hSIn {z : ℂ} (hz : z ∈ (S : Set ℂ)) : z ∈ R := by
    simp only [S, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact mem_of_mem_nhds h0in
    · exact mem_of_mem_nhds hpin
  have hmero : MeromorphicOn (mellinKernel σ ξ) R :=
    fun z hz => meromorphicAt_mellinKernel hξ (hRre hz)
  have hsub : R ∩ P ⊆ (S : Set ℂ) := by
    intro z hz
    by_cases hz0 : z = 0
    · simp [S, hz0]
    by_cases hzp : z = p
    · simp [S, hzp]
    exact False.elim (not_lt_of_ge
      (analyticAt_mellinKernel_off_poles hξ (hRre hz.1) hz0 hzp).meromorphicOrderAt_nonneg hz.2)
  have hnobd : Disjoint (RectangleBorder a b) P := by
    apply Set.disjoint_left.mpr
    intro z hzb hzP
    have hzR := rectangleBorder_subset_rectangle a b hzb
    have hzS := hsub ⟨hzR, hzP⟩
    simp only [S, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hzS
    rcases hzS with rfl | rfl
    · exact not_mem_rectangleBorder_of_rectangle_mem_nhds h0in hzb
    · exact not_mem_rectangleBorder_of_rectangle_mem_nhds hpin hzb
  have hfinite : (R ∩ P).Finite := S.finite_toSet.subset hsub
  have hsimple : HasSimplePolesOn (mellinKernel σ ξ) R :=
    (hasSimplePolesOn_mellinKernel hσ (by linarith) hξ).mono (fun z hz => hRre hz)
  have hrect := RectangleIntegral'_eq_sumResiduesIn hab habi hmero hnobd hfinite hsimple
  have hset : R ∩ P = (S : Set ℂ) ∩ P :=
    Set.Subset.antisymm (fun z hz => ⟨hsub hz, hz.2⟩)
      (fun z hz => ⟨hSIn hz.1, hz.2⟩)
  have hsum := sumResiduesIn_inter_eq_of_set_eq (F := mellinKernel σ ξ) hset
    (fun z hz hzp => residue_eq_zero_of_not_pole_of_meromorphicAt
      (hmero z (hSIn hz)) (le_of_not_gt hzp))
  have h0p : (0 : ℂ) ≠ p := by
    intro he
    have hh := congrArg Complex.re he
    simp [p] at hh
    linarith
  have hval : sumResiduesIn (mellinKernel σ ξ) (S : Set ℂ) =
      residue (mellinKernel σ ξ) 0 + residue (mellinKernel σ ξ) p := by
    unfold sumResiduesIn
    calc
      _ = ∑ z ∈ S, residue (mellinKernel σ ξ) z := by
        exact (tsum_fintype _).trans
          (Finset.sum_subtype (p := fun z : ℂ => z ∈ (S : Set ℂ))
            S (fun z => Iff.rfl) (residue (mellinKernel σ ξ))).symm
      _ = _ := by simp [S, h0p]
  rw [hsum, hval, residue_mellinKernel_zero hσ hξ,
    residue_mellinKernel_secondary hσ (by linarith) hξ] at hrect
  exact hrect

/-- Tail majorant on the whole strip; the restriction on height avoids the poles. -/
theorem norm_mellinKernel_strip_tail_le {σ ξ r t : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) (hr : -(3 / 4 : ℝ) ≤ r)
    (ht : 1 ≤ |t|) :
    ‖mellinKernel σ ξ ((r : ℂ) + t * I)‖ ≤
      (1024 * Real.Gamma (r + 5) * ξ ^ r) * (1 + t ^ 2)⁻¹ := by
  let z : ℂ := (r : ℂ) + I * t
  have hg : ‖Gamma (z + 1)‖ ≤ 16 * Real.Gamma (r + 5) / (1 + t ^ 2) ^ 2 :=
    Complex.gamma_vertical_quartic_bound hr t
  have hl : ‖riemannZeta ((2 * σ : ℝ) + z)‖ ≤ 8 * |t| := by
    have hh := Zeta23.RvM.riemannZeta_linear_growth (δ := 1 / 4)
      (by norm_num) (s := (2 * σ : ℝ) + z) (by simp [z]; linarith) (by simpa [z] using ht)
    have him : ((2 * σ : ℝ) + z).im = t := by simp [z]
    rw [him] at hh
    norm_num only at hh
    linarith only [hh, abs_nonneg t]
  have hrz : ‖riemannZeta (1 + z)‖ ≤ 8 * |t| := by
    have hh := Zeta23.RvM.riemannZeta_linear_growth (δ := 1 / 4)
      (by norm_num) (s := 1 + z) (by simp [z]; linarith) (by simpa [z] using ht)
    have him : (1 + z).im = t := by simp [z]
    rw [him] at hh
    norm_num only at hh
    linarith only [hh, abs_nonneg t]
  have hq : ‖riemannZeta ((2 * σ : ℝ) + z) / riemannZeta (2 * σ : ℝ)‖ ≤
      ‖riemannZeta ((2 * σ : ℝ) + z)‖ := by
    rw [norm_div]
    exact div_le_self (norm_nonneg _) (one_le_norm_riemannZeta_real (by linarith))
  have hprod :
      ‖riemannZeta ((2 * σ : ℝ) + z) / riemannZeta (2 * σ : ℝ)‖ *
      ‖riemannZeta (1 + z)‖ ≤ 64 * (1 + t ^ 2) := by
    calc
      _ ≤ (8 * |t|) * (8 * |t|) :=
        mul_le_mul (hq.trans hl) hrz (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith only [sq_abs t]
  have hp : ‖(ξ : ℂ) ^ z‖ = ξ ^ r := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hξ]; simp [z]
  have hD : 0 < 1 + t ^ 2 := by positivity
  have hG : 0 ≤ Real.Gamma (r + 5) := (Real.Gamma_pos_of_pos (by linarith)).le
  rw [mellinKernel_onLine]
  unfold mellinIntegrand
  change ‖Gamma (z + 1) * _ * _ * _‖ ≤ _
  simp only [norm_mul]
  rw [hp, mul_assoc ‖Gamma (z + 1)‖]
  calc
    _ ≤ (16 * Real.Gamma (r + 5) / (1 + t ^ 2) ^ 2) *
        (64 * (1 + t ^ 2)) * ξ ^ r := by
      gcongr
    _ = _ := by field_simp [ne_of_gt hD]; ring

theorem exists_mellinKernel_closed_strip_tail_bound {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ B : ℝ, ∀ σ : ℝ, 1 / 2 < σ → ∀ r ∈ Icc (-(3 / 4 : ℝ)) 1,
      ∀ t : ℝ, 1 ≤ |t| →
        ‖mellinKernel σ ξ ((r : ℂ) + t * I)‖ ≤ B * (1 + t ^ 2)⁻¹ := by
  let c : ℝ → ℝ := fun r => 1024 * Real.Gamma (r + 5) * ξ ^ r
  have hc : ContinuousOn c (Icc (-(3 / 4 : ℝ)) 1) := by
    intro r hr
    have hgc : ContinuousAt (fun u : ℝ => Complex.Gamma ((u : ℂ) + 5)) r := by
      apply (Complex.continuousAt_Gamma _ ?_).comp
        (Complex.continuous_ofReal.continuousAt.add continuousAt_const)
      intro n hn
      have he := congrArg Complex.re hn
      simp at he
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith [hr.1]
    have hg : ContinuousAt (fun r : ℝ => Real.Gamma (r + 5)) r := by
      simpa only [← Complex.ofReal_ofNat, ← Complex.ofReal_add, Complex.Gamma_ofReal,
        Complex.ofReal_re, Function.comp_def] using Complex.continuous_re.continuousAt.comp hgc
    have hp : ContinuousAt (fun r : ℝ => ξ ^ r) r :=
      (Real.continuous_const_rpow hξ.ne').continuousAt
    exact ((continuousAt_const.mul hg).mul hp).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨B, fun σ hσ r hr t ht => ?_⟩
  have hle : c r ≤ B := (le_abs_self _).trans
    (by simpa only [Real.norm_eq_abs] using hB r hr)
  exact (norm_mellinKernel_strip_tail_le hσ hξ hr.1 ht).trans
    (mul_le_mul_of_nonneg_right hle (by positivity))


/-- Exact signed contour shift to Re z = -3/4, with the actual convergent remainder. -/
theorem weight_eq_residues_add_negative {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hσhi : σ ≤ 3 / 4) (hξ : 0 < ξ) :
    weight σ ξ = 1 + secondaryResidueCoefficient σ *
      (ξ : ℂ) ^ ((1 : ℂ) - (2 * σ : ℝ)) + weightOnLine σ ξ (-(3 / 4)) := by
  let H : ℝ → ℂ := fun T =>
    ∫ r in (-(3 / 4 : ℝ))..1, mellinKernel σ ξ ((r : ℂ) + T * I)
  obtain ⟨B, hB⟩ := exists_mellinKernel_closed_strip_tail_bound hξ
  have hH (T : ℝ) (hT : 1 ≤ |T|) :
      ‖H T‖ ≤ (B * (1 + T ^ 2)⁻¹) * |1 - (-(3 / 4 : ℝ))| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro r hr
    apply hB σ hσ r _ T hT
    simpa only [uIcc_of_le (by norm_num : -(3 / 4 : ℝ) ≤ 1)] using
      uIoc_subset_uIcc hr
  have hdecay : Tendsto (fun T : ℝ => (1 + T ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_mono (fun T : ℝ => by linarith : ∀ T : ℝ, T ^ 2 ≤ 1 + T ^ 2)
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)))
  have hlim : Tendsto
      (fun T : ℝ => (B * (1 + T ^ 2)⁻¹) * |1 - (-(3 / 4 : ℝ))|) atTop (𝓝 0) := by
    simpa using (hdecay.const_mul B).mul_const |1 - (-(3 / 4 : ℝ))|
  have hpos : Tendsto H atTop (𝓝 0) :=
    squeeze_zero_norm' ((eventually_ge_atTop (1 : ℝ)).mono
      (fun T hT => hH T (hT.trans (le_abs_self T)))) hlim
  have hneg : Tendsto (fun T => H (-T)) atTop (𝓝 0) :=
    squeeze_zero_norm' ((eventually_ge_atTop (1 : ℝ)).mono (fun T hT => by
      simpa only [neg_sq] using hH (-T)
        (by simpa only [abs_neg] using hT.trans (le_abs_self T)))) hlim
  have hlineN :
      (fun t : ℝ => mellinKernel σ ξ ((-(3 / 4 : ℝ) : ℂ) + t * I)) =
      mellinIntegrand σ ξ (-(3 / 4)) := by
    funext t
    simpa only [Complex.ofReal_neg] using mellinKernel_onLine σ ξ (-(3 / 4)) t
  have hline1 :
      (fun t : ℝ => mellinKernel σ ξ ((1 : ℂ) + t * I)) =
      mellinIntegrand σ ξ 1 := by
    funext t
    simpa only [Complex.ofReal_one] using mellinKernel_onLine σ ξ 1 t
  have ha : Integrable (fun t : ℝ => mellinKernel σ ξ ((-(3 / 4 : ℝ) : ℂ) + t * I)) := by
    rw [hlineN]
    exact integrable_mellinIntegrand_negative hσ hσhi hξ
  have hb : Integrable (fun t : ℝ => mellinKernel σ ξ ((1 : ℂ) + t * I)) := by
    rw [hline1]
    exact integrable_mellinIntegrand hσ hξ (by norm_num : (0 : ℝ) < 1)
  have hva := intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hvb := intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect (T : ℝ) (hT : 0 < T) :
      (2 * Real.pi * I : ℂ)⁻¹ *
        (H (-T) - H T +
          I * (∫ t in -T..T, mellinKernel σ ξ ((1 : ℂ) + t * I)) -
          I * (∫ t in -T..T, mellinKernel σ ξ ((-(3 / 4 : ℝ) : ℂ) + t * I))) =
      1 + secondaryResidueCoefficient σ * (ξ : ℂ) ^ ((1 : ℂ) - (2 * σ : ℝ)) := by
    simpa [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, H, smul_eq_mul]
      using rectangleIntegral_mellinKernel hσ hσhi hξ hT
  have hlimrect :=
    (((hneg.sub hpos).add (hvb.const_mul I)).sub (hva.const_mul I)).const_mul
      (2 * Real.pi * I : ℂ)⁻¹
  have he := tendsto_nhds_unique hlimrect
    (tendsto_const_nhds.congr' ((eventually_ge_atTop (1 : ℝ)).mono
      fun T hT => (hrect T (by linarith)).symm))
  simp only [sub_self, zero_add] at he
  have hnorm :
      (2 * Real.pi * I : ℂ)⁻¹ *
        (I * (∫ t : ℝ, mellinKernel σ ξ ((1 : ℂ) + t * I)) -
          I * (∫ t : ℝ, mellinKernel σ ξ ((-(3 / 4 : ℝ) : ℂ) + t * I))) =
      weight σ ξ - weightOnLine σ ξ (-(3 / 4)) := by
    rw [hline1, hlineN]
    simp only [weight, weightOnLine]
    field_simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [hnorm] at he
  exact sub_eq_iff_eq_add.mp he
/-- Real-power version of the signed contour expansion. -/
theorem weight_eq_residues_add_negative_real {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hσhi : σ ≤ 3 / 4) (hξ : 0 < ξ) :
    weight σ ξ = 1 + secondaryResidueCoefficient σ *
      (ξ ^ (1 - 2 * σ) : ℝ) + weightOnLine σ ξ (-(3 / 4)) := by
  have hp : (ξ : ℂ) ^ ((1 : ℂ) - (2 * σ : ℝ)) = (ξ ^ (1 - 2 * σ) : ℝ) := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
      (Complex.ofReal_cpow hξ.le (1 - 2 * σ)).symm
  rw [weight_eq_residues_add_negative hσ hσhi hξ, hp]


end RiemannResearch.Analysis.ConreyBaluyot
