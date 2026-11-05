import RiemannResearch.RH.ParetoMellinFiniteEnergy
import RiemannResearch.RH.ParetoMellinHardyEndpoint
import RiemannResearch.Analysis.WeightedMellinLogarithmicKernel
import RiemannResearch.RH.QMellinTransfer
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.NymanConductorContinuation
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Tactic.Ring

/-! # Mellin jets and analytic division on the squarefree closed span

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (5 November
2026), §8, and the locally uniform argument in the project's
`CorrectionDirichletZeroBridge20260929.md`. The atom symbol comes from the
Mellin identity in L. Báez-Duarte, Rend. Lincei Mat. Appl. 14 (2003), 5–11.
M. Balazard, *An arithmetical function related to Báez-Duarte’s criterion*,
Prop. 11, https://doi.org/10.1007/978-3-030-61887-2_3, states quotient
continuation on the full closed residue span. Here it is specialized to the
matched squarefree space. Weierstrass convergence transports every vanishing
Taylor coefficient through the Hilbert closure. Normalization fills every
removable singularity, including
the value zero at the zeta pole. -/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.RH.PrimeTreeChargeContinuation
open ZetaTwoHilbert ZetaTwoParetoTransfer QMellinTransfer
open Pareto ArithmeticConductorCommonZeros ZetaConductorRegularization

/-- The physical logarithmic kernel gives the explicit Mellin derivative
and bounds it uniformly on every stricter closed half-plane. -/
theorem mellin_logarithmic_jet (f : QHilbert) (j : ℕ) (σ : ℝ)
    (hσ : (1 / 2 : ℝ) < σ) (z : ℂ) (hz : σ ≤ z.re) :
    let g := complexPhysicalStep (toPareto f)
    iteratedDeriv j (qMellin f) z =
      MeasureTheory.WeightedMellin.logarithmicTransform g j z ∧
    ‖iteratedDeriv j (qMellin f) z‖ ^ 2 ≤
      MeasureTheory.WeightedMellin.energy g 1 * ((2 * j).factorial : ℝ) /
        (2 * σ - 1) ^ (2 * j + 1) := by
  dsimp only
  have hE := complexPhysicalStep_finiteEnergy (toPareto f)
  change iteratedDeriv j (paretoMellin (toPareto f)) z = _ ∧
    ‖iteratedDeriv j (paretoMellin (toPareto f)) z‖ ^ 2 ≤ _
  rw [← complexPhysicalStep_transform (toPareto f)]
  exact ⟨MeasureTheory.WeightedMellin.iteratedDeriv_transform_eq_logarithmicTransform
    hE j (hσ.trans_le hz), MeasureTheory.WeightedMellin.iteratedDeriv_transform_norm_sq_le_of_margin
    hE j hσ hz⟩

private theorem halfPlane_nhds {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) :
    ∀ᶠ w : ℂ in 𝓝 z, (1 / 2 : ℝ) < w.re :=
  (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz

private theorem analytic_mellin (f : QHilbert) (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    AnalyticAt ℂ (qMellin f) z := by
  change AnalyticAt ℂ (paretoMellin (toPareto f)) z
  exact paretoMellin_analyticOnNhd (toPareto f) z hz

private theorem analytic_jet (f : QHilbert) (j : ℕ) (z : ℂ)
    (hz : (1 / 2 : ℝ) < z.re) :
    AnalyticAt ℂ (iteratedDeriv j (qMellin f)) z := by
  induction j with
  | zero =>
    rw [iteratedDeriv_zero]
    exact analytic_mellin f z hz
  | succ j ih =>
    simpa only [iteratedDeriv_succ] using ih.deriv

/-- Hilbert convergence implies convergence of every Mellin jet on the open
continuity half-plane. -/
theorem tendsto_mellin_jet {ι : Type*} {l : Filter ι} {F : ι → QHilbert}
    {f : QHilbert} (hF : Tendsto F l (𝓝 f)) (j : ℕ) (z : ℂ)
    (hz : (1 / 2 : ℝ) < z.re) :
    Tendsto (fun i => iteratedDeriv j (qMellin (F i)) z) l
      (𝓝 (iteratedDeriv j (qMellin f) z)) := by
  let σ : ℝ := (z.re + 1 / 2) / 2
  have hσ : (1 / 2 : ℝ) < σ := by dsimp [σ]; linarith
  have hsz : σ < z.re := by dsimp [σ]; linarith
  have hU : IsOpen {w : ℂ | σ < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hj : ∀ k : ℕ, TendstoLocallyUniformlyOn
      (fun i => iteratedDeriv k (qMellin (F i))) (iteratedDeriv k (qMellin f))
      l {w : ℂ | σ < w.re} := by
    intro k
    induction k with
    | zero =>
      simp only [iteratedDeriv_zero]
      change TendstoLocallyUniformlyOn (fun i w => paretoMellin (toPareto (F i)) w)
        (paretoMellin (toPareto f)) l {w : ℂ | σ < w.re}
      have ht : Tendsto (fun i => toPareto (F i)) l (𝓝 (toPareto f)) :=
        toParetoCLM.continuous.continuousAt.tendsto.comp hF
      exact (paretoMellin_tendstoUniformlyOn_of_tendsto ht σ hσ).tendstoLocallyUniformlyOn
    | succ k ih =>
      have hd : ∀ i : ι, DifferentiableOn ℂ (iteratedDeriv k (qMellin (F i)))
          {w : ℂ | σ < w.re} := fun i w hw =>
        (analytic_jet (F i) k w (lt_trans hσ hw)).differentiableAt.differentiableWithinAt
      simpa only [iteratedDeriv_succ, Function.comp_def] using
        ih.deriv (Eventually.of_forall hd) hU
  exact (hj j).tendsto_at hsz

/-- At an off-pole point in the half-plane every finite squarefree
combination has an analytic zeta factor in its Mellin germ. -/
private theorem finite_factor (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) (hz1 : z ≠ 1)
    (f : QHilbert) (hf : f ∈ Submodule.span ℝ (range ZetaTwoOptimizerStage.squarefreeAtom)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      qMellin f =ᶠ[𝓝 z] fun w => riemannZeta w * g w := by
  let S : Submodule ℝ QHilbert := {
    carrier := {a | ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      qMellin a =ᶠ[𝓝 z] fun w => riemannZeta w * g w}
    zero_mem' := by
      refine ⟨fun _ => 0, analyticAt_const, ?_⟩
      filter_upwards [halfPlane_nhds hz] with w hw
      exact (qMellinContinuous w hw).map_zero.trans (mul_zero _).symm
    add_mem' := by
      rintro a b ⟨g, hg, hga⟩ ⟨h, hh, hhb⟩
      refine ⟨fun w => g w + h w, hg.add hh, ?_⟩
      filter_upwards [halfPlane_nhds hz, hga, hhb] with w hw haw hbw
      rw [qMellin_add a b w hw, haw, hbw, mul_add]
    smul_mem' := by
      rintro c a ⟨g, hg, hga⟩
      refine ⟨fun w => (c : ℂ) * g w, analyticAt_const.mul hg, ?_⟩
      filter_upwards [halfPlane_nhds hz, hga] with w hw haw
      rw [qMellin_smul c a w hw, haw, Complex.real_smul]
      ring }
  have hspan : Submodule.span ℝ (range ZetaTwoOptimizerStage.squarefreeAtom) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    unfold ZetaTwoOptimizerStage.squarefreeAtom
    split_ifs
    · have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
      refine ⟨fun w => conductorSymbol (i + 2) w / w,
        (analyticAt_conductorSymbol _ _).div analyticAt_id hz0, ?_⟩
      filter_upwards [halfPlane_nhds hz, compl_singleton_mem_nhds hz1] with w hw hw1
      rw [qMellin_residue_zeta _ (by omega) _ (by linarith) hw1,
        conductorSymbol_eq_cpow _ (by omega)]
      ring
    · exact S.zero_mem
  exact hspan hf

/-- The order at every off-pole point, including a multiple zeta zero,
survives passage to the squarefree closed span. -/
theorem mellin_order_ge_zeta (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure)
    (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) (hz1 : z ≠ 1) :
    analyticOrderAt riemannZeta z ≤ analyticOrderAt (qMellin f) z := by
  have haz := analyticOn_riemannZeta z hz1
  have hzfin := analyticOrderAt_riemannZeta_ne_top_of_ne_one hz1
  have hm := Nat.cast_analyticOrderNatAt hzfin
  change f ∈ _root_.closure
    (Submodule.span ℝ (range ZetaTwoOptimizerStage.squarefreeAtom) : Set QHilbert) at hf
  obtain ⟨F, hmem, hF⟩ := mem_closure_iff_seq_limit.mp hf
  rw [← hm, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (analytic_mellin f z hz)]
  intro j hj
  have hzero (i : ℕ) : iteratedDeriv j (qMellin (F i)) z = 0 := by
    obtain ⟨g, hg, he⟩ := finite_factor z hz hz1 _ (hmem i)
    have hord : (analyticOrderNatAt riemannZeta z : ℕ∞) ≤
        analyticOrderAt (qMellin (F i)) z := by
      rw [hm, analyticOrderAt_congr he]
      change analyticOrderAt riemannZeta z ≤ analyticOrderAt (riemannZeta * g) z
      rw [analyticOrderAt_mul haz hg]
      exact le_add_of_nonneg_right (bot_le : 0 ≤ analyticOrderAt g z)
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analytic_mellin (F i) z hz)).mp hord j hj
  have hlim := tendsto_mellin_jet hF j z hz
  apply tendsto_nhds_unique hlim
  simpa only [hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

private def rawQuotient (f : QHilbert) (s : ℂ) : ℂ :=
  s * qMellin f s / riemannZeta s

private def halfPlane : Set ℂ := {s | (1 / 2 : ℝ) < s.re}

/-- The canonical removable extension of the quotient. Its value at a
multiple zero can differ from Lean's pointwise quotient at that zero. -/
def chargeExtension (f : QHilbert) : ℂ → ℂ := toMeromorphicNFOn (rawQuotient f) halfPlane

private theorem local_model (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure)
    (z : ℂ) (hz : z ∈ halfPlane) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ rawQuotient f =ᶠ[𝓝[≠] z] g ∧
      (z = 1 → g z = 0) := by
  have hfA := analytic_mellin f z hz
  by_cases hz1 : z = 1
  · subst z
    have hC := analyticAt_conductorZeta 2 (by norm_num) 1
    have hC0 := conductorZeta_one_ne_zero 2 (by norm_num)
    refine ⟨fun w => w * qMellin f w * conductorSymbol 2 w / conductorZeta 2 w,
      ((analyticAt_id.mul hfA).mul (analyticAt_conductorSymbol 2 1)).div hC hC0, ?_, ?_⟩
    · have hev : ∀ᶠ w : ℂ in 𝓝 1, conductorZeta 2 w ≠ 0 :=
        hC.continuousAt.eventually_ne hC0
      filter_upwards [self_mem_nhdsWithin, hev.filter_mono nhdsWithin_le_nhds] with w hw hCw
      have hE := conductorZeta_of_ne_one 2 (show w ≠ 1 from hw)
      have hprod : riemannZeta w * conductorSymbol 2 w ≠ 0 := hE ▸ hCw
      rw [rawQuotient, hE]
      field_simp [left_ne_zero_of_mul hprod, right_ne_zero_of_mul hprod]
    · intro _
      simp [conductorSymbol_one 2 (by norm_num)]
  · have hZ : AnalyticAt ℂ riemannZeta z := analyticOn_riemannZeta z hz1
    have hfin := analyticOrderAt_riemannZeta_ne_top_of_ne_one hz1
    have hle := mellin_order_ge_zeta f hf z hz hz1
    rw [← Nat.cast_analyticOrderNatAt hfin] at hle
    obtain ⟨G, hG, heG⟩ := (natCast_le_analyticOrderAt hfA).mp hle
    obtain ⟨H, hH, hH0, heH⟩ := hZ.analyticOrderAt_ne_top.mp hfin
    refine ⟨fun w => w * G w / H w, (analyticAt_id.mul hG).div hH hH0, ?_, fun h => (hz1 h).elim⟩
    filter_upwards [self_mem_nhdsWithin, heG.filter_mono nhdsWithin_le_nhds,
      heH.filter_mono nhdsWithin_le_nhds] with w hw hg hh
    let a := (w - z) ^ analyticOrderNatAt riemannZeta z
    have ha : a ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (show w ≠ z from hw))
    change qMellin f w = a * G w at hg
    change riemannZeta w = a * H w at hh
    rw [rawQuotient, hg, hh, show w * (a * G w) = a * (w * G w) by ring,
      mul_div_mul_left _ _ ha]

private theorem model_eq (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure)
    {z : ℂ} (hz : z ∈ halfPlane) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g z)
    (he : rawQuotient f =ᶠ[𝓝[≠] z] g) :
    chargeExtension f =ᶠ[𝓝 z] g := by
  have hm : MeromorphicOn (rawQuotient f) halfPlane := by
    intro w hw
    obtain ⟨h, hh, e, _⟩ := local_model f hf w hw
    exact (MeromorphicAt.meromorphicAt_congr e).mpr hh.meromorphicAt
  exact (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hm hz).trans
    (by simpa only [toMeromorphicNFAt_eq_self.mpr hg.meromorphicNFAt] using
      toMeromorphicNFAt_eventuallyEq_nhds_congr he)

theorem chargeExtension_analytic (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    AnalyticOnNhd ℂ (chargeExtension f) {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  intro z hz
  obtain ⟨g, hg, he, _⟩ := local_model f hf z hz
  exact hg.congr (model_eq f hf hz hg he).symm

theorem chargeExtension_one (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    chargeExtension f 1 = 0 := by
  have h1 : (1 : ℂ) ∈ halfPlane := by norm_num [halfPlane]
  obtain ⟨g, hg, he, h1g⟩ := local_model f hf 1 h1
  exact (model_eq f hf h1 hg he).eq_of_nhds.trans (h1g rfl)

theorem chargeExtension_eq (f : QHilbert) (hf : f ∈ ZetaTwoOptimizerStage.closure)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (h1 : s ≠ 1) (hZ : riemannZeta s ≠ 0) :
    chargeExtension f s = s * qMellin f s / riemannZeta s := by
  have hg : AnalyticAt ℂ (rawQuotient f) s :=
    (analyticAt_id.mul (analytic_mellin f s hs)).div
      (analyticOn_riemannZeta s h1) hZ
  exact (model_eq f hf hs hg Filter.EventuallyEq.rfl).eq_of_nhds

/-- The matched displacement has the canonical extension with its polar value
and the prescribed quotient on the zero-free set. -/
theorem displacement_chargeExtension :
    let d := QSquarefreeDisplacementRigidity.displacement
    AnalyticOnNhd ℂ (chargeExtension d) {z : ℂ | (1 / 2 : ℝ) < z.re} ∧
      chargeExtension d 1 = 0 ∧
      ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → riemannZeta s ≠ 0 →
        chargeExtension d s = s * qMellin d s / riemannZeta s := by
  exact ⟨chargeExtension_analytic _ QSquarefreeDisplacementRigidity.displacement_mem,
    chargeExtension_one _ QSquarefreeDisplacementRigidity.displacement_mem,
    chargeExtension_eq _ QSquarefreeDisplacementRigidity.displacement_mem⟩

end RiemannResearch.RH.PrimeTreeChargeContinuation
