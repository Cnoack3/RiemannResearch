/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.XiTaylorDiskRadius
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Taylor coefficient growth of the completed logarithmic derivative

The canonical scalar coefficients at rational centers detect every zero in
their open convergence disks. The power series sum and the meromorphic xi
logarithmic derivative agree first as germs, then meromorphically throughout
each disk. A zero would give the latter order minus one.
-/

noncomputable section
open Filter Metric Set Zeta23 Zeta23.XiPrime
open scoped Topology NNReal ENNReal
namespace RiemannResearch.RH.RationalZeroFreeDisks

/-- Scalar Taylor coefficient at the rational center 1+iq. -/
def xiTaylorCoeff (q : ℚ) (n : ℕ) : ℂ :=
  iteratedDeriv n (logDeriv xi) (diskCenter q) / n.factorial

def xiTaylorSeries (q : ℚ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (xiTaylorCoeff q)

private theorem xi_center_series (q : ℚ) :
    HasFPowerSeriesAt (logDeriv xi) (xiTaylorSeries q) (diskCenter q) := by
  apply AnalyticAt.hasFPowerSeriesAt
  apply (xi_logDerivative_analyticAt_iff _).mpr
  intro hz
  exact lt_irrefl (1:ℝ) hz.2.2

private theorem xi_order_ne_top (z : ℂ) : analyticOrderAt xi z ≠ ⊤ := by
  intro h
  rw [analyticOrderAt_eq_top] at h
  have han : AnalyticOnNhd ℂ xi univ := fun w _ => xi_analyticAt w
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ z) h
  have hzero := hall (mem_univ (1:ℂ))
  rw [xi_one] at hzero
  norm_num at hzero

private theorem xi_pole_order {z : ℂ} (hz : IsNontrivialZero z) :
    meromorphicOrderAt (logDeriv xi) z = -1 :=
  (xi_analyticAt z).meromorphicOrderAt_logDeriv_of_zero (xi_order_ne_top z)
    ((ZeroFree.xi_eq_zero_iff z).mpr hz)

/-- A positive lower bound for the canonical radius excludes every actual
zero in the corresponding open disk, including zeros of higher multiplicity. -/
theorem xiTaylorRadius_zero_free {q : ℚ} {R : ℝ≥0}
    (hR : (R : ℝ≥0∞) ≤ (xiTaylorSeries q).radius)
    {z : ℂ} (hz : z ∈ ball (diskCenter q) (R : ℝ)) : ¬ IsNontrivialZero z := by
  let c := diskCenter q
  let p := xiTaylorSeries q
  let g : ℂ → ℂ := fun w => p.sum (w-c)
  let U := ball c (R : ℝ)
  have hpos : 0 < (R : ℝ) := dist_nonneg.trans_lt (mem_ball.mp hz)
  have hpos' : (0 : ℝ≥0∞) < R := by exact_mod_cast hpos
  have hp : 0 < p.radius := hpos'.trans_le hR
  have hg : HasFPowerSeriesOnBall g p c p.radius := by
    refine ⟨le_rfl,hp,?_⟩
    intro y hy
    simpa [g, add_comm] using (p.hasFPowerSeriesOnBall hp).hasSum hy
  have hgU : AnalyticOnNhd ℂ g U := by
    intro w hw
    apply hg.analyticAt_of_mem
    have hw' : w ∈ eball c (R : ℝ≥0∞) := by rwa [eball_coe]
    exact lt_of_lt_of_le hw' hR
  have heq : logDeriv xi =ᶠ[𝓝 c] g := by
    filter_upwards [hasFPowerSeriesAt_iff'.mp (xi_center_series q),
      hasFPowerSeriesAt_iff'.mp hg.hasFPowerSeriesAt] with w hw hw'
    exact hw.unique hw'
  have hcen : xi c ≠ 0 := by
    intro hzero
    exact lt_irrefl (1:ℝ) (((ZeroFree.xi_eq_zero_iff c).mp hzero).2.2)
  have hnear := (xi_analyticAt c).continuousAt.eventually_ne hcen
  have hmul : (fun w => g w * xi w) =ᶠ[𝓝 c] deriv xi := by
    filter_upwards [heq,hnear] with w hfg hn
    rw [← hfg]
    exact div_mul_cancel₀ _ hn
  have hprod : AnalyticOnNhd ℂ (fun w => g w * xi w) U :=
    fun w hw => (hgU w hw).mul (xi_analyticAt w)
  have hder : AnalyticOnNhd ℂ (deriv xi) U := fun w _ => (xi_analyticAt w).deriv
  have hall := hprod.eqOn_of_preconnected_of_eventuallyEq hder
    (convex_ball c (R : ℝ)).isPreconnected (mem_ball_self hpos) hmul
  have hpunct : ∀ᶠ w in 𝓝[≠] z, xi w ≠ 0 := by
    rcases (xi_analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact False.elim (xi_order_ne_top z (analyticOrderAt_eq_top.mpr h))
    · exact h
  have hnU : U ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  have hzg : logDeriv xi =ᶠ[𝓝[≠] z] g := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnU,hpunct] with w hw hn
    exact (div_eq_iff hn).mpr (hall hw).symm
  intro hzero
  have hnonneg := (hgU z hz).meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr hzg, xi_pole_order hzero] at hnonneg
  exact (show ¬ (0 : WithTop ℤ) ≤ -1 by decide) hnonneg

/-- The canonical radius at a single rational center equals the infimum
of its distances to all nontrivial zeros. -/
theorem xiTaylorSeries_radius_eq_iInf_edist (q : ℚ) :
    (xiTaylorSeries q).radius =
      ⨅ ρ : {z : ℂ // IsNontrivialZero z}, edist ρ.val (diskCenter q) := by
  apply le_antisymm
  · apply le_iInf
    intro ρ
    by_contra! hlt
    obtain ⟨r,hr,hr'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
    have hz : ρ.val ∈ eball (diskCenter q) (r:ℝ≥0∞) := hr
    rw [eball_coe] at hz
    exact xiTaylorRadius_zero_free hr'.le hz ρ.property
  · by_contra! hlt
    obtain ⟨r,hr,hr'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
    have hpos : 0 < r := by
      exact_mod_cast (show (0:ℝ≥0∞) < r from bot_le.trans_lt hr)
    have hd : DifferentiableOn ℂ (logDeriv xi) (closedBall (diskCenter q) (r:ℝ)) := by
      intro z hz
      have ha : AnalyticAt ℂ (logDeriv xi) z := by
        apply (xi_logDerivative_analyticAt_iff z).mpr
        intro hzero
        have he : edist z (diskCenter q) ≤ (r:ℝ≥0∞) := by
          rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (mem_closedBall.mp hz)
        exact (not_le_of_gt hr') ((iInf_le _ ⟨z,hzero⟩).trans he)
      exact ha.differentiableAt.differentiableWithinAt
    have hp := hd.hasFPowerSeriesOnBall hpos
    have heq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries (xi_center_series q)
    have hle := hp.r_le
    rw [heq] at hle
    exact hr.not_ge hle

/-- Countably many actual coefficient radii exactly recover the geometric
disk criterion, with no analytic-continuation assumption. -/
theorem rationalDiskBound_iff_xiTaylorRadii (R : ℝ≥0) :
    RationalDiskBound (R : ℝ) ↔ ∀ q : ℚ, (R:ℝ≥0∞) ≤ (xiTaylorSeries q).radius := by
  constructor
  · intro h q
    have hD := (taylorDisks_iff_analytic_disks R.property).mpr
      ((xi_logDerivative_disks_iff _).mpr h)
    by_contra! hlt
    have hf : (xiTaylorSeries q).radius ≠ ⊤ := (hlt.trans_le le_top).ne
    have hreal : (xiTaylorSeries q).radius.toReal < (R : ℝ) := by
      simpa using (ENNReal.toReal_lt_toReal hf ENNReal.coe_ne_top).mpr hlt
    obtain ⟨s,hs,hsR⟩ := exists_rat_btwn hreal
    have hs0 : 0 < (s:ℝ) := ENNReal.toReal_nonneg.trans_lt hs
    obtain ⟨p,hp⟩ := hD q s hs0 hsR
    have heq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries (xi_center_series q)
    have hle := hp.r_le
    rw [heq] at hle
    exact hs.not_ge (by simpa [ENNReal.toReal_ofReal hs0.le] using ENNReal.toReal_mono hf hle)
  · intro h q z hz
    by_contra! hlt
    apply xiTaylorRadius_zero_free (h q) _ hz
    have hzopen : z ∈ rationalOpenDisk q (R : ℝ) := hlt
    rw [rationalOpenDisk_eq_ball q (r := (R : ℝ)) R.property] at hzopen
    exact hzopen

/-- The exact growth statistic uses true scalar coefficients and an
extended nonnegative limsup. -/
def xiTaylorRootGrowth (q : ℚ) : ℝ≥0∞ :=
  limsup (fun n : ℕ => (↑(‖xiTaylorCoeff q n‖₊ ^ (1/(n:ℝ))) : ℝ≥0∞)) atTop

theorem xiTaylorRootGrowth_eq (q : ℚ) :
    xiTaylorRootGrowth q = (xiTaylorSeries q).radius⁻¹ := by
  rw [FormalMultilinearSeries.radius_inv_eq_limsup]
  have hnorm (n : ℕ) : ‖xiTaylorSeries q n‖₊ = ‖xiTaylorCoeff q n‖₊ := by
    apply NNReal.eq
    exact FormalMultilinearSeries.ofScalars_norm ℂ (xiTaylorCoeff q) n
  simp only [xiTaylorRootGrowth, hnorm]


/-- The supremum of the actual root-growth statistics characterizes
every supporting half-plane of the nontrivial zeros. -/
theorem xiTaylorRootGrowth_iSup_le_iff (R : ℝ≥0) :
    (⨆ q : ℚ, xiTaylorRootGrowth q) ≤ (R:ℝ≥0∞)⁻¹ ↔
      ∀ z : ℂ, IsNontrivialZero z → z.re ≤ 1-(R : ℝ) := by
  rw [iSup_le_iff]
  refine Iff.trans ?_ ((rationalDiskBound_iff_xiTaylorRadii R).symm.trans
    (rationalDiskBound_iff (r := (R : ℝ)) R.property))
  constructor
  · intro h q
    have hq := h q
    rw [xiTaylorRootGrowth_eq] at hq
    simpa only [inv_inv] using ENNReal.inv_le_inv.mpr hq
  · intro h q
    rw [xiTaylorRootGrowth_eq]
    exact ENNReal.inv_le_inv.mpr (h q)

/-- Reciprocal distance from the line of centers to the right zero boundary.
An infimum of zero yields infinite growth. -/
theorem iSup_xiTaylorRootGrowth_eq :
    (⨆ q : ℚ, xiTaylorRootGrowth q) =
      (⨅ ρ : {z : ℂ // IsNontrivialZero z}, ENNReal.ofReal (1-ρ.val.re))⁻¹ := by
  let S := ⨆ q : ℚ, xiTaylorRootGrowth q
  let d := ⨅ ρ : {z : ℂ // IsNontrivialZero z}, ENNReal.ofReal (1-ρ.val.re)
  have hcut (r : ℝ≥0) : (r:ℝ≥0∞) ≤ S⁻¹ ↔ (r:ℝ≥0∞) ≤ d := by
    have hi : (r:ℝ≥0∞) ≤ S⁻¹ ↔ S ≤ (r:ℝ≥0∞)⁻¹ := by
      constructor <;> intro h <;> simpa only [inv_inv] using ENNReal.inv_le_inv.mpr h
    rw [hi, xiTaylorRootGrowth_iSup_le_iff]
    change _ ↔ _ ≤ ⨅ ρ : {z : ℂ // IsNontrivialZero z}, ENNReal.ofReal (1-ρ.val.re)
    rw [le_iInf_iff]
    constructor
    · intro h ρ
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (by linarith only [h ρ.val ρ.property])
    · intro h z hz
      have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h ⟨z,hz⟩)
      have hgap : (r:ℝ) ≤ 1-z.re := by
        simpa [ENNReal.toReal_ofReal (sub_nonneg.mpr hz.2.2.le)] using hr
      linarith
  have hd : S⁻¹ = d := by
    apply le_antisymm
    · by_contra! h
      obtain ⟨r,hr,hs⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
      exact hr.not_ge ((hcut r).mp hs.le)
    · by_contra! h
      obtain ⟨r,hr,hs⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
      exact hr.not_ge ((hcut r).mpr hs.le)
  change S = d⁻¹
  rw [← hd, inv_inv]

/-- RH is equivalent to the scalar Cauchy–Hadamard threshold 2 at
every rational center on the line Re(s)=1. -/
theorem riemannHypothesis_iff_xiTaylorRootGrowth :
    RiemannHypothesis ↔ ∀ q : ℚ, xiTaylorRootGrowth q ≤ 2 := by
  have hgeom := rationalDiskBound_iff_xiTaylorRadii (1/2 : ℝ≥0)
  have h : RiemannHypothesis ↔ ∀ q : ℚ, 1/2 ≤ (xiTaylorSeries q).radius := by
    simpa using riemannHypothesis_iff_half_disks.trans (by simpa using hgeom)
  rw [h]
  constructor
  · intro hr q
    rw [xiTaylorRootGrowth_eq]
    simpa using ENNReal.inv_le_inv.mpr (hr q)
  · intro hg q
    specialize hg q
    rw [xiTaylorRootGrowth_eq] at hg
    simpa using ENNReal.inv_le_inv.mpr hg


open RiemannResearch.Analysis.ActualZeroOrdinate

/-- The actual nonempty zero set and its reflection give the opposite
inequality at the RH threshold. -/
theorem two_le_iSup_xiTaylorRootGrowth :
    (2 : ℝ≥0∞) ≤ ⨆ q : ℚ, xiTaylorRootGrowth q := by
  classical
  obtain ⟨T,hT⟩ := eventually_count_pos.exists
  have hc : 0 < Fintype.card (Copies T) := by rwa [card_copies]
  obtain ⟨j⟩ := Fintype.card_pos_iff.mp hc
  let ρ := j.1.val
  have hρ : IsNontrivialZero ρ := (mem_cutoff.mp j.1.property).1
  have hex : ∃ z : ℂ, IsNontrivialZero z ∧ 1/2 ≤ z.re := by
    by_cases hh : 1/2 ≤ ρ.re
    · exact ⟨ρ,hρ,hh⟩
    · have href : IsNontrivialZero (1-ρ) :=
        RvM.completedRiemannZeta_eq_zero_iff.mp
          (by rw [completedRiemannZeta_one_sub]
              exact RvM.completedRiemannZeta_eq_zero_iff.mpr hρ)
      refine ⟨1-ρ,href,?_⟩
      rw [Complex.sub_re,Complex.one_re]
      linarith
  obtain ⟨z,hz,hβ⟩ := hex
  have hD : (⨅ ρ : {w : ℂ // IsNontrivialZero w}, ENNReal.ofReal (1-ρ.val.re)) ≤
      (1/2 : ℝ≥0∞) := by
    calc
      _ ≤ ENNReal.ofReal (1-z.re) :=
        iInf_le (fun ρ : {w : ℂ // IsNontrivialZero w} => ENNReal.ofReal (1-ρ.val.re)) ⟨z,hz⟩
      _ ≤ ENNReal.ofReal (1/2) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
        norm_num
  rw [iSup_xiTaylorRootGrowth_eq]
  simpa using ENNReal.inv_le_inv.mpr hD

/-- The actual coefficient-growth supremum attains two exactly under RH. -/
theorem riemannHypothesis_iff_iSup_xiTaylorRootGrowth_eq_two :
    RiemannHypothesis ↔ (⨆ q : ℚ, xiTaylorRootGrowth q) = 2 := by
  rw [riemannHypothesis_iff_xiTaylorRootGrowth, ← iSup_le_iff]
  exact ⟨fun h => le_antisymm h two_le_iSup_xiTaylorRootGrowth, fun h => h.le⟩

/-- The algebraic continuum-contact source establishes the current upper
endpoint for the actual derivative-growth supremum. -/
theorem continuumContact_xiTaylorRootGrowth (hc : DirichletContinuumContactNonvanishing) :
    (⨆ q : ℚ, xiTaylorRootGrowth q) ≤ (ENNReal.ofReal (1-continuumContact))⁻¹ := by
  let r : ℝ≥0 := ⟨1-continuumContact, by linarith only [continuumContact_mem.2]⟩
  have he : ENNReal.ofReal (1-continuumContact) = (r:ℝ≥0∞) := by
    change ENNReal.ofReal (r:ℝ) = (r:ℝ≥0∞)
    exact ENNReal.ofReal_coe_nnreal
  rw [he, xiTaylorRootGrowth_iSup_le_iff]
  exact (rationalDiskBound_iff r.property).mp (continuumContact_disks hc)

end RiemannResearch.RH.RationalZeroFreeDisks
