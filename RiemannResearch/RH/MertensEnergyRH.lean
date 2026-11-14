/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.MertensWeightedEnergy
import RiemannResearch.RH.MertensWeightedMoments
import RiemannResearch.Analysis.CesaroFiniteCalculus
import RiemannResearch.Analysis.FirstMellinSeries
import RiemannResearch.RH.BurnolCayleyJensen
import RiemannResearch.RH.TreeEulerCriterion
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.FunProp

/-!
# Actual weighted Mertens energy implies zero exclusion and RH

Source: the user's Reciprocal_Residue_Density_and_Direct_RH_Agenda (1).tex,
Section 6 and agenda Step 2. This development closes its direct analytic
implication using the first-difference Dirichlet series of the actual Mertens
sums, finite Abel summation with its boundary term, local normal convergence,
and the repository's proved holomorphic prime-tree criterion.

The Euler-product normalization is the classical formula
https://dlmf.nist.gov/25.2.E11 . This reference supports that normalization;
all continuation and zero-exclusion implications below are proved in Lean.
No external analytic provider, RH hypothesis, or novelty claim is used.

The uniform small-damping energy/signed-cancellation bounds remain Open.
The named RH theorems are conditional research reductions, not a proof of
those arithmetic bounds. Zero obstructions retain strict half-plane margins.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.MertensWeightedEnergy
open RiemannResearch.Analysis.Cesaro

theorem mertensPrefix_complex (N : ℕ) :
    partialSum (fun n => (ArithmeticFunction.moebius n : ℂ)) N =
      (mertensPrefix N : ℂ) := by
  simp only [partialSum, mertensPrefix,
    RiemannResearch.LinearAlgebra.CumulativeCellEnergy.cumulative,
    mobiusCoefficients, Complex.ofReal_sum, Complex.ofReal_intCast]

def mertensTransform (s : ℂ) : ℂ :=
  ∑' n : ℕ, mellinFirst s (n + 1) * (mertensPrefix (n + 1) : ℂ)

theorem mertensTransform_summable (ε : ℝ) (hE : HasFiniteEnergy ε)
    {s : ℂ} (hs0 : 0 < s.re) (hs : 1 / 2 + ε < s.re) :
    Summable (fun n : ℕ =>
      mellinFirst s (n + 1) * (mertensPrefix (n + 1) : ℂ)) := by
  apply Summable.of_norm_bounded
    ((summable_absolute_mertens_moment ε s.re hE hs).mul_left ‖s‖)
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) * |mertensPrefix (n+1)| :=
      mul_le_mul_of_nonneg_right
        (mellinFirst_norm_le s hs0 (n+1) (Nat.succ_pos _)) (abs_nonneg _)
    _ = _ := by
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show -s.re - 1 = -1 - s.re by ring]
      ring

theorem mertensTransform_analyticOnNhd (ε : ℝ) (hε : 0 ≤ ε)
    (hE : HasFiniteEnergy ε) :
    AnalyticOnNhd ℂ mertensTransform {s : ℂ | 1/2 + ε < s.re} := by
  intro s hs
  let σ : ℝ := (1/2 + ε + s.re)/2
  have hσ : 1/2 + ε < σ := by dsimp [σ]; change 1/2 + ε < s.re at hs; linarith
  have hσ0 : 0 < σ := by linarith
  have ha : Summable (fun n : ℕ =>
      ‖(mertensPrefix (n+1) : ℂ)‖ * ((n : ℝ)+1)^(-1-σ)) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      summable_absolute_mertens_moment ε σ hE hσ
  have h := firstMellinSeries_analyticOnNhd (fun n => (mertensPrefix n : ℂ)) σ hσ0 ha s
    (show σ < s.re by dsimp [σ]; change 1/2 + ε < s.re at hs; linarith)
  have heq : firstMellinSeries (fun n => (mertensPrefix n : ℂ)) = mertensTransform := by
    funext z
    simp only [firstMellinSeries, mertensTransform, mul_comm]
  rw [heq] at h
  exact h


theorem finite_mertens_abel (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((n+1 : ℕ) : ℂ)^(-s) *
      (ArithmeticFunction.moebius (n+1) : ℂ)) =
    (∑ n ∈ Finset.range N, mellinFirst s (n+1) *
      (mertensPrefix (n+1) : ℂ)) +
      ((N+1 : ℕ) : ℂ)^(-s) * (mertensPrefix N : ℂ) := by
  simpa only [partialSum, mellinFirst, mertensPrefix,
    RiemannResearch.LinearAlgebra.CumulativeCellEnergy.cumulative,
    mobiusCoefficients, Complex.ofReal_sum, Complex.ofReal_intCast] using
    finite_abel (fun n => (n : ℂ)^(-s))
      (fun n => (ArithmeticFunction.moebius n : ℂ)) N

theorem mertens_abel_boundary_tendsto {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℂ)^(-s) *
      (mertensPrefix N : ℂ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hp : Tendsto (fun N : ℕ => ((N+1 : ℕ) : ℝ)^(1-s.re)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp hN
  apply squeeze_zero_norm _ hp
  intro N
  have hx : (0 : ℝ) < ((N+1 : ℕ) : ℝ) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hc : ‖((N+1 : ℕ) : ℂ)^(-s)‖ = ((N+1 : ℕ) : ℝ)^(-s.re) := by
    convert Complex.norm_cpow_eq_rpow_re_of_pos hx (-s) using 1 <;> simp
  rw [hc]
  calc
    _ ≤ ((N+1 : ℕ) : ℝ)^(-s.re) * ((N+1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left ((mertensPrefix_abs_le N).trans (by
        exact_mod_cast Nat.le_succ N)) (Real.rpow_nonneg hx.le _)
    _ = ((N+1 : ℕ) : ℝ)^(-s.re) * ((N+1 : ℕ) : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
    _ = ((N+1 : ℕ) : ℝ)^(-s.re + 1) := (Real.rpow_add hx _ _).symm
    _ = _ := by congr 1; ring


theorem mertensTransform_eq_inv_zeta (ε : ℝ) (hE : HasFiniteEnergy ε)
    {s : ℂ} (hs : 1 < s.re) (hmargin : 1/2+ε < s.re) :
    mertensTransform s = (riemannZeta s)⁻¹ := by
  let μ : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)
  have hL : Summable (LSeries.term μ s) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hLs := (summable_nat_add_iff 1).mpr hL
  have hshift : HasSum (fun n => LSeries.term μ s (n+1)) (LSeries μ s) := by
    have he : LSeries μ s = ∑' n : ℕ, LSeries.term μ s (n+1) := by
      rw [LSeries, hL.tsum_eq_zero_add, LSeries.term_zero, zero_add]
    rw [he]
    exact hLs.hasSum
  have hpartial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      ((n+1 : ℕ) : ℂ)^(-s) * (ArithmeticFunction.moebius (n+1) : ℂ))
      atTop (𝓝 (LSeries μ s)) := by
    convert hshift.tendsto_sum_nat using 1
    ext N
    apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
    exact mul_comm _ _
  have hright := ((mertensTransform_summable ε hE (by linarith) hmargin).hasSum.tendsto_sum_nat).add
    (mertens_abel_boundary_tendsto hs)
  have he := tendsto_nhds_unique hpartial
    (hright.congr' (Eventually.of_forall fun N => (finite_mertens_abel s N).symm))
  have hvalue : LSeries μ s = mertensTransform s := by
    simpa only [add_zero, mertensTransform] using he
  rw [← hvalue]
  apply mul_left_cancel₀ (riemannZeta_ne_zero_of_one_le_re hs.le)
  rw [mul_inv_cancel₀ (riemannZeta_ne_zero_of_one_le_re hs.le)]
  simpa only [LSeries_one_eq_riemannZeta hs, μ] using LSeries_one_mul_Lseries_moebius hs

/-- Conditional research reduction: all positive weighted Mertens energies
are finite. The energy premise is the remaining arithmetic obligation. -/
theorem riemannHypothesis_of_hasFiniteEnergy_forall
    (hE : ∀ ε : ℝ, 0 < ε → HasFiniteEnergy ε) : RiemannHypothesis := by
  apply PrimeTreeEuler.riemannHypothesis_iff_rootExtends.mpr
  refine ⟨mertensTransform, ?_, ?_⟩
  · intro s hs
    change (1/2 : ℝ) < s.re at hs
    let ε := (s.re - 1/2)/2
    have hε : 0 < ε := by dsimp [ε]; linarith
    exact mertensTransform_analyticOnNhd ε hε.le (hE ε hε) s
      (show 1/2+ε < s.re by dsimp [ε]; linarith)
  · intro s hs
    change Tendsto _ atTop (𝓝 (mertensTransform s))
    rw [mertensTransform_eq_inv_zeta (1/4) (hE _ (by norm_num)) hs (by linarith)]
    exact PrimeTreeEuler.tendsto_treeRoot hs

/-- Exact signed-energy criterion implies RH, with no analytic provider hypothesis. -/
theorem riemannHypothesis_of_bounded_offDiagonal_forall
    (h : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ N, offDiagonal ε N ≤ B) :
    RiemannHypothesis :=
  riemannHypothesis_of_hasFiniteEnergy_forall fun ε hε =>
    (hasFiniteEnergy_iff_bounded_offDiagonal ε hε).mpr (h ε hε)


theorem regularZetaRatio_mul_mertensTransform (ε : ℝ) (hε : 0 ≤ ε)
    (hε1 : ε < 1/2) (hE : HasFiniteEnergy ε)
    {s : ℂ} (hs : 1/2+ε < s.re) :
    RiemannResearch.RH.Burnol.regularZetaRatio s * mertensTransform s =
      (s-1)/s := by
  have h0 {z : ℂ} (hz : 1/2+ε < z.re) : z ≠ 0 := by
    intro he
    simp only [he, Complex.zero_re] at hz
    linarith
  have hl : AnalyticOnNhd ℂ
      (fun z => RiemannResearch.RH.Burnol.regularZetaRatio z * mertensTransform z)
      {z : ℂ | 1/2+ε < z.re} := by
    intro z hz
    exact (RiemannResearch.RH.Burnol.analyticAt_regularZetaRatio (h0 hz)).mul
      (mertensTransform_analyticOnNhd ε hε hE z hz)
  have hr : AnalyticOnNhd ℂ (fun z : ℂ => (z-1)/z)
      {z : ℂ | 1/2+ε < z.re} := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).div analyticAt_id (h0 hz)
  have ho : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have he : (fun z => RiemannResearch.RH.Burnol.regularZetaRatio z * mertensTransform z)
      =ᶠ[𝓝 (2 : ℂ)] (fun z : ℂ => (z-1)/z) := by
    filter_upwards [ho.mem_nhds (x := (2 : ℂ)) (by norm_num)] with z hz
    change 1 < z.re at hz
    have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz
    rw [RiemannResearch.RH.Burnol.regularZetaRatio_eq (by linarith) hz1,
      mertensTransform_eq_inv_zeta ε hE hz (by linarith),
      mul_assoc, mul_inv_cancel₀ (riemannZeta_ne_zero_of_one_le_re hz.le), mul_one]
  exact (hl.eqOn_of_preconnected_of_eventuallyEq hr
    (convex_halfSpace_re_gt (1/2+ε)).isPreconnected
    (z₀ := (2 : ℂ)) (by change 1/2+ε < (2 : ℂ).re; norm_num; linarith) he).eq_of_mem hs

/-- One finite damped energy excludes every zero strictly to its right. -/
theorem zeta_ne_zero_of_hasFiniteEnergy (ε : ℝ) (hε : 0 ≤ ε)
    (hE : HasFiniteEnergy ε) {s : ℂ}
    (hs : 1/2+ε < s.re) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  by_cases hε1 : ε < 1/2
  · intro hzeta
    have h := regularZetaRatio_mul_mertensTransform ε hε hε1 hE hs
    rw [RiemannResearch.RH.Burnol.regularZetaRatio_eq (by linarith) hs1,
      hzeta, mul_zero, zero_mul] at h
    have hs0 : s ≠ 0 := by intro he; simp only [he, Complex.zero_re] at hs; linarith
    exact (div_ne_zero (sub_ne_zero.mpr hs1) hs0) h.symm
  · exact riemannZeta_ne_zero_of_one_le_re (by linarith)

/-- The analytic reciprocal has a zero at the pole of zeta. -/
theorem mertensTransform_one_eq_zero (ε : ℝ) (hε : 0 ≤ ε)
    (hε1 : ε < 1 / 2) (hE : HasFiniteEnergy ε) :
    mertensTransform 1 = 0 := by
  simpa only [Burnol.regularZetaRatio_one, one_mul, sub_self, zero_div] using
    regularZetaRatio_mul_mertensTransform ε hε hε1 hE
      (s := 1) (by norm_num; linarith)

set_option backward.isDefEq.respectTransparency false in
/-- The reciprocal's zero at one is simple, with derivative exactly one. -/
theorem mertensTransform_hasDerivAt_one (ε : ℝ) (hε : 0 ≤ ε)
    (hε1 : ε < 1 / 2) (hE : HasFiniteEnergy ε) :
    HasDerivAt mertensTransform 1 1 := by
  have h1 : 1 / 2 + ε < (1 : ℂ).re := by norm_num; linarith
  have hF := (mertensTransform_analyticOnNhd ε hε hE 1 h1).differentiableAt.hasDerivAt
  have hR := (Burnol.analyticAt_regularZetaRatio (s := 1) one_ne_zero).differentiableAt.hasDerivAt
  have hp := hR.mul hF
  simp only [mertensTransform_one_eq_zero ε hε hε1 hE,
    Burnol.regularZetaRatio_one, mul_zero, one_mul, zero_add] at hp
  have heq : (fun z => Burnol.regularZetaRatio z * mertensTransform z)
      =ᶠ[𝓝 (1 : ℂ)] (fun z : ℂ => (z-1)/z) := by
    have ho : IsOpen {z : ℂ | 1 / 2 + ε < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds h1] with z hz
    exact regularZetaRatio_mul_mertensTransform ε hε hε1 hE hz
  have hr : HasDerivAt (fun z : ℂ => (z-1)/z) 1 1 := by
    convert! ((hasDerivAt_id (1 : ℂ)).sub_const 1).fun_div
      (hasDerivAt_id (1 : ℂ)) one_ne_zero using 1 <;> norm_num
  have hd : deriv mertensTransform 1 = 1 :=
    (hp.congr_of_eventuallyEq heq.symm).unique hr
  rw [hd] at hF
  exact hF

/-- The actual Mertens series equals the reciprocal throughout the energy
half-plane away from the pole. -/
theorem mertensTransform_eq_inv_zeta_of_hasFiniteEnergy (ε : ℝ) (hε : 0 ≤ ε)
    (hE : HasFiniteEnergy ε) {s : ℂ}
    (hs : 1 / 2 + ε < s.re) (hs1 : s ≠ 1) :
    mertensTransform s = (riemannZeta s)⁻¹ := by
  by_cases hε1 : ε < 1 / 2
  · have hs0 : s ≠ 0 := by
      intro he
      simp only [he, Complex.zero_re] at hs
      linarith
    have h := regularZetaRatio_mul_mertensTransform ε hε hε1 hE hs
    rw [Burnol.regularZetaRatio_eq (by linarith) hs1, mul_assoc] at h
    have hp : riemannZeta s * mertensTransform s = 1 :=
      mul_left_cancel₀ (div_ne_zero (sub_ne_zero.mpr hs1) hs0)
        (h.trans (mul_one _).symm)
    apply mul_left_cancel₀ (zeta_ne_zero_of_hasFiniteEnergy ε hε hE hs hs1)
    rw [mul_inv_cancel₀ (zeta_ne_zero_of_hasFiniteEnergy ε hε hE hs hs1)]
    exact hp
  · exact mertensTransform_eq_inv_zeta ε hE (by linarith) hs

theorem not_hasFiniteEnergy_of_zero (ε : ℝ) (hε : 0 ≤ ε)
    {s : ℂ} (hs : 1/2+ε < s.re) (hs1 : s ≠ 1) (hzero : riemannZeta s = 0) :
    ¬ HasFiniteEnergy ε := by
  intro hE
  exact zeta_ne_zero_of_hasFiniteEnergy ε hε hE hs hs1 hzero

theorem finiteEnergy_tendsto_atTop_of_zero (ε : ℝ) (hε : 0 ≤ ε)
    {s : ℂ} (hs : 1/2+ε < s.re) (hs1 : s ≠ 1) (hzero : riemannZeta s = 0) :
    Tendsto (finiteEnergy ε) atTop atTop := by
  have hu : ¬ ∃ A : ℝ, ∀ N, finiteEnergy ε N ≤ A := by
    rw [← hasFiniteEnergy_iff_bounded_finiteEnergy]
    exact not_hasFiniteEnergy_of_zero ε hε hs hs1 hzero
  push_neg at hu
  apply tendsto_atTop.mpr
  intro A
  obtain ⟨N, hN⟩ := hu A
  exact eventually_atTop.mpr ⟨N, fun n hn => hN.le.trans (finiteEnergy_monotone ε hn)⟩

/-- The signed cross term, not only total energy, diverges above every bound
if a zero lies strictly beyond the damping line. -/
theorem offDiagonal_tendsto_atTop_of_zero (ε : ℝ) (hε : 0 < ε)
    {s : ℂ} (hs : 1/2+ε < s.re) (hs1 : s ≠ 1) (hzero : riemannZeta s = 0) :
    Tendsto (offDiagonal ε) atTop atTop := by
  let D : ℝ := ∑' n : ℕ, ((n : ℝ)+1)^(-1-2*ε)
  have hlim := finiteEnergy_tendsto_atTop_of_zero ε hε.le hs hs1 hzero
  apply tendsto_atTop.mpr
  intro A
  filter_upwards [hlim.eventually (eventually_ge_atTop (A+D))] with N hN
  have hid := finiteEnergy_identity ε N
  have hd : diagonal ε N ≤ D := diagonal_le_pseries ε hε N
  linarith


/-- A single sequence of damping exponents approaching zero suffices. -/
theorem riemannHypothesis_of_energy_along_damping
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hE : ∀ j, HasFiniteEnergy (ε j)) : RiemannHypothesis := by
  apply riemannHypothesis_of_hasFiniteEnergy_forall
  intro δ hδ
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  exact hasFiniteEnergy_mono hj.le (hE j)

/-- Conditional research reduction with a countable damping schedule and
only frequently bounded signed sums at each damping. -/
theorem riemannHypothesis_of_frequently_bounded_offDiagonal_along_damping
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (hlim : Tendsto ε atTop (𝓝 0))
    (h : ∀ j, ∃ B : ℝ, ∃ᶠ N : ℕ in atTop, offDiagonal (ε j) N ≤ B) :
    RiemannHypothesis :=
  riemannHypothesis_of_energy_along_damping ε hlim fun j =>
    (hasFiniteEnergy_iff_frequently_bounded_offDiagonal (ε j) (hε j)).mpr (h j)

end RiemannResearch.RH.MertensWeightedEnergy
