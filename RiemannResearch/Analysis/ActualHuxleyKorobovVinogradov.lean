/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualSelbergDensityAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Critical exponential weight on the far strip

Huxley, *On the difference between consecutive primes*, Invent. Math. 15
(1972), 164–170, supplies the uniform density bound. Cook, *On the occurrence
of large gaps between prime numbers*, Lemma 3, writes its logarithm as the
44th power, uniformly from three quarters to one.

Bellotti, *Explicit bounds for the Riemann zeta function and a new zero-free
region*, J. Math. Anal. Appl. 536 (2024), 128249, gives the asymptotic
Vinogradov–Korobov constant 48.0718. We use the eventual positive-ordinate
count formulation. The zero-free width decreases for sufficiently large
ordinates and tends to zero, so the finitely many lower zeros are absorbed
in the height threshold.

With these two classical inputs, every fixed displacement strictly above
one third has weighted mass saving every power of log T at the exact
weight exp(2 log T · displacement).
-/

noncomputable section
open Filter MeasureTheory Set Zeta23

namespace RiemannResearch.Analysis.ActualZeroOrdinate

def HuxleyDensityHypothesis : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc (3 / 4 : ℝ) 1,
    rightInclusiveCount T σ ≤
      C * T ^ (3 * (1 - σ) / (3 * σ - 1)) * (Real.log T) ^ (44 : ℝ)

/-- Bellotti's asymptotic boundary, in the inclusive count convention. -/
def BellottiKorobovVinogradovCount : Prop :=
  ∀ᶠ T : ℝ in atTop, rightInclusiveCount T
    (1 - 1 / ((240359 / 5000 : ℝ) * (Real.log T) ^ (2 / 3 : ℝ) *
      (Real.log (Real.log T)) ^ (1 / 3 : ℝ))) = 0

/-- The moving boundary in Bellotti's published asymptotic theorem. -/
def bellottiAbscissa (T : ℝ) : ℝ :=
  1 - 1 / ((240359 / 5000 : ℝ) * (Real.log T) ^ (2 / 3 : ℝ) *
    (Real.log (Real.log T)) ^ (1 / 3 : ℝ))

/-- The source theorem above large positive ordinates. -/
def BellottiKorobovVinogradovNonvanishing : Prop :=
  ∀ᶠ t : ℝ in atTop, ∀ s : ℂ, s.im = t → bellottiAbscissa t ≤ s.re → riemannZeta s ≠ 0

private theorem bellottiAbscissa_mono :
    MonotoneOn bellottiAbscissa (Ici (Real.exp (Real.exp 1))) := by
  intro x hx y hy hxy
  have hx₀ := (Real.exp_pos _).trans_le hx
  have hLx : Real.exp 1 ≤ Real.log x := by simpa using Real.log_le_log (Real.exp_pos _) hx
  have hLxp := (Real.exp_pos _).trans_le hLx
  have hll : 1 ≤ Real.log (Real.log x) := by simpa using Real.log_le_log (Real.exp_pos _) hLx
  have hllp := zero_lt_one.trans_le hll
  have hLxy := Real.log_le_log hx₀ hxy
  have hLyp := hLxp.trans_le hLxy
  have hlxy := Real.log_le_log hLxp hLxy
  have hp := Real.rpow_le_rpow hLxp.le hLxy (show 0 ≤ (2 / 3 : ℝ) by norm_num)
  have hq := Real.rpow_le_rpow hllp.le hlxy (show 0 ≤ (1 / 3 : ℝ) by norm_num)
  have hd := mul_le_mul (mul_le_mul_of_nonneg_left hp (show 0 ≤ (240359 / 5000 : ℝ) by norm_num))
    hq (Real.rpow_nonneg hllp.le _) (by positivity)
  unfold bellottiAbscissa
  apply sub_le_sub_left
  exact one_div_le_one_div_of_le (by positivity) hd

theorem tendsto_bellottiAbscissa : Tendsto bellottiAbscissa atTop (nhds 1) := by
  let f (T : ℝ) := (240359 / 5000 : ℝ) * (Real.log T) ^ (2 / 3 : ℝ)
  let g (T : ℝ) := f T * (Real.log (Real.log T)) ^ (1 / 3 : ℝ)
  have hf : Tendsto f atTop atTop :=
    ((tendsto_rpow_atTop (show 0 < (2 / 3 : ℝ) by norm_num)).comp Real.tendsto_log_atTop).const_mul_atTop
      (by norm_num)
  have hll : Tendsto (fun T : ℝ => Real.log (Real.log T)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hg : Tendsto g atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hf
    filter_upwards [hll.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 0]
      with T hT hL
    exact le_mul_of_one_le_right (by dsimp [f]; positivity)
      (Real.one_le_rpow hT (by norm_num))
  have hw : Tendsto (fun T : ℝ => 1 / g T) atTop (nhds 0) := tendsto_const_nhds.div_atTop hg
  change Tendsto (fun T : ℝ => 1 - 1 / g T) atTop (nhds 1)
  simpa only [sub_zero] using
    (show Tendsto (fun T : ℝ => 1 - 1 / g T) atTop (nhds ((1 : ℝ) - 0)) from
      tendsto_const_nhds.sub hw)

/-- Pointwise high-ordinate nonvanishing gives the actual inclusive count
at height T. A finite lower cutoff handles all zeros below the source's
threshold; eventual monotonicity handles the remaining ordinates. -/
theorem bellotti_count_of_nonvanishing (h : BellottiKorobovVinogradovNonvanishing) :
    BellottiKorobovVinogradovCount := by
  classical
  obtain ⟨H, hH⟩ := eventually_atTop.1 h
  let U := max H (Real.exp (Real.exp 1))
  have hsmall : ∀ᶠ T : ℝ in atTop, ∀ ρ : {z // z ∈ cutoff U}, ρ.val.re < bellottiAbscissa T := by
    apply eventually_all.mpr
    intro ρ
    exact tendsto_bellottiAbscissa.eventually (Ioi_mem_nhds (mem_cutoff.mp ρ.property).1.2.2)
  change ∀ᶠ T : ℝ in atTop, rightInclusiveCount T (bellottiAbscissa T) = 0
  filter_upwards [hsmall, eventually_ge_atTop U] with T hs hT
  unfold rightInclusiveCount realSum
  apply Finset.sum_eq_zero
  intro ρ hρ
  obtain ⟨hz, him, himT⟩ := mem_cutoff.mp hρ
  have hβ : ¬ bellottiAbscissa T ≤ ρ.re := by
    by_cases hu : ρ.im ≤ U
    · exact not_le.mpr (hs ⟨ρ, mem_cutoff.mpr ⟨hz, him, hu⟩⟩)
    · have hu' := (lt_of_not_ge hu).le
      have hm := bellottiAbscissa_mono ((le_max_right _ _).trans hu')
        ((le_max_right _ _).trans hT) himT
      exact fun hβ => hH ρ.im ((le_max_left _ _).trans hu') ρ rfl (hm.trans hβ) hz.1
  simp only [if_neg hβ, mul_zero]

/-- The VK width eventually exceeds every fixed multiple of log log T / log T. -/
theorem eventually_loglog_le_bellottiWidth (D : ℝ) (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop, D * Real.log (Real.log T) / Real.log T ≤ 1 - bellottiAbscissa T := by
  let R := (240359 / 5000 : ℝ)
  have hR : 0 < R := by norm_num [R]
  have he := (isLittleO_log_rpow_rpow_atTop (s := (1 / 3 : ℝ)) (4 / 3 : ℝ)
    (by norm_num)).bound (show 0 < 1 / (D * R) by positivity)
  have hl : ∀ᶠ T : ℝ in atTop, 1 < Real.log T := Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop 1)
  filter_upwards [hl, Real.tendsto_log_atTop.eventually he] with T hL hsmall
  let L := Real.log T
  let l := Real.log L
  have hLp : 0 < L := lt_trans zero_lt_one hL
  have hlp : 0 < l := Real.log_pos hL
  change ‖l ^ (4 / 3 : ℝ)‖ ≤ 1 / (D * R) * ‖L ^ (1 / 3 : ℝ)‖ at hsmall
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hlp _),
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hsmall
  have hs : (D * R) * l ^ (4 / 3 : ℝ) ≤ L ^ (1 / 3 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hD.le hR.le)
    calc
      _ ≤ _ := h
      _ = _ := by field_simp [hD.ne', hR.ne']
  have hwidth : D * l / L ≤ 1 / (R * L ^ (2 / 3 : ℝ) * l ^ (1 / 3 : ℝ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hLp).mpr
    calc
      _ = (D * R * l ^ (4 / 3 : ℝ)) * L ^ (2 / 3 : ℝ) := by
        rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hlp, Real.rpow_one]
        ring
      _ ≤ L ^ (1 / 3 : ℝ) * L ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hLp.le _)
      _ = 1 * L := by rw [← Real.rpow_add hLp]; norm_num
  simpa only [bellottiAbscissa, sub_sub_cancel] using hwidth

/-- At a moving abscissa D log log T / log T from one, the zero count is
eventually zero for every fixed positive D. -/
theorem eventually_no_zeros_in_loglog_strip (hv : BellottiKorobovVinogradovCount)
    (D : ℝ) (hD : 0 < D) :
    ∀ᶠ T : ℝ in atTop, rightInclusiveCount T
      (1 - D * Real.log (Real.log T) / Real.log T) = 0 := by
  filter_upwards [hv, eventually_loglog_le_bellottiWidth D hD] with T hzero hwidth
  have hc := rightInclusiveCount_antitone T (show bellottiAbscissa T ≤
    1 - D * Real.log (Real.log T) / Real.log T by linarith only [hwidth])
  change rightInclusiveCount T (bellottiAbscissa T) = 0 at hzero
  rw [hzero] at hc
  exact le_antisymm hc (rightInclusiveCount_nonneg _ _)

/-- The exponent in the uniform Huxley estimate is at most
(2 − κ)(1 − σ) once σ reaches σ₀ > 5/6. -/
theorem huxley_critical_weight_margin {σ₀ : ℝ} (h₀ : 5 / 6 < σ₀) :
    0 < 2 - 3 / (3 * σ₀ - 1) ∧ ∀ σ ∈ Icc σ₀ 1,
      3 * (1 - σ) / (3 * σ - 1) + 2 * (σ - 1 / 2) ≤
        1 - (2 - 3 / (3 * σ₀ - 1)) * (1 - σ) := by
  have hd₀ : 0 < 3 * σ₀ - 1 := by linarith
  constructor
  · exact sub_pos.mpr ((div_lt_iff₀ hd₀).mpr (by linarith))
  intro σ hσ
  have hd : 0 < 3 * σ - 1 := by linarith [hσ.1]
  have hratio : 3 / (3 * σ - 1) ≤ 3 / (3 * σ₀ - 1) := by
    apply (div_le_div_iff₀ hd hd₀).mpr
    linarith only [hσ.1]
  have hmul := mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr hσ.2)
  rw [div_mul_eq_mul_div] at hmul
  linarith only [hmul]

/-- Uniform weighted inclusive counts across the full far strip at b = 2.
The gain persists even when the abscissa moves with height. -/
theorem weighted_huxley_count_superlog (hH : HuxleyDensityHypothesis)
    (hv : BellottiKorobovVinogradovCount) {σ₀ : ℝ} (h₀ : 5 / 6 < σ₀)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc σ₀ 1,
      rightInclusiveCount T σ * T ^ (2 * (σ - 1 / 2)) ≤ C * (T * (Real.log T) ^ (-A)) := by
  obtain ⟨C, hC, hcount⟩ := hH
  let κ := 2 - 3 / (3 * σ₀ - 1)
  have hκ : 0 < κ := (huxley_critical_weight_margin h₀).1
  let D := (44 + A) / κ
  have hD : 0 < D := div_pos (by linarith) hκ
  have hκD : κ * D = 44 + A := by dsimp [D]; field_simp [hκ.ne']
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcount, eventually_no_zeros_in_loglog_strip hv D hD,
    eventually_gt_atTop (Real.exp 1)] with T hc hzero hT
  let L := Real.log T
  let l := Real.log L
  have hTp : 0 < T := (Real.exp_pos _).trans hT
  have hL : 1 < L := by simpa [L] using Real.log_lt_log (Real.exp_pos _) hT
  have hLp : 0 < L := lt_trans zero_lt_one hL
  intro σ hσ
  by_cases hz : 1 - D * l / L ≤ σ
  · have hz' := rightInclusiveCount_antitone T hz
    change rightInclusiveCount T (1 - D * l / L) = 0 at hzero
    rw [hzero] at hz'
    rw [le_antisymm hz' (rightInclusiveCount_nonneg _ _), zero_mul]
    positivity
  have hdist : D * l ≤ (1 - σ) * L := by
    apply (div_le_iff₀ hLp).mp
    linarith only [lt_of_not_ge hz]
  have hs := mul_le_mul_of_nonneg_left hdist hκ.le
  rw [← mul_assoc, hκD] at hs
  have hexp := mul_le_mul_of_nonneg_left ((huxley_critical_weight_margin h₀).2 σ hσ) hLp.le
  let E := 3 * (1 - σ) / (3 * σ - 1)
  have hexp' : L * E + l * 44 + L * (2 * (σ - 1 / 2)) ≤ L + l * (-A) := by
    change L * (E + 2 * (σ - 1 / 2)) ≤ L * (1 - κ * (1 - σ)) at hexp
    linarith only [hs, hexp]
  have hb := hc σ ⟨by linarith only [h₀, hσ.1], hσ.2⟩
  calc
    _ ≤ (C * T ^ E * L ^ (44 : ℝ)) * T ^ (2 * (σ - 1 / 2)) :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hTp.le _)
    _ = C * Real.exp (L * E + l * 44 + L * (2 * (σ - 1 / 2))) := by
      rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos hTp,
        Real.rpow_def_of_pos hLp, Real.rpow_def_of_pos hTp]
      ring
    _ ≤ C * Real.exp (L + l * (-A)) := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hexp') hC.le
    _ = _ := by rw [Real.exp_add, Real.rpow_def_of_pos hLp, Real.exp_log hTp]

/-- A uniform budget for critical weighted inclusive counts transfers to
the normalized mass of all exceptional copies. The constant is independent
of the cutoff and budget. -/
theorem normalized_critical_weight_of_count {T δ K : ℝ} (hδ : δ ∈ Icc (0 : ℝ) (1 / 2))
    (hT : Real.exp 1 ≤ T) (hK : 0 ≤ K)
    (hN : (1 / (16 * Real.pi)) * T * Real.log T ≤ (Ncount 0 T : ℝ))
    (hcount : ∀ σ ∈ Icc (1 / 2 + δ) 1,
      rightInclusiveCount T σ * T ^ (2 * (σ - 1 / 2)) ≤ K * T) :
    badWeightedSum T δ (fun t => Real.exp (2 * Real.log T * t)) / (Ncount 0 T : ℝ) ≤
      64 * Real.pi * K := by
  have hTp := (Real.exp_pos _).trans_le hT
  let L := Real.log T
  have hL : 1 ≤ L := by simpa [L] using Real.log_le_log (Real.exp_pos _) hT
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have ht : ∀ t ∈ Icc δ (1 / 2), strictTail T t * Real.exp (2 * L * t) ≤ 2 * K * T := by
    intro t ht
    have hσ : 1 / 2 + t ∈ Icc (1 / 2 + δ) (1 : ℝ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hc := hcount _ hσ
    rw [show 1 / 2 + t - 1 / 2 = t by ring, Real.rpow_def_of_pos hTp] at hc
    have h := mul_le_mul_of_nonneg_right (strictTail_le_twice_inclusive T t (hδ.1.trans ht.1))
      (Real.exp_pos (2 * L * t)).le
    have he : 2 * L * t = Real.log T * (2 * t) := by dsimp [L]; ring
    rw [he] at h ⊢
    linarith only [h, hc]
  have hint : (∫ t in δ..(1 / 2 : ℝ), strictTail T t * (2 * L * Real.exp (2 * L * t))) ≤
      ∫ _ in δ..(1 / 2 : ℝ), 2 * L * (2 * K * T) := by
    apply intervalIntegral.integral_mono_on hδ.2
      (FiniteStrictTail.intervalIntegrable_tail_mul _ _ _ (by fun_prop) _ _)
      intervalIntegrable_const
    intro t ht'
    calc
      _ = 2 * L * (strictTail T t * Real.exp (2 * L * t)) := by
        change strictTail T t * (2 * L * Real.exp (2 * L * t)) = _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (ht t ht') (by positivity)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hleft := ht δ ⟨le_rfl, hδ.2⟩
  have hNpos : 0 < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hN
  apply (div_le_iff₀ hNpos).mpr
  change badWeightedSum T δ (fun t => Real.exp (2 * L * t)) ≤ _
  rw [badExp_layerCake T δ (2 * L) hδ.2]
  have hleft' : 2 * K * T ≤ 2 * K * T * L :=
    le_mul_of_one_le_right (by positivity) hL
  have hdrop := mul_nonneg hδ.1 (show 0 ≤ 2 * L * (2 * K * T) by positivity)
  calc
    _ ≤ 4 * K * T * L := by linarith only [hint, hleft, hleft', hdrop]
    _ = (64 * Real.pi * K) * ((1 / (16 * Real.pi)) * T * L) := by
      field_simp [Real.pi_ne_zero]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (by positivity)

/-- The full normalized exponential mass saves every prescribed log power. -/
theorem normalized_critical_weight_superlog_of_huxley
    (hH : HuxleyDensityHypothesis) (hv : BellottiKorobovVinogradovCount)
    {δ : ℝ} (hδ : δ ∈ Ioc (1 / 3 : ℝ) (1 / 2)) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      badWeightedSum T δ (fun t => Real.exp (2 * Real.log T * t)) / (Ncount 0 T : ℝ) ≤
        C * (Real.log T) ^ (-A) := by
  obtain ⟨C, hC, hh⟩ := weighted_huxley_count_superlog hH hv
    (σ₀ := 1 / 2 + δ) (by linarith only [hδ.1]) A hA
  refine ⟨64 * Real.pi * C, by positivity, ?_⟩
  filter_upwards [hh, eventually_count_ge_log, eventually_ge_atTop (Real.exp 1)] with T hT hN hE
  have hL : 0 < Real.log T := lt_of_lt_of_le zero_lt_one
    (by simpa using Real.log_le_log (Real.exp_pos _) hE)
  have h := normalized_critical_weight_of_count (δ := δ) ⟨by linarith only [hδ.1], hδ.2⟩
    hE (show 0 ≤ C * (Real.log T) ^ (-A) by positivity) hN
    (fun σ hσ => by simpa only [mul_assoc, mul_comm T] using hT σ hσ)
  simpa only [mul_assoc] using h

/-- The full Vinogradov–Korobov width gives a stretched exponential saving.
Keeping the stated logarithm makes the direct Huxley estimate transparent. -/
theorem weighted_huxley_count_vkDecay (hH : HuxleyDensityHypothesis)
    (hv : BellottiKorobovVinogradovCount) {σ₀ : ℝ} (h₀ : 5 / 6 < σ₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc σ₀ 1,
      rightInclusiveCount T σ * T ^ (2 * (σ - 1 / 2)) ≤
        C * ((Real.log T) ^ (44 : ℝ) * Real.exp (-(2 - 3 / (3 * σ₀ - 1)) *
          (1 - bellottiAbscissa T) * Real.log T)) * T := by
  obtain ⟨C, hC, hh⟩ := hH
  refine ⟨C, hC, ?_⟩
  filter_upwards [hh, hv, eventually_gt_atTop (Real.exp 1)] with T hcount hzero hT
  have hTp := (Real.exp_pos _).trans hT
  have hL : 0 < Real.log T := zero_lt_one.trans
    (by simpa using Real.log_lt_log (Real.exp_pos _) hT)
  let κ := 2 - 3 / (3 * σ₀ - 1)
  have hκ : 0 < κ := (huxley_critical_weight_margin h₀).1
  intro σ hσ
  by_cases hz : bellottiAbscissa T ≤ σ
  · have hz' := rightInclusiveCount_antitone T hz
    change rightInclusiveCount T (bellottiAbscissa T) = 0 at hzero
    rw [hzero] at hz'
    rw [le_antisymm hz' (rightInclusiveCount_nonneg _ _), zero_mul]
    positivity
  have hd := mul_le_mul_of_nonneg_left (sub_le_sub_left (le_of_not_ge hz) 1) hκ.le
  have hmargin := (huxley_critical_weight_margin h₀).2 σ hσ
  let E := 3 * (1 - σ) / (3 * σ - 1)
  have he : E + 2 * (σ - 1 / 2) ≤ 1 - κ * (1 - bellottiAbscissa T) :=
    hmargin.trans (sub_le_sub_left hd 1)
  have h := hcount σ ⟨by linarith only [h₀, hσ.1], hσ.2⟩
  calc
    _ ≤ (C * T ^ E * (Real.log T) ^ (44 : ℝ)) * T ^ (2 * (σ - 1 / 2)) :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hTp.le _)
    _ = (C * (Real.log T) ^ (44 : ℝ)) * T ^ (E + 2 * (σ - 1 / 2)) := by
      rw [Real.rpow_add hTp]; ring
    _ ≤ (C * (Real.log T) ^ (44 : ℝ)) * T ^ (1 - κ * (1 - bellottiAbscissa T)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
        ((Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hT.le) he) (by positivity)
    _ = _ := by
      rw [Real.rpow_def_of_pos hTp,
        show Real.log T * (1 - κ * (1 - bellottiAbscissa T)) =
          Real.log T + -κ * (1 - bellottiAbscissa T) * Real.log T by ring,
        Real.exp_add, Real.exp_log hTp]
      ring

/-- A source-level theorem for the normalized b = 2 weighted mass retaining
the stretched exponential and the original analytic multiplicities. -/
theorem normalized_critical_weight_vkDecay (hH : HuxleyDensityHypothesis)
    (hv : BellottiKorobovVinogradovNonvanishing) {δ : ℝ} (hδ : δ ∈ Ioc (1 / 3 : ℝ) (1 / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      badWeightedSum T δ (fun t => Real.exp (2 * Real.log T * t)) / (Ncount 0 T : ℝ) ≤
        C * ((Real.log T) ^ (44 : ℝ) * Real.exp (-(2 - 3 / (3 * (1 / 2 + δ) - 1)) *
          (1 - bellottiAbscissa T) * Real.log T)) := by
  obtain ⟨C, hC, hh⟩ := weighted_huxley_count_vkDecay hH (bellotti_count_of_nonvanishing hv)
    (σ₀ := 1 / 2 + δ) (by linarith only [hδ.1])
  refine ⟨64 * Real.pi * C, by positivity, ?_⟩
  filter_upwards [hh, eventually_count_ge_log, eventually_ge_atTop (Real.exp 1)] with T hT hN hE
  have hL : 0 < Real.log T := lt_of_lt_of_le zero_lt_one
    (by simpa using Real.log_le_log (Real.exp_pos _) hE)
  have h := normalized_critical_weight_of_count (δ := δ) ⟨by linarith only [hδ.1], hδ.2⟩
    hE (show 0 ≤ C * ((Real.log T) ^ (44 : ℝ) * Real.exp (-(2 - 3 / (3 * (1 / 2 + δ) - 1)) *
      (1 - bellottiAbscissa T) * Real.log T)) by positivity) hN hT
  simpa only [mul_assoc] using h

end RiemannResearch.Analysis.ActualZeroOrdinate
