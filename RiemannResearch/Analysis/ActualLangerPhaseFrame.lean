/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualDistinctOrdinateProportion
import RiemannResearch.Analysis.ActualZeroPhaseMoments
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Langer zero counting and actual finite phase frames

R. E. Langer, *On the zeros of exponential sums and integrals*, Bull. Amer.
Math. Soc. 37 (1931), 213–239, DOI 10.1090/S0002-9904-1931-05133-8. The zero-count remainder for an exponential
sum with n+1 real frequencies is at most n; see also Heittokangas et al.,
Bull. London Math. Soc. 55 (2023), §2.3, DOI 10.1112/blms.12719.
Nazarov, Algebra i Analiz 5 (1993), no. 4, Lemma 1.3, uses an open vertical
strip. Rotation, removal of zero coefficients and translation of the
frequencies give the real-zero specialization for frequencies log(1),…,log(d)
used here. The remainder d−1 and frequency span log d are uniform in the
complex coefficients, even when some coefficients vanish.

The actual Gram weights every analytic copy. Its kernel is determined by
distinct ordinates: each contributes a squared absolute value and each
actual distinct zero has positive multiplicity. This gives polynomial
dimension invertibility and imposes no quantitative lower eigenvalue.
-/

noncomputable section
open Filter Complex Set Zeta23
open scoped BigOperators InnerProductSpace ComplexConjugate Topology

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate HorizontalEuclideanMoments

/-- The finite Dirichlet exponential sum of frequencies log(1),…,log(d). -/
def langerSum (d : ℕ) (w : Fin d → ℂ) (t : ℝ) : ℂ :=
  ∑ i : Fin d, w i * Complex.exp (((t * Real.log ((i.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) * I)

/-- Real distinct zeros inside the open rectangle covered by Langer's
zero-count theorem. There is no zeta-zero or Gram assumption in this input. -/
def LangerOpenIntervalZeroCount : Prop :=
  ∀ (d : ℕ) (w : Fin d → ℂ), (∃ i : Fin d, w i ≠ 0) →
    ∀ (a b : ℝ), a < b → ∀ s : Finset ℝ,
      (∀ t ∈ s, t ∈ Ioo a b) → (∀ t ∈ s, langerSum d w t = 0) →
        (s.card : ℝ) ≤ (d : ℝ) - 1 + (b-a)*Real.log (d : ℝ)/(2*Real.pi)

/-- Increasing the open upper endpoint and taking the limit preserves
the exact constant for the repository's positive half-open height convention. -/
theorem LangerOpenIntervalZeroCount.half_open (hL : LangerOpenIntervalZeroCount)
    (d : ℕ) (w : Fin d → ℂ) (hw : ∃ i : Fin d, w i ≠ 0) (T : ℝ) (hT : 0 ≤ T)
    (s : Finset ℝ) (hs : ∀ t ∈ s, t ∈ Ioc 0 T)
    (hz : ∀ t ∈ s, langerSum d w t = 0) :
    (s.card : ℝ) ≤ (d : ℝ)-1+T*Real.log (d : ℝ)/(2*Real.pi) := by
  let f := fun u : ℝ => (d : ℝ)-1+(T+u)*Real.log (d : ℝ)/(2*Real.pi)
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
    (show Continuous f by dsimp [f]; fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u := self_mem_nhdsWithin
  have h := ge_of_tendsto hlim (by
    filter_upwards [hpos] with u hu
    have hab : 0 < T+u := add_pos_of_nonneg_of_pos hT hu
    simpa only [f, sub_zero] using hL d w hw 0 (T+u) hab s
      (fun t ht => ⟨(hs t ht).1, (hs t ht).2.trans_lt (lt_add_of_pos_right _ hu)⟩) hz)
  simpa only [f, add_zero] using h

private theorem langerSum_eq_inner (d : ℕ) (x : Space d) (ρ : ℂ) :
    langerSum d (fun i => conj (x i)) ρ.im = inner ℂ x (copyPhaseVector d ρ) := by
  rw [PiLp.inner_apply]
  simp only [langerSum, copyPhaseVector, WithLp.ofLp_toLp, RCLike.inner_apply']

/-- Every sampled phase evaluation vanishes separately on a Gram kernel vector. -/
theorem phaseGram_kernel_zero_on_ordinates (T : ℝ) (d : ℕ) (hN : 0 < Ncount 0 T)
    (x : Space d) (hx : phaseGram T d x = 0) (t : ℝ) (ht : t ∈ distinctOrdinates T) :
    langerSum d (fun i => conj (x i)) t = 0 := by
  classical
  let v := fun c : Copies T => copyPhaseVector d c.1.1
  have hzero : (∑ c : Copies T, (InnerProductSpace.rankOne ℂ (v c) (v c)) x) = 0 := by
    have hn : (Ncount 0 T : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hN.ne')
    simpa only [phaseGram, copyGram, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply, smul_eq_zero, hn, false_or, v] using hx
  have hsum : (∑ c : Copies T, Complex.normSq (inner ℂ x (v c))) = 0 := by
    have hp := congrArg (fun y : Space d => (inner ℂ x y).re) hzero
    simp only [inner_sum, InnerProductSpace.inner_right_rankOne_apply, inner_zero_right,
      Complex.zero_re, Complex.re_sum] at hp
    convert hp using 1
    apply Finset.sum_congr rfl
    intro c _
    rw [← inner_conj_symm (v c) x, Complex.mul_conj, Complex.ofReal_re]
  obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp ht
  let c : Copies T := ⟨⟨ρ,hρ⟩, ⟨0,multiplicity_pos hρ⟩⟩
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Copies T))) => Complex.normSq_nonneg _)).mp hsum c (Finset.mem_univ c)
  exact (langerSum_eq_inner d x ρ).trans (Complex.normSq_eq_zero.mp hz)

/-- Count-only strict invertibility. A nonzero null vector would produce
a nonzero exponential sum vanishing at too many distinct ordinates. -/
theorem phaseGram_isUnit_of_langer_count (hL : LangerOpenIntervalZeroCount)
    (T : ℝ) (d : ℕ) (hT : 0 ≤ T) (hN : 0 < Ncount 0 T)
    (hcount : (d : ℝ)-1+T*Real.log (d : ℝ)/(2*Real.pi) < ((distinctOrdinates T).card : ℝ)) :
    IsUnit (phaseGram T d) := by
  classical
  let G := (phaseGram T d).toLinearMap
  have hker : G.ker = ⊥ := LinearMap.ker_eq_bot'.mpr (by
    intro x hx
    by_contra hne
    have hw : ∃ i : Fin d, conj (x i) ≠ 0 := by
      by_contra! hall
      apply hne
      ext i
      change x i = 0
      simpa only [map_eq_zero] using hall i
    have hs : ∀ t ∈ distinctOrdinates T, t ∈ Ioc 0 T := by
      intro t ht
      obtain ⟨ρ,hρ,rfl⟩ := Finset.mem_image.mp ht
      exact (mem_cutoff.mp hρ).2
    exact hcount.not_ge (hL.half_open d _ hw T hT _ hs
      (fun t ht => phaseGram_kernel_zero_on_ordinates T d hN x hx t ht)))
  have hinj : Function.Injective G := LinearMap.ker_eq_bot.mp hker
  let e := (LinearEquiv.ofBijective G ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv
  exact ⟨e.toUnit, rfl⟩

/-- If a proportion κ of all copies have distinct ordinates, every support
growth d ≤ Tᵇ with 0 ≤ b < κ ≤ 1 yields eventual invertibility. -/
theorem phaseGram_eventually_isUnit_of_ordinate_proportion (hL : LangerOpenIntervalZeroCount)
    {κ b : ℝ} (hκ : CumulativeDistinctOrdinateProportion κ) (hb : 0 ≤ b)
    (hbκ : b < κ) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ T^b → IsUnit (phaseGram T d) := by
  let B : ℝ := 1/(2*Real.pi)
  have hB : 0 < B := by dsimp [B]; positivity
  let k := (κ+b)/2
  have hbk : b < k := by dsimp [k]; linarith only [hbκ]
  have hkκ : k < κ := by dsimp [k]; linarith only [hbκ]
  have hk : 0 < k := hb.trans_lt hbk
  let q := (B+b*B/k)/2
  have hqB : q < B := by
    have h : b*B/k < B := (div_lt_iff₀ hk).mpr (by nlinarith only [mul_lt_mul_of_pos_right hbk hB])
    dsimp [q]; linarith only [h]
  have hgap : 0 < k*q-b*B := by
    have he : k*q = (k*B+b*B)/2 := by dsimp [q]; field_simp [hk.ne']
    rw [he]; nlinarith only [mul_lt_mul_of_pos_right hbk hB]
  obtain ⟨H,hH⟩ := hκ (κ-k) (sub_pos.mpr hkκ)
  have hLlarge := Real.tendsto_log_atTop.eventually_gt_atTop ((k*q-b*B)⁻¹)
  filter_upwards [eventually_ge_atTop H,eventually_count_ge_log_of_lt hqB,eventually_count_pos,
      eventually_gt_atTop (1 : ℝ), hLlarge] with T hTH hN hNpos hT hlog d hd hdT
  have hTp := zero_lt_one.trans hT
  have hdp : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d from hd)
  have hlogd : Real.log (d : ℝ) ≤ b*Real.log T := by
    simpa only [Real.log_rpow hTp] using Real.log_le_log hdp hdT
  have hdlin : (d : ℝ) ≤ T := hdT.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT.le (hbκ.le.trans hκ.le_one))
  have hmass := (mul_le_mul_of_nonneg_left hN hk.le).trans
    (show k*(Ncount 0 T : ℝ) ≤ ((distinctOrdinates T).card : ℝ) by
      simpa only [sub_sub_cancel] using hH T hTH)
  have hL1 : 1 < (k*q-b*B)*Real.log T := by
    have hh := mul_lt_mul_of_pos_left hlog hgap
    simpa only [mul_inv_cancel₀ hgap.ne'] using hh
  have hgapT := mul_lt_mul_of_pos_left hL1 hTp
  have hfreq := mul_le_mul_of_nonneg_left hlogd (mul_nonneg hTp.le hB.le)
  apply phaseGram_isUnit_of_langer_count hL T d hTp.le hNpos
  apply lt_of_lt_of_le _ hmass
  change (d : ℝ)-1+T*Real.log (d : ℝ)/(2*Real.pi) < k*(q*T*Real.log T)
  rw [show T*Real.log (d : ℝ)/(2*Real.pi) = (T*B)*Real.log (d : ℝ) by dsimp [B]; ring]
  nlinarith only [hgapT, hfreq, hdlin]

theorem phaseGram_eventually_isUnit_of_distinctCritical (hL : LangerOpenIntervalZeroCount)
    {κ b : ℝ} (hκ : CumulativeDistinctCriticalProportion κ) (hb : 0 ≤ b)
    (hbκ : b < κ) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ T^b → IsUnit (phaseGram T d) :=
  phaseGram_eventually_isUnit_of_ordinate_proportion hL hκ.distinct_ordinates hb hbκ


/-- The proved Montgomery–Taylor cumulative proportion is available directly. -/
theorem phaseGram_eventually_isUnit_montgomeryTaylor (hL : LangerOpenIntervalZeroCount)
    {b : ℝ} (hb : 0 ≤ b) (hbk : b < ThmD.HD 1) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ T^b → IsUnit (phaseGram T d) :=
  phaseGram_eventually_isUnit_of_distinctCritical hL montgomeryTaylor_distinctCriticalProportion hb hbk

/-- The external ten-point cumulative distinct-on-line record supplies its
exact rational value to the same frame theorem. -/
theorem phaseGram_eventually_isUnit_tenPoint (hL : LangerOpenIntervalZeroCount)
    (hκ : CumulativeDistinctCriticalProportion tenPointCriticalFraction)
    {b : ℝ} (hb : 0 ≤ b) (hbk : b < tenPointCriticalFraction) :
    ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ T^b → IsUnit (phaseGram T d) :=
  phaseGram_eventually_isUnit_of_distinctCritical hL hκ hb hbk

end RiemannResearch.Analysis.ActualZeroPhaseMoments
