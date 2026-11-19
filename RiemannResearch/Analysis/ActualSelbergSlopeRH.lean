/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.ActualSelbergDensityAssembly
import RiemannResearch.Analysis.ActualZeroSublinearEnergy
import RiemannResearch.RH.HorizontalEnergyCriterion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Uniform density slopes and the support of the actual zeros

An actual zero contributes at least one occurrence in each subsequent inclusive
count. A bound with negative height exponent, even with an arbitrary fixed
real power of log T, eventually falls below one. This gives the support
radius 1/a and a cofinal-slope characterization of Mathlib's Riemann hypothesis.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology ComplexConjugate

namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem one_le_rightInclusiveCount_of_mem {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ cutoff T) : 1 ≤ rightInclusiveCount T ρ.re := by
  unfold rightInclusiveCount realSum
  calc
    (1 : ℝ) ≤ (zeroMult ρ : ℝ) * (if ρ.re ≤ ρ.re then 1 else 0) := by
      simp only [le_refl, if_true, mul_one]
      exact_mod_cast multiplicity_pos hρ
    _ ≤ _ := Finset.single_le_sum
      (f := fun z : ℂ => (zeroMult z : ℝ) * (if ρ.re ≤ z.re then 1 else 0))
      (fun z _ => mul_nonneg (Nat.cast_nonneg _) (by split_ifs <;> norm_num)) hρ

private theorem positive_zero_re_le_of_logLoss {a b : ℝ} (ha : 0 < a)
    (hD : UniformLogLossDensity a b) {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (hi : 0 < ρ.im) : ρ.re ≤ 1 / 2 + 1 / a := by
  by_contra! hoff
  let η := a * (ρ.re - 1 / 2) - 1
  have hη : 0 < η := by
    have h := (div_lt_iff₀ ha).mp (show 1 / a < ρ.re - 1 / 2 by linarith)
    dsimp [η]
    linarith only [h]
  obtain ⟨C,T₀,hC,hT₀,hw⟩ := hD
  have hz := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero b η hη).comp
    Real.tendsto_log_atTop).const_mul C
  simp only [Function.comp_apply,mul_zero] at hz
  have hbad : ∀ᶠ T : ℝ in atTop, False := by
    filter_upwards [eventually_ge_atTop T₀,eventually_ge_atTop ρ.im,
      hz.eventually_lt_const zero_lt_one] with T ht him hsmall
    have ht0 : 0 < T := zero_lt_one.trans (hT₀.trans_le ht)
    have hm := one_le_rightInclusiveCount_of_mem (mem_cutoff.mpr ⟨hρ,hi,him⟩)
    have hd := hw T ht ρ.re ⟨by linarith [one_div_pos.mpr ha],hρ.2.2.le⟩
    have he : T * Real.exp (-(a * Real.log T) * (ρ.re - 1 / 2)) =
        Real.exp (-η * Real.log T) := by
      calc
        _ = Real.exp (Real.log T + -(a * Real.log T) * (ρ.re - 1 / 2)) := by
          rw [Real.exp_add,Real.exp_log ht0]
        _ = _ := by congr 1; dsimp [η]; ring
    have he' : C * T * Real.log T ^ b * Real.exp (-(a * Real.log T) * (ρ.re - 1 / 2)) =
        C * (Real.log T ^ b * Real.exp (-η * Real.log T)) := by
      rw [← he]
      ring
    rw [he'] at hd
    exact (not_lt_of_ge (hm.trans hd)) hsmall
  exact hbad.exists.choose_spec

/-- Every nontrivial zero lies in the indicated half-plane if the uniform
count estimate has slope a and any fixed real logarithmic loss. -/
theorem zero_re_le_of_uniformLogLossDensity {a b : ℝ} (ha : 0 < a)
    (hD : UniformLogLossDensity a b) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    ρ.re ≤ 1 / 2 + 1 / a := by
  rcases lt_trichotomy 0 ρ.im with hi | hi | hi
  · exact positive_zero_re_le_of_logLoss ha hD hρ hi
  · have he : ρ = (ρ.re : ℂ) := by apply Complex.ext <;> simp [hi.symm]
    exact False.elim (RiemannResearch.RH.riemannZeta_ofReal_ne_zero ρ.re hρ.2.1 hρ.2.2.ne
      ((congrArg riemannZeta he).symm.trans hρ.1))
  · have hconj : IsNontrivialZero (conj ρ) := by
      refine ⟨?_,hρ.2.1,hρ.2.2⟩
      rw [_root_.riemannZeta_conj,hρ.1,map_zero]
    simpa only [Complex.conj_re] using positive_zero_re_le_of_logLoss
      (ρ := conj ρ) ha hD hconj (by simpa only [Complex.conj_im] using neg_pos.mpr hi)

/-- Reflection gives the two-sided support radius. Equality at the radius
is retained. -/
theorem zero_displacement_le_of_uniformLogLossDensity {a b : ℝ} (ha : 0 < a)
    (hD : UniformLogLossDensity a b) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    |ρ.re - 1 / 2| ≤ 1 / a := by
  have hr := zero_re_le_of_uniformLogLossDensity ha hD hρ
  have hl := zero_re_le_of_uniformLogLossDensity ha hD (zetaSeam.reflect_zero ρ hρ)
  rw [reflect_re] at hl
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem zero_displacement_le_of_uniformSelbergDensity {a : ℝ} (ha : 0 < a)
    (hD : UniformSelbergDensity a) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    |ρ.re - 1 / 2| ≤ 1 / a :=
  zero_displacement_le_of_uniformLogLossDensity ha (uniformLogLossDensity_of_uniformSelberg a hD) hρ

/-- RH supplies all finite density slopes, with the total-count provider at
the inclusive central threshold. -/
theorem uniformSelbergDensity_of_riemannHypothesis (hRH : RiemannHypothesis) (a : ℝ) :
    UniformSelbergDensity a := by
  obtain ⟨C,T₀,hC,hT₀,hw⟩ := uniformSelbergDensity_zero
  refine ⟨C,T₀,hC,hT₀,?_⟩
  intro T ht σ hσ
  by_cases hem : σ = 1 / 2
  · subst σ
    simpa only [sub_self,mul_zero,zero_mul,sub_zero] using hw T ht (1/2) hσ
  · have hs : 1 / 2 < σ := lt_of_le_of_ne hσ.1 (Ne.symm hem)
    have hzero : rightInclusiveCount T σ = 0 := by
      unfold rightInclusiveCount realSum
      apply Finset.sum_eq_zero
      intro ρ hm
      have hline := RH_implies_on_line hRH (mem_cutoff.mp hm).1
      simp only [hline,if_neg (not_le_of_gt hs),mul_zero]
    rw [hzero]
    have hT : 0 < T := zero_lt_one.trans (hT₀.trans_le ht)
    exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hT.le _)) (Real.log_pos (hT₀.trans_le ht)).le

/-- Cofinal slopes give RH even when the fixed logarithmic loss can vary
from one slope to the next. -/
theorem riemannHypothesis_iff_cofinal_logLossDensity :
    RiemannHypothesis ↔ ∀ A : ℝ, ∃ a b : ℝ, A < a ∧ UniformLogLossDensity a b := by
  constructor
  · intro h A
    exact ⟨A+1,1,by linarith,uniformLogLossDensity_of_uniformSelberg _
      (uniformSelbergDensity_of_riemannHypothesis h _)⟩
  · intro h
    apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
    intro ρ hz hr0 hr1
    by_contra hoff
    let d := |ρ.re - 1 / 2|
    have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hoff)
    obtain ⟨a,b,ha,hD⟩ := h (1/d)
    have ha0 : 0 < a := (one_div_pos.mpr hd).trans ha
    have hc := zero_displacement_le_of_uniformLogLossDensity ha0 hD
      (show IsNontrivialZero ρ from ⟨hz,hr0,hr1⟩)
    have hsmall : 1/a < d := (div_lt_iff₀ ha0).mpr (by
      simpa only [mul_comm] using (div_lt_iff₀ hd).mp ha)
    exact (not_lt_of_ge hc) hsmall

/-- A cofinal set of uniform Selberg slopes is equivalent to Mathlib RH.
No common constant or common starting height is required across the slopes. -/
theorem riemannHypothesis_iff_cofinal_uniformSelbergDensity :
    RiemannHypothesis ↔ ∀ A : ℝ, ∃ a : ℝ, A < a ∧ UniformSelbergDensity a := by
  constructor
  · intro h A
    exact ⟨A+1,by linarith,uniformSelbergDensity_of_riemannHypothesis h _⟩
  · intro h
    apply riemannHypothesis_iff_cofinal_logLossDensity.mpr
    intro A
    obtain ⟨a,ha,hD⟩ := h A
    exact ⟨a,1,ha,uniformLogLossDensity_of_uniformSelberg a hD⟩

/-- To improve a given strict horizontal boundary B, the Selberg slope
must exceed its reciprocal distance to the critical line. -/
theorem selberg_support_improves_iff {a B : ℝ} (ha : 0 < a) (hB : 1 / 2 < B) :
    1 / 2 + 1 / a < B ↔ 1 / (B - 1 / 2) < a := by
  have hδ := sub_pos.mpr hB
  constructor
  · intro h
    have hh := (div_lt_iff₀ ha).mp (show 1/a < B-1/2 by linarith only [h])
    exact (div_lt_iff₀ hδ).mpr (by simpa only [mul_comm] using hh)
  · intro h
    have hh := (div_lt_iff₀ hδ).mp h
    have h' : 1/a < B-1/2 := (div_lt_iff₀ ha).mpr (by simpa only [mul_comm] using hh)
    linarith only [h']

/-- The fixed-slope cutoff first becomes smaller than the classical open
strip boundary when a exceeds two. -/
theorem selberg_support_inside_strip_iff {a : ℝ} (ha : 0 < a) :
    1/2 + 1/a < 1 ↔ 2 < a := by
  simpa only [show (1 : ℝ)/(1-1/2) = 2 by norm_num] using
    selberg_support_improves_iff (a := a) (B := 1) ha (by norm_num)

end RiemannResearch.Analysis.ActualZeroOrdinate
