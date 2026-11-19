/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroCriticalLineTailFraction
import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.RH.WeilExplicitFormula.ThmD.Mult
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Critical-line proportions in absolute horizontal moments

The cumulative proportion of distinct zeros on the critical line bounds the
fraction of off-line occurrences. Ingham's zero density bound then transfers
the same fraction to every fixed positive horizontal moment on the scale
`log (log T) / log T`. Theorems use genuine analytic multiplicity.

Alpöge–Furman, arXiv:2608.13637v2, Theorem D and its cumulative form:
<https://arxiv.org/html/2608.13637v2>. The Montgomery–Taylor fraction is
proved by the imported Lean development. Independent source for the same
fraction: Lamzouri, arXiv:2609.02882v2.

Knausgård, arXiv:2610.08965v1, Theorem 1.3 and Proposition 5.3:
<https://arxiv.org/html/2610.08965v1>. Section 8 reports that the critical-line
proof uses one compiled branch-and-bound evaluation on seven gaps. The
paper's rational fraction is available here as an explicit literature input.

The November 19 ten-point record is the dyadic and cumulative result of
haakonrba (2026), pinned public proof and independent replay record:
<https://www.riemannzeta.fun/submissions/bakken-ten-hw-one-unit>.
Its cumulative output counts distinct critical-line zeros. The source is
represented separately from the repository's kernel-proved Montgomery–Taylor input.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Cumulative lower fraction for distinct zeros on the critical line. -/
def CumulativeDistinctCriticalProportion (κ : ℝ) : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (κ - ε) * (Ncount 0 T : ℝ) ≤ (N0star 0 T : ℝ)

/-- Kernel-proved Theorem D at the complete Montgomery–Taylor constant. -/
theorem montgomeryTaylor_distinctCriticalProportion :
    CumulativeDistinctCriticalProportion (ThmD.HD 1) :=
  ThmD.thmD₀_cumulative

/-- Rational arithmetic from Theorem 1.3 with the second window's constants. -/
theorem knausgard_critical_fraction_eq :
    ((2 : ℝ) - 6639737 / 5000000 - 4389 / 1000000) / (1 - 8722 / 1000000) =
      1669159 / 2478195 := by norm_num

/-- External input from Theorem 1.3, with the paper's actual counting conventions. -/
def KnausgardSimpleCriticalInput : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (1669159 / 2478195 - ε) * (Ncount 0 T : ℝ) ≤ (N0simple 0 T : ℝ)

/-- The exact score for the November 19 ten-point certificate of haakonrba. -/
def tenPointCriticalFraction : ℝ :=
  66732501992025865314318003264831248651423598405947 /
    99062663304046530894651923264741897583007812500000

theorem knausgard_lt_tenPointCriticalFraction : (1669159 : ℝ) / 2478195 < tenPointCriticalFraction := by
  norm_num [tenPointCriticalFraction]

theorem KnausgardSimpleCriticalInput.distinct_fraction (h : KnausgardSimpleCriticalInput) :
    CumulativeDistinctCriticalProportion (1669159 / 2478195) := by
  intro ε hε
  obtain ⟨H,hH⟩ := h ε hε
  exact ⟨H, fun T hT => (hH T hT).trans (by exact_mod_cast (trivial_chain₀ 0 T).1)⟩

/-- Tail at every horizontal cutoff, without assuming that critical zeros are simple. -/
theorem CumulativeDistinctCriticalProportion.normalized_tail {κ : ℝ}
    (hκ : CumulativeDistinctCriticalProportion κ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ δ : ℝ, 0 ≤ δ →
      strictTail T δ / (Ncount 0 T : ℝ) ≤ 1 - κ + ε := by
  obtain ⟨T₀, hb⟩ := hκ ε hε
  filter_upwards [eventually_ge_atTop T₀, eventually_count_pos] with T hT hN
  intro δ hδ
  have hs : (N0star 0 T : ℝ) ≤ (N0 0 T : ℝ) := by
    exact_mod_cast (trivial_chain₀ 0 T).2.1
  have hpro := (hb T hT).trans hs
  have hpartition := strictTail_zero_add_onLineCount T
  have htail := strictTail_le_zero T δ hδ
  apply (div_le_iff₀ (show 0 < (Ncount 0 T : ℝ) by exact_mod_cast hN)).mpr
  nlinarith only [hpartition, htail, hpro]

/-- Leading coefficient for every fixed positive order. -/
theorem CumulativeDistinctCriticalProportion.moment_ratio {κ : ℝ}
    (hκ : CumulativeDistinctCriticalProportion κ) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, displacementMoment T (p+1) / inghamDisplacementScale T ^ (p+1) ≤
      (3/2 : ℝ) ^ (p+1) * (1 - κ) + ε := by
  let F (t : ℝ) := ((1+t)*(3/2 : ℝ)) ^ (p+1) * (1-κ+t)
  have hf : Continuous F := by dsimp [F]; fun_prop
  have h0 : F 0 < (3/2 : ℝ) ^ (p+1) * (1 - κ) + ε := by dsimp [F]; linarith
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, F t < (3/2 : ℝ) ^ (p+1) * (1 - κ) + ε :=
    ((hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds h0))
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨θ, hθ, hgap⟩ := (hpos.and hev).exists
  obtain ⟨K, _, hbound⟩ := exists_displacementMoment_bound_by_offline_fraction
  have hz := (((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_div_atTop
    ((1+θ⁻¹)*(3/4 : ℝ))).pow (p+1)).const_mul (K * ((p+1).factorial : ℝ))
  have hlim : Tendsto (fun T : ℝ => F θ +
      (K * ((p+1).factorial : ℝ)) * (((1+θ⁻¹)*(3/4 : ℝ)) / Real.log (Real.log T)) ^ (p+1))
      atTop (𝓝 (F θ)) := by
    simpa only [Function.comp_apply, zero_pow (Nat.succ_ne_zero p), mul_zero, add_zero] using
      (tendsto_const_nhds (x := F θ)).add hz
  filter_upwards [hbound, hκ.normalized_tail θ hθ,
    hlim.eventually (gt_mem_nhds hgap)] with T hb hoff hsmall
  exact (hb p θ hθ).trans ((add_le_add
    (mul_le_mul_of_nonneg_left (hoff 0 le_rfl)
      (show 0 ≤ ((1+θ)*(3/2 : ℝ)) ^ (p+1) by positivity)) (le_refl _)).trans hsmall.le)

/-- The height-normalized quadratic coefficient. -/
theorem CumulativeDistinctCriticalProportion.energy_ratio {κ : ℝ}
    (hκ : CumulativeDistinctCriticalProportion κ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, horizontalEnergy T / (T * horizontalLogRate T) ≤
      9 * (1 - κ) / (8 * Real.pi) + ε := by
  let F (t : ℝ) := ((9/4)*(1-κ)+t) * (1/(2*Real.pi)+t)
  have hf : Continuous F := by dsimp [F]; fun_prop
  have h0 : F 0 < 9*(1-κ)/(8*Real.pi)+ε := by
    have he : F 0 = 9*(1-κ)/(8*Real.pi) := by dsimp [F]; ring
    linarith
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, F t < 9*(1-κ)/(8*Real.pi)+ε :=
    (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds h0)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨θ,hθ,hsmall⟩ := (hpos.and hev).exists
  have hsecond := hκ.moment_ratio 1 hθ
  have hcount := eventually_count_le_log_of_lt
    (show 1/(2*Real.pi) < 1/(2*Real.pi)+θ by linarith)
  filter_upwards [hsecond, hcount, eventually_count_pos, eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0]
      with T hm hn hp ht hℓ
  have hT : 0 < T := zero_lt_one.trans ht
  have hL := Real.log_pos ht
  have hN : (Ncount 0 T : ℝ) ≠ 0 := by positivity
  have h2 : horizontalEnergy T / (Ncount 0 T : ℝ) / inghamDisplacementScale T ^ 2 ≤ (9/4)*(1-κ)+θ := by
    norm_num [displacementMoment_two] at hm ⊢
    exact hm
  have hratio : (Ncount 0 T : ℝ) / (T * Real.log T) ≤ 1/(2*Real.pi)+θ :=
    (div_le_iff₀ (mul_pos hT hL)).mpr (by simpa only [mul_assoc] using hn)
  have he : horizontalEnergy T / (T * horizontalLogRate T) =
      (horizontalEnergy T / (Ncount 0 T : ℝ) / inghamDisplacementScale T ^ 2) *
        ((Ncount 0 T : ℝ) / (T * Real.log T)) := by
    unfold horizontalLogRate inghamDisplacementScale
    field_simp [hN, hL.ne', hℓ.ne', hT.ne']
  rw [he]
  have htop : 0 ≤ (9/4)*(1-κ)+θ :=
    (div_nonneg (div_nonneg (horizontalEnergy_nonneg T) (Nat.cast_nonneg _)) (sq_nonneg _)).trans h2
  exact (mul_le_mul h2 hratio (by positivity) htop).trans hsmall.le

/-- Established unconditional moment bounds using the verified cumulative fraction. -/
theorem montgomeryTaylor_displacementMoment_ratio_le (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, displacementMoment T (p+1) / inghamDisplacementScale T ^ (p+1) ≤
      (3/2 : ℝ) ^ (p+1) * (1 - ThmD.HD 1) + ε :=
  montgomeryTaylor_distinctCriticalProportion.moment_ratio p hε

/-- The literature refinement keeps the exact complementary rational fraction. -/
theorem knausgard_displacementMoment_ratio_le (h : KnausgardSimpleCriticalInput)
    (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, displacementMoment T (p+1) / inghamDisplacementScale T ^ (p+1) ≤
      (3/2 : ℝ) ^ (p+1) * (809036 / 2478195) + ε := by
  have hh := h.distinct_fraction
  rw [show (809036 : ℝ)/2478195 = 1 - 1669159/2478195 by norm_num]
  exact hh.moment_ratio p hε

/-- The certified arena statement is a distinct-on-line count. All occurrences
in the moment and its normalization retain their analytic multiplicities. -/
theorem tenPoint_displacementMoment_ratio_le
    (h : CumulativeDistinctCriticalProportion tenPointCriticalFraction)
    (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, displacementMoment T (p+1) / inghamDisplacementScale T ^ (p+1) ≤
      (3/2 : ℝ) ^ (p+1) * (1 - tenPointCriticalFraction) + ε :=
  h.moment_ratio p hε

end RiemannResearch.Analysis.ActualZeroOrdinate
