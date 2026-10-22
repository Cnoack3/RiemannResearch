import RiemannResearch.RH.ParetoMellinHardyEndpoint
import RiemannResearch.RH.ParetoMellinHeadObstruction
import RiemannResearch.RH.ThresholdRiemannHypothesis

/-!
# Moving Hardy bounds for exact arithmetic heads imply RH

Source: the user's proposed damping-to-zero and compactness argument,
September 24, 2026, for the research question. The proof given here uses
weighted Cauchy--Schwarz and the existing exact Mellin head-tail identity,
rather than assuming a compactness theorem or a Mellin identification.
`WeightedMellinHardy` supplies the actual Hardy norm identification;
`ThresholdRiemannHypothesis` supplies the actual arithmetic zero separator.

Status: conditional research reduction. The common bound on the genuine
Hardy line integrals while the half-plane edge tends to one half is Open.
The canonical specialization discharges legality and exact-head hypotheses;
it does not supply the common bound. A hypothetical right-half-strip zero
also forces the explicit polynomial weighted-energy cost proved below.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto
open WeightedMellin

/-- Weighted tail Cauchy--Schwarz with its complete explicit power factor. -/
theorem weightedMellin_tail_norm_sq_le
    (f : ℝ → ℂ) (u : ℝ) (hf : FiniteEnergy f u)
    (s : ℂ) (hs : u / 2 < s.re) (b : ℝ) (hb : 1 ≤ b) :
    ‖∫ x in Ioi b, f x * (x : ℂ) ^ (-s - 1)‖ ^ 2 ≤
      energy f u * (b ^ (u - 2 * s.re) / (2 * s.re - u)) := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hmeasure : volume.restrict (Ioi b) ≤ volume.restrict (Ioi (1 : ℝ)) :=
    Measure.restrict_mono (Ioi_subset_Ioi hb) le_rfl
  have hd := (density_memLp hf).mono_measure hmeasure
  have hk := (kernel_memLp u s hs).mono_measure hmeasure
  have hcs := RemoteLaplaceTail.norm_integral_mul_sq_le hd hk
  have hprod : (∫ x in Ioi b, density f u x * kernel u s x) =
      ∫ x in Ioi b, f x * (x : ℂ) ^ (-s - 1) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact density_mul_kernel f u s (lt_trans hb0 hx)
  have hkenergy : (∫ x in Ioi b, ‖kernel u s x‖ ^ 2) =
      b ^ (u - 2 * s.re) / (2 * s.re - u) := by
    calc
      _ = ∫ x in Ioi b, x ^ (u - 2 * s.re - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact kernel_norm_sq u s (lt_trans hb0 hx)
      _ = _ := by
        rw [integral_Ioi_rpow_of_lt (by linarith : u - 2 * s.re - 1 < -1) hb0]
        rw [show u - 2 * s.re - 1 + 1 = u - 2 * s.re by ring]
        rw [show u - 2 * s.re = -(2 * s.re - u) by ring, div_neg]
        ring
  have hdenergy : (∫ x in Ioi b, ‖density f u x‖ ^ 2) ≤ energy f u := by
    rw [← density_energy f u]
    exact integral_mono_measure hmeasure
      (Eventually.of_forall (fun x => sq_nonneg ‖density f u x‖))
      (density_memLp hf).norm.integrable_sq
  rw [hprod, hkenergy] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right hdenergy
    (div_nonneg (Real.rpow_nonneg hb0.le _) (by linarith)))

/-- An exact head and Mellin nullity force a nonzero weighted tail signature. -/
theorem exactHead_weighted_tail_signature_bound
    (f : ThresholdHilbert) (N : ℕ)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (u : ℝ) (hu : 1 ≤ u) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hus : u < 2 * s.re) (hnull : paretoMellin f s = 0) :
    ‖(1 - ((N : ℂ) + 1) ^ (-s)) / s‖ ^ 2 ≤
      energy (complexPhysicalStep f) u *
        (((N : ℝ) + 1) ^ (u - 2 * s.re) / (2 * s.re - u)) := by
  have hf := finiteEnergy_mono (complexPhysicalStep_finiteEnergy f) hu
  have hb : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hh := weightedMellin_tail_norm_sq_le (complexPhysicalStep f) u hf s
    (by linarith) ((N : ℝ) + 1) hb
  have he : (∫ x in Ioi ((N : ℝ) + 1),
      complexPhysicalStep f x * (x : ℂ) ^ (-s - 1)) =
      ∫ x in Ioi ((N : ℝ) + 1), mellinWeightedStep f x * paretoMellinKernel s x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (ne_of_gt (lt_trans zero_lt_one (lt_of_le_of_lt hb hx)))
    dsimp only
    rw [Complex.cpow_sub (-s) 1 hx0, Complex.cpow_one]
    unfold complexPhysicalStep mellinWeightedStep paretoMellinKernel
    ring
  rw [he, paretoMellin_tail_signature hhead s hs hnull, norm_neg] at hh
  exact hh

private theorem headSignature_norm_sq_lower
    (N : ℕ) (hN : 3 ≤ N) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    1 / (4 * ‖s‖ ^ 2) ≤ ‖(1 - ((N : ℂ) + 1) ^ (-s)) / s‖ ^ 2 := by
  have hb : 4 ≤ (N : ℝ) + 1 := by exact_mod_cast (show 4 ≤ N + 1 by omega)
  have hb0 : 0 < (N : ℝ) + 1 := by positivity
  have hmode : ‖((N : ℂ) + 1) ^ (-s)‖ = ((N : ℝ) + 1) ^ (-s.re) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      Complex.neg_re] using Complex.norm_cpow_eq_rpow_re_of_pos hb0 (-s)
  have hmode_sq : ‖((N : ℂ) + 1) ^ (-s)‖ ^ 2 ≤ (1 / 4 : ℝ) := by
    rw [hmode, ← Real.rpow_natCast, ← Real.rpow_mul hb0.le]
    calc
      _ ≤ ((N : ℝ) + 1) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
      _ = 1 / ((N : ℝ) + 1) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / 4 := (div_le_div_iff₀ hb0 (by norm_num)).2 (by linarith)
  have hmode_half : ‖((N : ℂ) + 1) ^ (-s)‖ ≤ (1 / 2 : ℝ) := by
    nlinarith [norm_nonneg (((N : ℂ) + 1) ^ (-s))]
  have hrev := norm_sub_norm_le (1 : ℂ) (((N : ℂ) + 1) ^ (-s))
  rw [norm_one] at hrev
  have hsq : (1 / 4 : ℝ) ≤ ‖1 - ((N : ℂ) + 1) ^ (-s)‖ ^ 2 := by
    nlinarith [norm_nonneg (1 - ((N : ℂ) + 1) ^ (-s))]
  rw [norm_div, div_pow]
  have hh := div_le_div_of_nonneg_right hsq (sq_nonneg ‖s‖)
  simpa only [div_div] using hh

/-- A zero imposes a quantified polynomial cost in every weaker Hardy space
whose boundary still lies to its left. This estimate is exact at each cutoff. -/
theorem exactHead_weightedEnergy_lower_of_mellin_zero
    (f : ThresholdHilbert) (N : ℕ) (hN : 3 ≤ N)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1)
    (u : ℝ) (hu : 1 ≤ u) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hus : u < 2 * s.re) (hnull : paretoMellin f s = 0) :
    ((2 * s.re - u) / (4 * ‖s‖ ^ 2)) *
      ((N : ℝ) + 1) ^ (2 * s.re - u) ≤ energy (complexPhysicalStep f) u := by
  have hh := (headSignature_norm_sq_lower N hN s hs).trans
    (exactHead_weighted_tail_signature_bound f N hhead u hu s hs hus hnull)
  have hd : 0 < 2 * s.re - u := sub_pos.mpr hus
  have hp : 0 < ((N : ℝ) + 1) ^ (2 * s.re - u) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hd.le hp.le)
  have he : (2 * s.re - u) * ((N : ℝ) + 1) ^ (2 * s.re - u) *
      (energy (complexPhysicalStep f) u *
        (((N : ℝ) + 1) ^ (u - 2 * s.re) / (2 * s.re - u))) =
      energy (complexPhysicalStep f) u := by
    rw [show u - 2 * s.re = -(2 * s.re - u) by ring,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)]
    field_simp [hd.ne', hp.ne']
  rw [he] at hm
  simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using hm

/-- A fixed weighted-energy bound below a proposed zero excludes that zero. -/
theorem zeta_ne_zero_of_exactHead_weightedEnergy_bound
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (f : ℕ → ThresholdHilbert) (hlegal : ∀ N, f N ∈ hilbertLegalClosure A)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (f N) k = 1)
    (u C : ℝ) (hu : 1 ≤ u)
    (hbound : ∀ᶠ N in atTop, energy (complexPhysicalStep (f N)) u ≤ C)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hus : u < 2 * s.re)
    (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hc : 0 < 1 / (4 * ‖s‖ ^ 2) := by
    exact one_div_pos.mpr (mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hs0) 2))
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).comp (tendsto_add_atTop_nat 1)
  have hp : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (u - 2 * s.re)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hus)).comp ht
  have hdecay : Tendsto (fun N : ℕ => C *
      (((N : ℝ) + 1) ^ (u - 2 * s.re) / (2 * s.re - u))) atTop (𝓝 0) := by
    simpa only [zero_div, mul_zero] using (hp.div_const (2 * s.re - u)).const_mul C
  obtain ⟨N, hN, hbN, hsmall⟩ :=
    ((eventually_ge_atTop 3).and
      (hbound.and (hdecay.eventually (gt_mem_nhds hc)))).exists
  have hnull := paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz (hlegal N)
  have hb := exactHead_weighted_tail_signature_bound (f N) N (hhead N)
    u hu s hs hus hnull
  have hq : 0 ≤ ((N : ℝ) + 1) ^ (u - 2 * s.re) / (2 * s.re - u) := by positivity
  have hl := (headSignature_norm_sq_lower N hN s hs).trans
    (hb.trans (mul_le_mul_of_nonneg_right hbN hq))
  exact (not_lt_of_ge hl) hsmall

/-- Conditional research reduction: bounded energies as the exponent drops to
the RH-critical value suffice for the actual Riemann hypothesis. -/
theorem riemannHypothesis_of_exactHead_movingEnergy_bound
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (f : ℕ → ThresholdHilbert) (hlegal : ∀ N, f N ∈ hilbertLegalClosure A)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (f N) k = 1)
    (α : ℕ → ℝ) (hαnonneg : ∀ N, 0 ≤ α N)
    (hα : Tendsto α atTop (𝓝 0)) (C : ℝ)
    (hbound : ∀ N, energy (complexPhysicalStep (f N)) (1 + 2 * α N) ≤ C) :
    RiemannHypothesis := by
  have hright (s : ℂ) (hsz : riemannZeta s = 0)
      (hs0 : 0 < s.re) (hs1 : s.re < 1) : s.re ≤ 1 / 2 := by
    by_contra hh
    have hs : (1 / 2 : ℝ) < s.re := lt_of_not_ge hh
    let u : ℝ := s.re + 1 / 2
    have hu : 1 ≤ u := by dsimp [u]; linarith
    have hus : u < 2 * s.re := by dsimp [u]; linarith
    have hlim : Tendsto (fun N => 1 + 2 * α N) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add (hα.const_mul 2)
    have hsmall : ∀ᶠ N in atTop, 1 + 2 * α N ≤ u := by
      exact (hlim.eventually (gt_mem_nhds (show (1 : ℝ) < u by dsimp [u]; linarith))).mono
        (fun N hN => hN.le)
    have hb : ∀ᶠ N in atTop, energy (complexPhysicalStep (f N)) u ≤ C := by
      filter_upwards [hsmall] with N hN
      exact (energy_mono (finiteEnergy_mono (complexPhysicalStep_finiteEnergy (f N))
        (by nlinarith [hαnonneg N])) hN).trans (hbound N)
    have hsne : s ≠ 1 := by intro he; simp [he] at hs1
    exact zeta_ne_zero_of_exactHead_weightedEnergy_bound A hA f hlegal hhead
      u C hu hb s hs hus hsne hsz
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hr := Zeta23.zeta_reflect_zero ρ ⟨hz, h0, h1⟩
  have hrbound := hright (Zeta23.reflect ρ) hr.1 hr.2.1 hr.2.2
  have hbnd := hright ρ hz h0 h1
  simp [Zeta23.reflect] at hrbound
  linarith

/-- The premise is stated as actual uniformly bounded Hardy line integrals,
not as a surrogate sequence norm or an assumed Mellin identification. -/
theorem riemannHypothesis_of_exactHead_movingHardy_bound
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (f : ℕ → ThresholdHilbert) (hlegal : ∀ N, f N ∈ hilbertLegalClosure A)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (f N) k = 1)
    (α : ℕ → ℝ) (hαnonneg : ∀ N, 0 ≤ α N)
    (hα : Tendsto α atTop (𝓝 0)) (C : ℝ)
    (hbound : ∀ N σ, 1 / 2 + α N < σ →
      (∫ w : ℝ, ‖paretoMellin (f N) (verticalPoint σ w)‖ ^ 2) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_exactHead_movingEnergy_bound A hA f hlegal hhead α hαnonneg hα C
  intro N
  have hf := finiteEnergy_mono (complexPhysicalStep_finiteEnergy (f N))
    (show 1 ≤ 1 + 2 * α N by nlinarith [hαnonneg N])
  apply (hardy_energy_isLUB hf).2
  rintro y ⟨σ, hσ, rfl⟩
  rw [complexPhysicalStep_transform]
  exact hbound N σ (by linarith)

/-- Actual canonical corrected Möbius family. The only unresolved input is
the uniform Hardy bound while the half-plane edge approaches one half. -/
theorem canonicalMobius_riemannHypothesis_of_movingHardy_bound
    (α : ℕ → ℝ) (hαnonneg : ∀ N, 0 ≤ α N)
    (hα : Tendsto α atTop (𝓝 0)) (C : ℝ)
    (hbound : ∀ N σ, 1 / 2 + α N < σ →
      (∫ w : ℝ, ‖paretoMellin (canonicalMobiusHilbert N)
        (verticalPoint σ w)‖ ^ 2) ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_exactHead_movingHardy_bound
    {n : ℕ | 0 < n} (fun _ hn => hn) canonicalMobiusHilbert
    (fun N => CoefficientStabilization.closedSpace_le_legalClosure
      (CoefficientStabilization.canonicalMobiusHilbert_mem_closedSpace N))
    (fun N k hk hkN => canonicalMobiusHilbert_exact N k hk hkN)
    α hαnonneg hα C hbound

end RiemannResearch.RH.Pareto
