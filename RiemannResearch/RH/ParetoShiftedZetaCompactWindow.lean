/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoLCMAnalyticRates
import RiemannResearch.RH.WeilExplicitFormula.Statement.Seam
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp

/-!
# The shifted-zeta budget on compact ordinate windows

Local analytic factorization retains the power of the zero. A horizontal
shift of that power has a Lorentzian square bound, with integrated mass
of order the shift. The analytic unit contributes a square of the shift.
This is the bounded-height part of the quotient integral in Proposition 2
of Balazard and de Roton (https://arxiv.org/abs/0812.1689).
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology NNReal BigOperators

namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint criticalPoint_ne_one criticalPoint_re)

private theorem criticalPoint_sub (t a : ℝ) :
    criticalPoint t - criticalPoint a = ((t - a : ℝ) : ℂ) * Complex.I := by
  simp only [MellinFrequency.criticalPoint, Complex.ofReal_sub]
  ring

private theorem dist_criticalPoint (t a : ℝ) :
    dist (criticalPoint t) (criticalPoint a) = |t - a| := by
  rw [dist_eq_norm, criticalPoint_sub, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

private theorem zeta_local_factor (a : ℝ) :
    ∃ (m : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g (criticalPoint a) ∧
      g (criticalPoint a) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (criticalPoint a), riemannZeta z = (z - criticalPoint a) ^ m * g z := by
  have ha := criticalPoint_ne_one a
  have han := Zeta23.riemannZeta_analyticOnNhd_compl_one (criticalPoint a) ha
  obtain ⟨g, hg, hg₀, hf⟩ := han.analyticOrderAt_ne_top.mp
    (Zeta23.analyticOrderAt_riemannZeta_ne_top ha)
  exact ⟨_, g, hg, hg₀, hf⟩

private theorem norm_one_sub_pow_le (q : ℂ) (hq : ‖q‖ ≤ 1) (m : ℕ) :
    ‖1 - q ^ m‖ ≤ (m : ℝ) * ‖1 - q‖ := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [show 1 - q ^ (m + 1) = (1 - q) + q * (1 - q ^ m) by rw [pow_succ]; ring]
    calc
      _ ≤ ‖1 - q‖ + ‖q * (1 - q ^ m)‖ := norm_add_le _ _
      _ ≤ ‖1 - q‖ + ‖1 - q ^ m‖ := by
        rw [norm_mul]
        exact add_le_add (le_refl _) (mul_le_of_le_one_left (norm_nonneg (1 - q ^ m)) hq)
      _ ≤ _ := by rw [Nat.cast_succ, add_mul, one_mul]; linarith only [hm]

/-- A neighborhood of every ordinate has a uniform bound for the actual
shifted quotient. A pole in the denominator is excluded by the same local factor. -/
theorem shiftedZetaQuotient_local_bound (a : ℝ) :
    ∃ r > 0, ∃ A ≥ 0, ∀ (t ε : ℝ), |t - a| < r → 0 < ε → ε < r →
      riemannZeta (criticalPoint t + (ε : ℂ)) ≠ 0 ∧
      boundarySquare (fun v => 1 - shiftedZetaQuotient ε v) t ≤
        A * (ε ^ 2 + ε ^ 2 / (ε ^ 2 + (t - a) ^ 2)) := by
  let s₀ := criticalPoint a
  obtain ⟨m, g, hg, hg₀, hfac⟩ := zeta_local_factor a
  let c := ‖g s₀‖ / 2
  have hc : 0 < c := by dsimp only [c, s₀]; positivity
  have hgsmall : ∀ᶠ z in 𝓝 s₀, c < ‖g z‖ := hg.continuousAt.norm.eventually
    (lt_mem_nhds (by dsimp only [c]; linarith [norm_pos_iff.mpr hg₀]))
  obtain ⟨K, V, hV, hLip⟩ := hg.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hfac.and (hgsmall.and hV))
  let A := (K : ℝ) / c
  have hA : 0 ≤ A := div_nonneg K.coe_nonneg hc.le
  refine ⟨R / 2, by positivity, 8 * ((m : ℝ) ^ 2 + A ^ 2), by positivity, ?_⟩
  intro t ε ht hε hεR
  let s := criticalPoint t
  let u := s + (ε : ℂ)
  have hs : s ∈ Metric.ball s₀ R := by
    rw [Metric.mem_ball, dist_criticalPoint]
    linarith
  have hus : dist u s = ε := by
    change dist (s + (ε : ℂ)) s = ε
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have hu : u ∈ Metric.ball s₀ R := by
    rw [Metric.mem_ball]
    calc
      _ ≤ dist u s + dist s s₀ := dist_triangle _ _ _
      _ < _ := by rw [hus, dist_criticalPoint]; linarith
  obtain ⟨hfs, hcs, hsV⟩ := hball hs
  obtain ⟨hfu, hcu, huV⟩ := hball hu
  change riemannZeta s = (s - s₀) ^ m * g s at hfs
  change riemannZeta u = (u - s₀) ^ m * g u at hfu
  have hgu : 0 < ‖g u‖ := hc.trans hcu
  have hgu₀ : g u ≠ 0 := norm_pos_iff.mp hgu
  have hu₀ : u - s₀ ≠ 0 := by
    intro he
    have hr := congrArg Complex.re (sub_eq_zero.mp he)
    simp [u, s, s₀, criticalPoint_re] at hr
    linarith
  have hnonzero : riemannZeta u ≠ 0 := by
    rw [hfu]
    exact mul_ne_zero (pow_ne_zero _ hu₀) hgu₀
  refine ⟨hnonzero, ?_⟩
  let q := (s - s₀) / (u - s₀)
  let B := g s / g u
  have hqform : shiftedZetaQuotient ε t = q ^ m * B := by
    change riemannZeta s / riemannZeta u = _
    rw [hfs, hfu, mul_div_mul_comm, ← div_pow]
  have hunorm : ‖u - s₀‖ ^ 2 = ε ^ 2 + (t - a) ^ 2 := by
    rw [show u - s₀ = (ε : ℂ) + ((t - a : ℝ) : ℂ) * Complex.I by
      change s + (ε : ℂ) - s₀ = _
      rw [show s + (ε : ℂ) - s₀ = (ε : ℂ) + (s - s₀) by ring]
      rw [criticalPoint_sub]]
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  have hq : ‖q‖ ≤ 1 := by
    change ‖(s - s₀) / (u - s₀)‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr hu₀)]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hunorm, criticalPoint_sub, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg ε]
  have hqdiff : ‖1 - q‖ ^ 2 = ε ^ 2 / (ε ^ 2 + (t - a) ^ 2) := by
    rw [show 1 - q = (ε : ℂ) / (u - s₀) by
      dsimp only [q]
      field_simp [hu₀]
      dsimp only [u]
      ring]
    rw [norm_div, div_pow, hunorm, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hB : ‖1 - B‖ ≤ A * ε := by
    rw [show 1 - B = (g u - g s) / g u by dsimp only [B]; field_simp [hgu₀]]
    rw [norm_div]
    have hgs : ‖g u - g s‖ ≤ (K : ℝ) * ε := by
      have hh := hLip.dist_le_mul u huV s hsV
      rw [hus, dist_eq_norm] at hh
      exact hh
    refine (div_le_div_of_nonneg_right hgs hgu.le).trans ?_
    change (K : ℝ) * ε / ‖g u‖ ≤ (K : ℝ) / c * ε
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (mul_nonneg K.coe_nonneg hε.le) hc hcu.le
  have hdef : ‖1 - shiftedZetaQuotient ε t‖ ≤ (m : ℝ) * ‖1 - q‖ + A * ε := by
    rw [hqform, show 1 - q ^ m * B = (1 - q ^ m) + q ^ m * (1 - B) by ring]
    refine (norm_add_le _ _).trans (add_le_add (norm_one_sub_pow_le q hq m) ?_)
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq)).trans hB
  have hsq : ‖1 - shiftedZetaQuotient ε t‖ ^ 2 ≤
      2 * ((m : ℝ) ^ 2 * (ε ^ 2 / (ε ^ 2 + (t - a) ^ 2)) + A ^ 2 * ε ^ 2) := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hdef
    refine hh.trans ?_
    calc
      _ ≤ 2 * (((m : ℝ) * ‖1 - q‖) ^ 2 + (A * ε) ^ 2) := by
        nlinarith only [sq_nonneg ((m : ℝ) * ‖1 - q‖ - A * ε)]
      _ = _ := by rw [mul_pow, mul_pow, hqdiff]
  unfold boundarySquare
  apply (div_le_iff₀ (by positivity)).mpr
  have he : 0 ≤ ε ^ 2 / (ε ^ 2 + (t - a) ^ 2) := by positivity
  have ht' : (1 / 4 : ℝ) ≤ 1 / 4 + t ^ 2 := by linarith [sq_nonneg t]
  have hmajor : 0 ≤ 8 * ((m : ℝ) ^ 2 + A ^ 2) *
      (ε ^ 2 + ε ^ 2 / (ε ^ 2 + (t - a) ^ 2)) := by positivity
  refine hsq.trans (le_trans ?_ (mul_le_mul_of_nonneg_left ht' hmajor))
  nlinarith only [mul_nonneg (sq_nonneg (m : ℝ)) (sq_nonneg ε),
    mul_nonneg (sq_nonneg A) he]

private theorem lorentzian_interval_bound (a b u ε : ℝ) (hε : 0 < ε) :
    (∫ t in a..b, ε ^ 2 / (ε ^ 2 + (t - u) ^ 2)) ≤ Real.pi * ε := by
  have heq (t : ℝ) : ε ^ 2 / (ε ^ 2 + (t - u) ^ 2) =
      ε * (ε / (ε ^ 2 + (t - u) ^ 2)) := by rw [← mul_div_assoc, pow_two]
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun t => ε / (ε ^ 2 + t ^ 2)) u,
    integral_div_sq_add_sq, mul_comm Real.pi]
  exact mul_le_mul_of_nonneg_left (by
    linarith [Real.arctan_lt_pi_div_two ((b - u) / ε),
      Real.neg_pi_div_two_lt_arctan ((a - u) / ε)]) hε.le

private theorem quotientWindow_majorant_integral (T a ε A : ℝ) (hT : 0 ≤ T)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hA : 0 ≤ A) :
    (∫ t in -T..T, A * (ε ^ 2 + ε ^ 2 / (ε ^ 2 + (t - a) ^ 2))) ≤
      (A * (2 * T + Real.pi)) * ε := by
  have hc : Continuous (fun t : ℝ => ε ^ 2 / (ε ^ 2 + (t - a) ^ 2)) :=
    continuous_const.div (by fun_prop) (fun _ => by positivity)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const, smul_eq_mul]
  have hconst : (T - -T) * ε ^ 2 ≤ 2 * T * ε := by
    have hh := mul_le_mul_of_nonneg_left hε₁ hε.le
    nlinarith only [mul_nonneg hT (sub_nonneg.mpr hh)]
  exact (mul_le_mul_of_nonneg_left
    (add_le_add hconst (lorentzian_interval_bound (-T) T a ε hε)) hA).trans_eq (by ring)

/-- The Balazard–de Roton quotient contributes at most order ε on each fixed
ordinate interval. The constant depends on the window and actual local
zeta factors. -/
theorem shiftedZetaQuotient_window_le (T : ℝ) (hT : 0 ≤ T) :
    ∃ C ≥ 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (boundarySquare (fun t => 1 - shiftedZetaQuotient ε t)) volume (-T) T ∧
      (∫ t in Set.Icc (-T) T, boundarySquare (fun v => 1 - shiftedZetaQuotient ε v) t) ≤ C * ε := by
  classical
  choose r hr A hA hlocal using shiftedZetaQuotient_local_bound
  let U a := Metric.ball a (r a)
  have hopen (a : ℝ) : IsOpen (U a) := Metric.isOpen_ball
  have hcov : Icc (-T) T ⊆ ⋃ a, U a := fun t _ =>
    mem_iUnion.mpr ⟨t, Metric.mem_ball_self (hr t)⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U hopen hcov
  refine ⟨∑ a ∈ s, A a * (2 * T + Real.pi), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun a _ => by positivity [hA a, Real.pi_pos])
  have hεR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a ∈ s, ε < r a :=
    (Filter.eventually_all_finset s).mpr fun a _ =>
      (gt_mem_nhds (hr a)).filter_mono nhdsWithin_le_nhds
  have hε₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 / 4 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds
  have hεpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  filter_upwards [hεR, hε₁, hεpos] with ε hεR hε₁ hε
  let f := boundarySquare (fun t => 1 - shiftedZetaQuotient ε t)
  let P (a t : ℝ) := A a * (ε ^ 2 + ε ^ 2 / (ε ^ 2 + (t - a) ^ 2))
  have hpoint (t : ℝ) (ht : t ∈ Icc (-T) T) :
      riemannZeta (criticalPoint t + (ε : ℂ)) ≠ 0 ∧ f t ≤ ∑ a ∈ s, P a t := by
    obtain ⟨a, hta⟩ := mem_iUnion.mp (hs ht)
    obtain ⟨ha, hta⟩ := mem_iUnion.mp hta
    have habs : |t - a| < r a := by
      simpa only [U, Metric.mem_ball, Real.dist_eq] using hta
    obtain ⟨hz, hf⟩ := hlocal a t ε habs hε (hεR a ha)
    refine ⟨hz, hf.trans ?_⟩
    exact Finset.single_le_sum (f := fun a => P a t) (fun b _ => by
      dsimp only [P]
      positivity [hA b]) ha
  have hcp : Continuous criticalPoint := by unfold criticalPoint; fun_prop
  have hc₁ : ContinuousOn (fun t => riemannZeta (criticalPoint t)) (Icc (-T) T) := by
    intro t _
    exact ((differentiableAt_riemannZeta (criticalPoint_ne_one t)).continuousAt.comp
      hcp.continuousAt).continuousWithinAt
  have hc₂ : ContinuousOn (fun t => riemannZeta (criticalPoint t + (ε : ℂ))) (Icc (-T) T) := by
    intro t _
    have hne : criticalPoint t + (ε : ℂ) ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp [criticalPoint_re] at hr
      linarith
    have hshift : Continuous (fun v : ℝ => criticalPoint v + (ε : ℂ)) :=
      hcp.add continuous_const
    have hz : ContinuousAt riemannZeta (criticalPoint t + (ε : ℂ)) :=
      (differentiableAt_riemannZeta hne).continuousAt
    exact (hz.comp (x := t) hshift.continuousAt).continuousWithinAt
  have hQ : ContinuousOn (shiftedZetaQuotient ε) (Icc (-T) T) :=
    hc₁.div hc₂ (fun t ht => (hpoint t ht).1)
  have hf : ContinuousOn f (Icc (-T) T) := by
    apply ((continuousOn_const.sub hQ).norm.pow 2).div
    · exact (show Continuous (fun t : ℝ => 1 / 4 + t ^ 2) by fun_prop).continuousOn
    · intro t _
      positivity
  have hT' : -T ≤ T := by linarith
  have hfI := hf.intervalIntegrable_of_Icc (μ := volume) hT'
  refine ⟨hfI, ?_⟩
  have hP (a : ℝ) : Continuous (P a) := by
    dsimp only [P]
    exact continuous_const.mul (continuous_const.add
      (continuous_const.div (by fun_prop) (fun _ => by positivity)))
  have hPI (a : ℝ) : IntervalIntegrable (P a) volume (-T) T := (hP a).intervalIntegrable _ _
  have hPS : IntervalIntegrable (fun t => ∑ a ∈ s, P a t) volume (-T) T := by
    simpa only [← Finset.sum_apply] using (IntervalIntegrable.sum s (fun a _ => hPI a))
  change (∫ t in Icc (-T) T, f t) ≤ _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT']
  calc
    _ ≤ ∫ t in -T..T, ∑ a ∈ s, P a t :=
      intervalIntegral.integral_mono_on hT' hfI hPS (fun t ht => (hpoint t ht).2)
    _ = ∑ a ∈ s, ∫ t in -T..T, P a t := intervalIntegral.integral_finsetSum (fun a _ => hPI a)
    _ ≤ ∑ a ∈ s, (A a * (2 * T + Real.pi)) * ε :=
      Finset.sum_le_sum (fun a _ => quotientWindow_majorant_integral T a ε (A a)
        hT hε (by linarith) (hA a))
    _ = _ := by rw [Finset.sum_mul]

end RiemannResearch.RH.Pareto.ResidueMellin
