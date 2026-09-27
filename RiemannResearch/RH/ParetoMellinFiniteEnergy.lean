import RiemannResearch.RH.ParetoMellinHolomorphic
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphy of the actual Pareto Mellin integral under finite energy

The proof extends the bounded-sequence theorem by genuine Hilbert-norm
approximation. It uses Mathlib's Weierstrass theorem for locally uniform
limits. No arithmetic, zeta, residual regularity, or RH hypothesis is used.

Source: the general Hilbert approximation and holomorphic limit argument.
Burnol, arXiv:math/0202166, Theorem 4.1, motivates the finite-energy
Mellin application; no result conditional on RH is used here.
-/

namespace RiemannResearch.RH.Pareto
open Set Filter
open scoped Topology BigOperators
noncomputable section

theorem paretoMellin_tendstoUniformlyOn_of_tendsto
    {ι : Type*} {l : Filter ι} {F : ι → ThresholdHilbert}
    {f : ThresholdHilbert} (hF : Tendsto F l (𝓝 f))
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) :
    TendstoUniformlyOn (fun i s => paretoMellin (F i) s)
      (paretoMellin f) l {s : ℂ | σ < s.re} := by
  let C : ℝ := Real.sqrt (1 / (2 * σ - 1))
  have hzero : Tendsto (fun i => C * ‖F i - f‖) l (𝓝 0) := by
    have h := ((hF.sub (tendsto_const_nhds (x := f))).norm).const_mul C
    simpa only [sub_self, norm_zero, mul_zero] using h
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hzero.eventually (gt_mem_nhds hε)] with i hi s hs
  have hs' : (1 / 2 : ℝ) < s.re := lt_trans hσ hs
  have hmap := (paretoMellinContinuous s hs').map_sub f (F i)
  change paretoMellin (f - F i) s =
    paretoMellin f s - paretoMellin (F i) s at hmap
  have hc : Real.sqrt (1 / (2 * s.re - 1)) ≤ C := by
    apply Real.sqrt_le_sqrt
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  calc
    dist (paretoMellin f s) (paretoMellin (F i) s)
        = ‖paretoMellin (f - F i) s‖ := by rw [dist_eq_norm, ← hmap]
    _ ≤ Real.sqrt (1 / (2 * s.re - 1)) * ‖f - F i‖ :=
      paretoMellin_norm_le _ _ hs'
    _ ≤ C * ‖f - F i‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = C * ‖F i - f‖ := by rw [norm_sub_rev]
    _ < ε := hi

private theorem hilbertSequence_single_abs_le (i : ℕ) (c : ℝ) (k : ℕ) :
    |hilbertSequence (lp.single 2 i c) k| ≤
      |c / Real.sqrt (paretoWeight i)| := by
  cases k with
  | zero => simp
  | succ n =>
    by_cases hn : n = i
    · subst n
      simp [hilbertSequence_succ]
    · simp [hilbertSequence_succ, lp.single_apply, hn]

private theorem hilbertSequence_finite_sum_single_bounded
    (f : ThresholdHilbert) (t : Finset ℕ) :
    ∃ C : ℝ, ∀ k,
      |hilbertSequence (∑ i ∈ t, lp.single 2 i (f i)) k| ≤ C := by
  refine ⟨∑ i ∈ t, |f i / Real.sqrt (paretoWeight i)|, ?_⟩
  intro k
  have he : hilbertSequence (∑ i ∈ t, lp.single 2 i (f i)) k =
      ∑ i ∈ t, hilbertSequence (lp.single 2 i (f i)) k := by
    change hilbertSequenceLinear (∑ i ∈ t, lp.single 2 i (f i)) k = _
    rw [map_sum]
    simp [Finset.sum_apply, hilbertSequenceLinear]
  rw [he]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => hilbertSequence_single_abs_le i (f i) k)

/-- Every finite-energy physical step sequence has a holomorphic Mellin
integral on the genuine continuity half-plane. -/
theorem paretoMellin_differentiableAt (f : ThresholdHilbert)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    DifferentiableAt ℂ (paretoMellin f) s := by
  let σ : ℝ := (s.re + 1 / 2) / 2
  have hσ : (1 / 2 : ℝ) < σ := by dsimp [σ]; linarith
  have hsσ : σ < s.re := by dsimp [σ]; linarith
  let F : Finset ℕ → ThresholdHilbert := fun t => ∑ i ∈ t, lp.single 2 i (f i)
  have hF : Tendsto F atTop (𝓝 f) :=
    lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) f
  have hU : IsOpen {z : ℂ | σ < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hd : ∀ t : Finset ℕ,
      DifferentiableOn ℂ (paretoMellin (F t)) {z : ℂ | σ < z.re} := by
    intro t
    obtain ⟨C, hC⟩ := hilbertSequence_finite_sum_single_bounded f t
    intro z hz
    exact (paretoMellin_differentiableAt_of_bounded (F t) hC z
      (by have := hσ; change σ < z.re at hz; linarith)).differentiableWithinAt
  have hu := paretoMellin_tendstoUniformlyOn_of_tendsto hF σ hσ
  exact (hu.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall hd) hU s hsσ).differentiableAt (hU.mem_nhds hsσ)

theorem paretoMellin_differentiableOn (f : ThresholdHilbert) :
    DifferentiableOn ℂ (paretoMellin f) {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  intro s hs
  exact (paretoMellin_differentiableAt f s hs).differentiableWithinAt

theorem paretoMellin_analyticOnNhd (f : ThresholdHilbert) :
    AnalyticOnNhd ℂ (paretoMellin f) {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  exact (paretoMellin_differentiableOn f).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

end
end RiemannResearch.RH.Pareto
