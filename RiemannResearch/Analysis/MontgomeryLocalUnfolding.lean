import RiemannResearch.Analysis.MontgomeryTaylorMicroscopicDensity

/-! # Local unfolding for microscopic pair counts of actual zero ordinates -/

noncomputable section
open Filter Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualMontgomeryExceptionalPairs

/-- Uniform choice of a center in a dyadic height interval. Both logarithmic
densities have ratio tending to one even if the relative centers oscillate. -/
theorem dyadic_local_log_ratio {ι : Type*} {l : Filter ι} {T c : ι → ℝ}
    (hT : Tendsto T l atTop) (hc : ∀ᶠ i in l, T i ≤ c i ∧ c i ≤ 2*T i) :
    Tendsto (fun i => Real.log (c i / (2*Real.pi)) / Real.log (T i)) l (𝓝 1) := by
  have hL := Real.tendsto_log_atTop.comp hT
  have hsmall (b : ℝ) : Tendsto (fun i => b / Real.log (T i)) l (𝓝 0) :=
    by simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hL).const_mul b
  have hlow := (tendsto_const_nhds (x := (1:ℝ))).sub (hsmall (Real.log (2*Real.pi)))
  have hupp := (tendsto_const_nhds (x := (1:ℝ))).add
    (hsmall (Real.log 2 - Real.log (2*Real.pi)))
  simp only [sub_zero, add_zero] at hlow hupp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  all_goals
    filter_upwards [hc,hT.eventually (eventually_gt_atTop (1:ℝ))] with i hi ht
    have ht0 : 0 < T i := zero_lt_one.trans ht
    have hc0 := ht0.trans_le hi.1
    have hp : 0 < 2*Real.pi := by positivity
    have hl := Real.log_pos ht
    have h1 := Real.log_le_log ht0 hi.1
    have h2 := Real.log_le_log hc0 hi.2
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) ht0.ne'] at h2
    rw [Real.log_div hc0.ne' hp.ne']
    field_simp [hl.ne']
    linarith

theorem dyadic_physical_width_unfolds {ι : Type*} {l : Filter ι} {T c Q : ι → ℝ}
    {q : ℝ} (hT : Tendsto T l atTop) (hc : ∀ᶠ i in l, T i ≤ c i ∧ c i ≤ 2*T i)
    (hQ : Tendsto Q l (𝓝 q)) :
    Tendsto (fun i => (Real.log (T i) / (2*Real.pi)) *
      (2*Real.pi*Q i / Real.log (c i / (2*Real.pi)))) l (𝓝 q) := by
  have hl := dyadic_local_log_ratio hT hc
  have h := hQ.div hl (by norm_num : (1:ℝ) ≠ 0)
  simp only [div_one] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro i
  simp only [Pi.div_apply, div_div_eq_mul_div]
  rw [← mul_div_assoc]
  congr 1
  field_simp [Real.pi_ne_zero]


/-- Counts up to each cutoff with the spacing evaluated at any local dyadic
center. Both the cutoffs and test widths can vary. -/
theorem PositiveGapPCC.dyadic_local_width {ι : Type*} {l : Filter ι} (h : PositiveGapPCC)
    {T c Q : ι → ℝ} {q : ℝ} (hT : Tendsto T l atTop)
    (hc : ∀ᶠ i in l, T i ≤ c i ∧ c i ≤ 2*T i)
    (hQ : Tendsto Q l (𝓝 q)) (hq : 0 < q) :
    Tendsto (fun i => physicalStrictPairs (T i) (2*Real.pi*Q i / Real.log (c i / (2*Real.pi))) /
      unfoldedCutoff (T i)) l (𝓝 (sineGapMass q)) :=
  h.moving_physical_width hT (dyadic_physical_width_unfolds hT hc hQ) hq

/-- A positive unconditional lower bound as soon as q exceeds 2000000/1345001. -/
theorem moving_dyadic_strict_pair_lower {ι : Type*} {l : Filter ι}
    {T c Q : ι → ℝ} {q : ℝ} (hT : Tendsto T l atTop)
    (hc : ∀ᶠ i in l, T i ≤ c i ∧ c i ≤ 2*T i)
    (hQ : Tendsto Q l (𝓝 q)) (hq : 0 < q) :
    ∀ᶠ i in l, 1345001/2000000 - 1/q <
      physicalStrictPairs (T i) (2*Real.pi*Q i / Real.log (c i / (2*Real.pi))) /
      unfoldedCutoff (T i) :=
  moving_strict_pair_density_lower hT hq (dyadic_physical_width_unfolds hT hc hQ)
    (sub_lt_sub_right montgomeryTaylor_fraction_gt_1345001_div_2000000 _)

/-- Fujii's row bound and the simple-critical proportion place the actual
normalized count between positive constants for any such moving width. -/
theorem moving_strict_pairs_order_one_of_fujii {ι : Type*} {l : Filter ι}
    (hf : FujiiMicroscopicRowMoments) {T w : ι → ℝ} {q : ℝ}
    (hT : Tendsto T l atTop) (hq : 0 < q)
    (hw : Tendsto (fun i => unfoldingScale (T i) * w i) l (𝓝 q))
    (hs : 1/q < ThmD.HD 1) :
    ∃ a b : ℝ, 0 < a ∧ ∀ᶠ i in l,
      a < physicalStrictPairs (T i) (w i) / unfoldedCutoff (T i) ∧
      physicalStrictPairs (T i) (w i) / unfoldedCutoff (T i) ≤ b := by
  let a := (ThmD.HD 1 - 1/q)/2
  have ha : 0 < a := half_pos (sub_pos.mpr hs)
  have hlo := moving_strict_pair_density_lower hT hq hw (half_lt_self (sub_pos.mpr hs))
  obtain ⟨C,hC,hup⟩ := eventually_microscopic_upper_of_fujii hf (2*Real.pi*(q+1))
  refine ⟨a,2*C,ha,?_⟩
  filter_upwards [hlo, hT.eventually hup, hT.eventually (eventually_gt_atTop (1:ℝ)),
    hw.eventually (lt_mem_nhds hq), hw.eventually (gt_mem_nhds (show q < q+1 by linarith)),
    hT.eventually (tendsto_count_div_mainTerm.eventually
      (gt_mem_nhds (show (1:ℝ) < 2 by norm_num)))] with i hi hu ht hpos hbound hcount
  have hL : 0 < unfoldingScale (T i) := div_pos (Real.log_pos ht) (by positivity)
  have hw0 := (mul_pos_iff_of_pos_left hL).mp hpos
  have hwidth : w i * Real.log (T i) ≤ 2*Real.pi*(q+1) := by
    change Real.log (T i)/(2*Real.pi) * w i < q+1 at hbound
    rw [div_mul_eq_mul_div] at hbound
    have h' := (div_lt_iff₀ (show (0:ℝ) < 2*Real.pi by positivity)).mp hbound
    linarith only [h',mul_comm (w i) (Real.log (T i)),mul_comm (2*Real.pi) (q+1)]
  have hD : 0 < unfoldedCutoff (T i) :=
    div_pos (mul_pos (zero_lt_one.trans ht) (Real.log_pos ht)) (by positivity)
  refine ⟨hi,?_⟩
  calc
    _ ≤ C*(Ncount 0 (T i) : ℝ)/unfoldedCutoff (T i) :=
      div_le_div_of_nonneg_right (hu _ hw0.le hwidth) hD.le
    _ = C*((Ncount 0 (T i) : ℝ)/unfoldedCutoff (T i)) := mul_div_assoc _ _ _
    _ ≤ C*2 := mul_le_mul_of_nonneg_left hcount.le hC
    _ = 2*C := mul_comm _ _

end RiemannResearch.Analysis.MontgomeryPositiveGap
