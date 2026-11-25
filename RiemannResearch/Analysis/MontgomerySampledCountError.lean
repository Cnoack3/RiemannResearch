import RiemannResearch.Analysis.MontgomeryMesoscopicGapCount
import RiemannResearch.Analysis.MontgomeryWindowVarianceCriterion

/-! # Riemann–von Mangoldt increments sampled at actual ordinate occurrences

The elementary count main term contributes one unit per unfolded unit width
throughout every moving range occupying a vanishing fraction of the cutoff.
This remains true for fixed and shrinking positive widths. The signed
difference of the actual Riemann–von Mangoldt errors at each row's endpoints
contains the arithmetic correction.
-/

noncomputable section
open Filter Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate DyadicZeroWasserstein

/-- Normalized sum of increments of a height function over the actual forward
ordinate windows. Clipping, multiplicity and the lower endpoint agree with
the strictly positive gap count. -/
def sampledHeightIncrement (f : ℝ → ℝ) (T R : ℝ) : ℝ :=
  (∑ i : Copies T, (f (min T (copyOrdinate T i+R/unfoldingScale T)) - f (copyOrdinate T i))) /
    unfoldedCutoff T

/-- Sampled increments of the exact cumulative Riemann–von Mangoldt error. -/
def sampledRvMError (T R : ℝ) : ℝ := sampledHeightIncrement countError T R

private theorem scale_pos {T : ℝ} (hT : 1 < T) : 0 < unfoldingScale T :=
  div_pos (Real.log_pos hT) (by positivity)

/-- The actual positive-gap count splits exactly into its smooth main-term
increments and its signed count-error increments, including boundary rows. -/
theorem positiveGapMass_eq_sampled_main_add_RvMError {T R : ℝ} (hT : 1 < T) (hR : 0 < R) :
    positiveGapMass T R = sampledHeightIncrement countMain T R + sampledRvMError T R := by
  have hp := positiveGapMass_eq_ordinate_window_counts hT (div_pos hR (scale_pos hT))
  rw [div_mul_cancel₀ _ (scale_pos hT).ne'] at hp
  rw [hp,sampledRvMError,sampledHeightIncrement,sampledHeightIncrement,← add_div,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let t := copyOrdinate T i
  let u := min T (t+R/unfoldingScale T)
  have ht := (mem_cutoff.mp i.1.property).2.1
  have htu : t ≤ u := le_min (mem_cutoff.mp i.1.property).2.2
    (le_add_of_nonneg_right (div_pos hR (scale_pos hT)).le)
  have hn := Ncount_add (a:=0) (b:=t) (c:=u) ht.le htu
  change (Ncount t u : ℝ) = (countMain u-countMain t)+(countError u-countError t)
  unfold countError
  rw [hn,Nat.cast_add]
  ring

private def smoothRow (T H : ℝ) (i : Copies T) : ℝ :=
  (countMain (min T (copyOrdinate T i + H))-countMain (copyOrdinate T i)) /
    (H*unfoldingScale T)

private theorem smoothRow_value {T H : ℝ} (hT : 1 < T) (hH : 0 < H) (i : Copies T) :
    let t := copyOrdinate T i
    let u := min T (t+H)
    u = t ∨ ∃ s ∈ Ioo t u,
      smoothRow T H i = ((u-t)/H) * (Real.log (s/(2*Real.pi))/Real.log T) := by
  dsimp only
  let t := copyOrdinate T i
  let u := min T (t+H)
  have ht := (mem_cutoff.mp i.1.property).2.1
  have htu : t ≤ u := le_min (mem_cutoff.mp i.1.property).2.2 (le_add_of_nonneg_right hH.le)
  rcases htu.eq_or_lt with he | he
  · exact Or.inl he.symm
  right
  obtain ⟨s,hs,hd⟩ := exists_hasDerivAt_eq_slope countMain DyadicZeroWasserstein.slope he
    (fun v hv => (countMain_deriv (ht.trans_le hv.1)).continuousAt.continuousWithinAt)
    (fun v hv => countMain_deriv (ht.trans hv.1))
  refine ⟨s,hs,?_⟩
  change (countMain u-countMain t)/(H*unfoldingScale T) = _
  have h := (eq_div_iff (sub_pos.mpr he).ne').mp hd
  rw [← h]
  unfold DyadicZeroWasserstein.slope unfoldingScale
  field_simp [Real.pi_ne_zero,hH.ne',(Real.log_pos hT).ne'] <;> ring

private theorem eventually_smooth_rows_bounded {H : ℝ → ℝ} (hH : ∀ᶠ T : ℝ in atTop, 0 < H T) :
    ∀ᶠ T : ℝ in atTop, ∀ i : Copies T, |smoothRow T (H T) i - 1| ≤ 2+1 := by
  obtain ⟨v,hv,hvLow⟩ := exists_ordinate_floor
  let a := Real.log (2*Real.pi)
  filter_upwards [hH,eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (|Real.log v|+|a|)]
    with T hHT hT hL i
  let t := copyOrdinate T i
  let u := min T (t+H T)
  have hlog := Real.log_pos hT
  rcases smoothRow_value hT hHT i with h | ⟨s,hs,hrow⟩
  · simp [smoothRow,h]
  have hlen : u-t ≤ H T := by linarith only [min_le_right T (t+H T)]
  have hratio : |(u-t)/H T| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr (hs.1.trans hs.2).le) hHT.le)]
    exact (div_le_one hHT).mpr hlen
  have hs₀ : 0 < s := hv.trans (lt_of_le_of_lt (hvLow T i) hs.1)
  have hlogs : |Real.log (s/(2*Real.pi))/Real.log T| ≤ 2 := by
    rw [abs_div,abs_of_pos hlog,Real.log_div hs₀.ne' (by positivity : 2*Real.pi ≠ 0)]
    apply (div_le_iff₀ hlog).mpr
    have hlo := Real.log_le_log hv ((hvLow T i).trans hs.1.le)
    have hhi := Real.log_le_log hs₀ (hs.2.le.trans (min_le_left _ _))
    dsimp only [a] at hL
    exact abs_le.mpr ⟨by linarith only [hlo,hL,neg_abs_le (Real.log v),le_abs_self (Real.log (2*Real.pi)),hlog],
      by linarith only [hhi,hL,abs_nonneg (Real.log v),neg_abs_le (Real.log (2*Real.pi))]⟩
  apply (abs_sub _ _).trans
  rw [hrow,abs_mul,abs_one]
  exact add_le_add (by simpa using mul_le_mul hratio hlogs (abs_nonneg _) zero_le_one) le_rfl

private theorem eventually_smooth_interior {H : ℝ → ℝ}
    (hH : ∀ᶠ T : ℝ in atTop, 0 < H T) (hHT : Tendsto (fun T : ℝ => H T/T) atTop (𝓝 0))
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ i : Copies T, δ*T ≤ copyOrdinate T i →
      copyOrdinate T i ≤ (1-δ)*T → |smoothRow T (H T) i-1| ≤ ε := by
  let K := |Real.log δ| + |Real.log (2*Real.pi)|
  have hlim : Tendsto (fun T : ℝ => K/Real.log T) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul K
  filter_upwards [hH,eventually_gt_atTop (1:ℝ),hHT.eventually_lt_const hδ,hlim.eventually_lt_const hε]
    with T hH₀ hT hsmall hεT i hleft hright
  let t := copyOrdinate T i
  have ht := zero_lt_one.trans hT
  have hlog := Real.log_pos hT
  have hcut : min T (t+H T) = t+H T := min_eq_right (by
    have ha := (div_lt_iff₀ ht).mp hsmall
    nlinarith only [ha,hright])
  rcases smoothRow_value hT hH₀ i with h | ⟨s,hs,hrow⟩
  · change min T (t+H T) = t at h
    rw [hcut] at h
    linarith only [h,hH₀]
  change s ∈ Ioo t (min T (t+H T)) at hs
  change smoothRow T (H T) i = ((min T (t+H T)-t)/H T)*(Real.log (s/(2*Real.pi))/Real.log T) at hrow
  rw [hcut,add_sub_cancel_left,div_self hH₀.ne',one_mul] at hrow
  have hsp := (mul_pos hδ ht).trans (lt_of_le_of_lt hleft hs.1)
  have hlo := Real.log_le_log (mul_pos hδ ht) (hleft.trans hs.1.le)
  rw [Real.log_mul hδ.ne' ht.ne'] at hlo
  have hup := Real.log_le_log hsp (hs.2.le.trans (min_le_left _ _))
  have hbound : |Real.log (s/(2*Real.pi))-Real.log T| ≤ K := by
    rw [Real.log_div hsp.ne' (by positivity : 2*Real.pi ≠ 0)]
    dsimp only [K]
    exact abs_le.mpr ⟨by linarith only [hlo,neg_abs_le (Real.log δ),le_abs_self (Real.log (2*Real.pi))],
      by linarith only [hup,neg_abs_le (Real.log (2*Real.pi)),abs_nonneg (Real.log δ)]⟩
  rw [hrow, ← div_self hlog.ne', ← sub_div, abs_div, abs_of_pos hlog]
  exact (div_le_div_of_nonneg_right hbound hlog.le).trans hεT.le

/-- On all moving positive widths occupying a vanishing fraction of the
cutoff, the smooth increments sampled at actual occurrences contribute
one per unfolded width, including fixed and shrinking widths. -/
theorem sampled_main_increment_div_width_tendsto {R : ℝ → ℝ}
    (hR : ∀ᶠ T : ℝ in atTop, 0 < R T)
    (hsmall : Tendsto (fun T : ℝ => R T/unfoldedCutoff T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => sampledHeightIncrement countMain T (R T)/R T) atTop (𝓝 1) := by
  let H := fun T : ℝ => R T/unfoldingScale T
  have hH : ∀ᶠ T : ℝ in atTop, 0 < H T := by
    filter_upwards [hR,eventually_gt_atTop (1:ℝ)] with T hr ht
    exact div_pos hr (scale_pos ht)
  have hHT : Tendsto (fun T : ℝ => H T/T) atTop (𝓝 0) := by
    apply hsmall.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    dsimp only [H,unfoldingScale,unfoldedCutoff]
    field_simp [Real.pi_ne_zero,(Real.log_pos hT).ne',(zero_lt_one.trans hT).ne'] <;> ring
  have hh := ordinateRowMean_tendsto_of_interior (f := fun T i => smoothRow T (H T) i)
    ⟨2,by norm_num,eventually_smooth_rows_bounded hH⟩ (fun hδ hε => eventually_smooth_interior hH hHT hδ hε)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  have he : H T*unfoldingScale T=R T := div_mul_cancel₀ _ (scale_pos hT).ne'
  dsimp only [smoothRow,sampledHeightIncrement]
  rw [he,← Finset.sum_div]
  change (_ / R T) / unfoldedCutoff T = (_ / unfoldedCutoff T)/R T
  dsimp only [H]
  ring

/-- At every eventually positive submacroscopic width the entire departure
from asymptotic unit density is equivalent to the signed sampled count-error
increment at that width. -/
theorem positiveGapMass_div_width_tendsto_iff_sampledRvMError {R : ℝ → ℝ} {ℓ : ℝ}
    (hR : ∀ᶠ T : ℝ in atTop, 0 < R T)
    (hsmall : Tendsto (fun T : ℝ => R T/unfoldedCutoff T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => positiveGapMass T (R T)/R T) atTop (𝓝 ℓ) ↔
      Tendsto (fun T : ℝ => sampledRvMError T (R T)/R T) atTop (𝓝 (ℓ-1)) := by
  have hmain := sampled_main_increment_div_width_tendsto hR hsmall
  constructor
  · intro hp
    apply (hp.sub hmain).congr'
    filter_upwards [hR,eventually_gt_atTop (1:ℝ)] with T hr ht
    rw [positiveGapMass_eq_sampled_main_add_RvMError ht hr,add_div,add_sub_cancel_left]
  · intro he
    have h := hmain.add he
    rw [show 1+(ℓ-1)=ℓ by ring] at h
    apply h.congr'
    filter_upwards [hR,eventually_gt_atTop (1:ℝ)] with T hr ht
    rw [positiveGapMass_eq_sampled_main_add_RvMError ht hr,add_div]

private theorem fixed_main_increment_tendsto {R : ℝ} (hR : 0 < R) :
    Tendsto (fun T : ℝ => sampledHeightIncrement countMain T R) atTop (𝓝 R) := by
  have hD : Tendsto unfoldedCutoff atTop atTop :=
    (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop).atTop_div_const (by positivity)
  have hs : Tendsto (fun T : ℝ => R/unfoldedCutoff T) atTop (𝓝 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.comp hD).const_mul R
  have h := (sampled_main_increment_div_width_tendsto (R:=fun _ => R) (Eventually.of_forall fun _ => hR)
    hs).mul_const R
  simpa only [div_mul_cancel₀ _ hR.ne',one_mul] using h

/-- The fixed-width two-ordinate conjecture is equivalent to the signed
RvM error sampled at the endpoints of the actual zero windows. Its target
is the negative integrated sine-square deficit. -/
theorem positiveGapPCC_iff_sampledRvMError :
    PositiveGapPCC ↔ ∀ R : ℝ, 0 < R →
      Tendsto (fun T => sampledRvMError T R) atTop (𝓝 (sineGapMass R-R)) := by
  constructor
  · intro h R hR
    have hp : Tendsto (fun T => positiveGapMass T R) atTop (𝓝 (sineGapMass R)) := by
      apply Metric.tendsto_nhds.mpr
      intro η hη
      filter_upwards [h R R hR le_rfl (η/2) (by linarith)] with T ht
      simpa only [Real.dist_eq] using (ht R ⟨le_rfl,le_rfl⟩).trans_lt (by linarith : η/2 < η)
    apply (hp.sub (fixed_main_increment_tendsto hR)).congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
    rw [positiveGapMass_eq_sampled_main_add_RvMError ht hR,add_sub_cancel_left]
  · intro h
    apply positiveGapPCC_of_pointwise
    intro R hR
    have hp := (fixed_main_increment_tendsto hR).add (h R hR)
    rw [show R+(sineGapMass R-R) = sineGapMass R by ring] at hp
    apply hp.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T ht
    exact (positiveGapMass_eq_sampled_main_add_RvMError ht hR).symm

/-- Pointwise positive-gap limits on the positive rational widths determine
the compact-uniform conjecture by monotonicity of the actual counts and the
unit Lipschitz bound on the sine mass. -/
theorem positiveGapPCC_iff_rationalWidthLimits :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ => positiveGapMass T q)
      atTop (𝓝 (sineGapMass q)) := by
  constructor
  · intro h q hq
    have hqr : 0 < (q : ℝ) := by exact_mod_cast hq
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [h q q hqr le_rfl (ε/2) (half_pos hε)] with T ht
    rw [Real.dist_eq]
    exact (ht q ⟨le_rfl,le_rfl⟩).trans_lt (half_lt_self hε)
  · intro h
    apply positiveGapPCC_of_pointwise
    intro x hx
    apply tendsto_order.2
    constructor
    · intro l hl
      obtain ⟨a,ha,hax⟩ := exists_rat_btwn
        (show max 0 (x-(sineGapMass x-l)) < x from max_lt hx (by linarith only [hl]))
      have ha₀ := (le_max_left _ _).trans_lt ha
      have hl' : l < sineGapMass a := by
        linarith only [(sineGapMass_increment_bounds hax.le).2,(le_max_right _ _).trans_lt ha]
      filter_upwards [(h a (by exact_mod_cast ha₀)).eventually_const_lt hl',eventually_gt_atTop (1:ℝ)]
        with T ht hT
      exact ht.trans_le (positiveGapMass_mono hT hax.le)
    · intro u hu
      obtain ⟨b,hxb,hb⟩ := exists_rat_btwn (show x < x+(u-sineGapMass x) by linarith only [hu])
      have hbu : sineGapMass b < u := by linarith only [(sineGapMass_increment_bounds hxb.le).2,hb]
      have hb₀ := hx.trans hxb
      filter_upwards [(h b (by exact_mod_cast hb₀)).eventually_lt_const hbu,eventually_gt_atTop (1:ℝ)]
        with T ht hT
      exact (positiveGapMass_mono hT hxb.le).trans_lt ht

/-- The countable closure obligations are exact signed RvM-error increments
sampled at the actual zeros, one limit at each positive rational width. -/
theorem positiveGapPCC_iff_rationalSampledRvMError :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ => sampledRvMError T q)
      atTop (𝓝 (sineGapMass q-q)) := by
  constructor
  · intro h q hq
    exact positiveGapPCC_iff_sampledRvMError.mp h q (by exact_mod_cast hq)
  · intro h
    apply positiveGapPCC_iff_rationalWidthLimits.mpr
    intro q hq
    have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
    have ht := (fixed_main_increment_tendsto hqr).add (h q hq)
    rw [show (q:ℝ)+(sineGapMass q-q) = sineGapMass q by ring] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact (positiveGapMass_eq_sampled_main_add_RvMError hT hqr).symm

end RiemannResearch.Analysis.MontgomeryPositiveGap

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapPCC_iff_rationalSampledRvMError' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_rationalSampledRvMError

end RiemannResearch.Analysis.MontgomeryPositiveGap
