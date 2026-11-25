import RiemannResearch.Analysis.MontgomeryGapFreeCutoffs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The measure of cutoff heights with a nonempty forward zero band

On every sufficiently high physical unit interval, a forward band of
unfolded width b ≤ 1 reaches an actual zero ordinate on a set of cutoff
heights of measure at most K b. The exceptional set estimate is uniform
in the unit interval and in b. It gives an absolute collision-scale
approximation to the bare variance on almost the entire interval when
the prescribed width is o(1/D).
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroWindowVariance ActualZeroCollisionCertificate

/-- Physical heights in a unit interval at which some actual zero occurrence
lies inside the forward band. -/
def exceptionalForwardCutoffs (U b : ℝ) : Set ℝ :=
  {T ∈ Icc U (U+1) | Ncount T (T+b/(Real.log T/(2*Real.pi))) ≠ 0}

/-- Uniform outer-measure estimate for the heights at which any zero can
affect the upper clipping boundary. -/
theorem eventually_volume_exceptionalForwardCutoffs_le :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ U : ℝ in atTop, ∀ b ∈ Icc (0:ℝ) 1,
      volume (exceptionalForwardCutoffs U b) ≤ ENNReal.ofReal (K*b) := by
  classical
  obtain ⟨A,hA,hcount⟩ := exists_shortWindow_count_bound
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  refine ⟨8*Real.pi*A,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.pi)] with U hU hlogU b hb
  let F := (zerosIn_finite U (U+2)).toFinset
  let w := b/(Real.log U/(2*Real.pi))
  have hu : 0 < U := by linarith only [hU]
  have hlu : 0 < Real.log U := (by positivity : 0 < 2*Real.pi).trans_le hlogU
  have hw : 0 ≤ w := div_nonneg hb.1 (div_pos hlu (by positivity)).le
  have hw₁ : w ≤ 1 := hb.2.trans' (div_le_self hb.1 ((le_div_iff₀ (by positivity)).mpr
    (by simpa only [one_mul] using hlogU)))
  have hcover : exceptionalForwardCutoffs U b ⊆ ⋃ z ∈ F, Icc (z.im-w) z.im := by
    intro T hT
    obtain ⟨hUT,hbad⟩ := hT
    let h := b/(Real.log T/(2*Real.pi))
    have hlt : 0 < Real.log T := hlu.trans_le (Real.log_le_log hu hUT.1)
    have hhw : h ≤ w := div_le_div_of_nonneg_left hb.1 (div_pos hlu (by positivity))
      (div_le_div_of_nonneg_right (Real.log_le_log hu hUT.1) (by positivity))
    have hne : (zerosIn T (T+h)).Nonempty := by
      apply Set.nonempty_iff_ne_empty.mpr
      intro he
      exact hbad (by change Ncount T (T+h) = 0; simp [Ncount,he])
    obtain ⟨z,hz,hlo,hhi⟩ := hne
    have hzF : z ∈ F := (zerosIn_finite U (U+2)).mem_toFinset.mpr
      ⟨hz,hUT.1.trans_lt hlo,by linarith only [hhi,hhw,hw₁,hUT.2]⟩
    exact Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hzF,⟨by linarith only [hhi,hhw],hlo.le⟩⟩⟩
  have hcard : F.card ≤ Ncount U (U+2) := by
    rw [Ncount,finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite U (U+2))]
    change F.card ≤ ∑ z ∈ F, zeroMult z
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun z hz => zetaSeam.one_le_mult z
      (((zerosIn_finite U (U+2)).mem_toFinset.mp hz).1)
  have hlog₄ : Real.log (U+4) ≤ 2*Real.log U := by
    calc _ ≤ Real.log (U^2) := Real.log_le_log (by linarith) (by nlinarith only [hU,sq_nonneg (U-3)])
         _ = _ := by rw [Real.log_pow]; norm_num
  have hc : (F.card:ℝ) ≤ 4*A*Real.log U := by
    have h₁ : (F.card:ℝ) ≤ Ncount U (U+2) := by exact_mod_cast hcard
    have h₂ := hcount U (U+2) (by linarith) (by linarith) le_rfl
    have h₃ := mul_le_mul_of_nonneg_left hlog₄ (show 0 ≤ 2*A by positivity)
    linarith only [h₁,h₂,h₃]
  have hs : (F.card:ℝ)*w ≤ (8*Real.pi*A)*b := by
    calc _ ≤ 4*A*Real.log U*w := mul_le_mul_of_nonneg_right hc hw
         _ = _ := by dsimp only [w]; field_simp [hlu.ne',Real.pi_ne_zero] <;> ring
  calc
    _ ≤ volume (⋃ z ∈ F, Icc (z.im-w) z.im) := measure_mono hcover
    _ ≤ ∑ z ∈ F, volume (Icc (z.im-w) z.im) := measure_biUnion_finset_le _ _
    _ = ENNReal.ofReal ((F.card:ℝ)*w) := by
      simp only [Real.volume_Icc,sub_sub_cancel,Finset.sum_const,nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hs

/-- For every positive width tending to zero, the measure of cutoff heights
where any center has a nonzero clipping error tends to zero on each high
physical unit interval. -/
theorem eventually_volume_nonzero_clip_le (r : ℝ → ℝ)
    (hr₀ : Tendsto r atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ U : ℝ in atTop,
      volume {T ∈ Icc U (U+1) | ∃ R ∈ Icc (0:ℝ) (r T), ∃ c : ℝ,
        normalizedWindowClipError T R c ≠ 0} ≤ ENNReal.ofReal ε := by
  obtain ⟨K,hK,hbad⟩ := eventually_volume_exceptionalForwardCutoffs_le
  let b := min 1 (ε/K)
  have hb : 0 < b := lt_min zero_lt_one (div_pos hε hK)
  have hb₁ : b ≤ 1 := min_le_left _ _
  have hKb : K*b ≤ ε := by
    calc _ ≤ K*(ε/K) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
         _ = _ := by field_simp [hK.ne']
  obtain ⟨t,ht⟩ := eventually_atTop.mp ((hr₀.eventually_lt_const hb).and
    ((eventually_gt_atTop (1:ℝ)).and (Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.pi))))
  filter_upwards [hbad,eventually_ge_atTop t] with U hU h₀
  apply le_trans _ ((hU b ⟨hb.le,hb₁⟩).trans (ENNReal.ofReal_le_ofReal hKb))
  apply measure_mono
  intro T hT
  obtain ⟨hUT,R,hR,c,hclip⟩ := hT
  obtain ⟨hsmall,hT,hlog⟩ := ht T (h₀.trans hUT.1)
  refine ⟨hUT,?_⟩
  intro he
  have hden : 1 ≤ Real.log T/(2*Real.pi) := (le_div_iff₀ (by positivity)).mpr
    (by simpa only [one_mul] using hlog)
  have hhh : R/(Real.log T/(2*Real.pi)) ≤ T :=
    (div_le_self hR.1 hden).trans (hR.2.trans (hsmall.le.trans (hb₁.trans hT.le)))
  have hcount : Ncount T (T+R/(Real.log T/(2*Real.pi))) ≤
      Ncount T (T+b/(Real.log T/(2*Real.pi))) := Ncount_mono le_rfl
    (add_le_add_right (div_le_div_of_nonneg_right (hR.2.trans hsmall.le) (zero_le_one.trans hden)) T)
  exact hclip (normalizedWindowClipError_eq_zero_of_empty_forward hT hR.1 hhh
    (Nat.eq_zero_of_le_zero (hcount.trans_eq he)) c)

/-- The absolute bare-variance error exceeds a given tolerance on a set of
asymptotically vanishing measure in every sufficiently high unit interval.
The width schedule need not be monotone or measurable. -/
theorem eventually_volume_absolute_argument_gap_error_le (r : ℝ → ℝ)
    (hr : ∀ᶠ T : ℝ in atTop, 0 < r T)
    (hscale : Tendsto (fun T : ℝ => (T*Real.log T/(2*Real.pi))*r T) atTop (𝓝 0))
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ U : ℝ in atTop, volume {T ∈ Icc U (U+1) |
      let D := T*Real.log T/(2*Real.pi)
      ε ≤ |D*(pureArgumentWidthMoment T (r T)/r T) - (actualCollision T:ℝ) -
        (2*D/r T)*(∫ u in (0:ℝ)..r T, positiveGapMass T u)|} ≤ ENNReal.ofReal δ := by
  have hr₀ : Tendsto r atTop (𝓝 0) := by
    apply squeeze_zero' (hr.mono (fun _ h => h.le)) _ hscale
    filter_upwards [hr,eventually_ge_atTop (2*Real.pi),Real.tendsto_log_atTop.eventually_ge_atTop
      (1:ℝ)] with T ht hT hl
    have ht₀ : 0 ≤ T := by linarith only [hT,Real.pi_pos]
    have hlog := mul_le_mul_of_nonneg_left hl ht₀
    have hD : 1 ≤ T * Real.log T / (2 * Real.pi) := (le_div_iff₀ (by positivity)).2 (by
      calc 1 * (2*Real.pi) = 2*Real.pi := one_mul _
           _ ≤ T := hT
           _ ≤ T * Real.log T := by simpa only [mul_one] using hlog)
    simpa using mul_le_mul_of_nonneg_right hD ht.le
  obtain ⟨K,hK,hbound⟩ := eventually_absolute_pureArgument_gap_error_le
  have hlim : Tendsto (fun T : ℝ => K*((T*Real.log T/(2*Real.pi))*r T)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hscale.const_mul K
  obtain ⟨t,ht⟩ := eventually_atTop.mp
    (hbound.and (hr.and ((hr₀.eventually_lt_const zero_lt_one).and (hlim.eventually_lt_const hε))))
  filter_upwards [eventually_volume_nonzero_clip_le r hr₀ hδ,eventually_ge_atTop t] with U hu hU
  apply le_trans _ hu
  apply measure_mono
  intro T hT
  obtain ⟨hTU,herr⟩ := hT
  obtain ⟨hb,hpos,hs,hex⟩ := ht T (hU.trans hTU.1)
  refine ⟨hTU,r T,⟨hpos.le,le_rfl⟩,r T,?_⟩
  intro he
  have h := hb (r T) ⟨hpos,hs.le⟩
  dsimp only at h herr
  rw [he,mul_zero,add_zero] at h
  exact (not_lt_of_ge herr) (h.trans_lt hex)

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_volume_exceptionalForwardCutoffs_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_volume_exceptionalForwardCutoffs_le

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_volume_nonzero_clip_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_volume_nonzero_clip_le

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_volume_absolute_argument_gap_error_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_volume_absolute_argument_gap_error_le

end RiemannResearch.Analysis.MontgomeryPositiveGap
