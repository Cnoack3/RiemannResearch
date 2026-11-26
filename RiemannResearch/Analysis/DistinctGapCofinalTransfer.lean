import RiemannResearch.Analysis.MicroscopicDistinctGapCriterion

/-! A cofinal translated-window second-moment upper estimate and an eventual
affine lower bound on *distinct* positive gaps force the multiplicity correction
at every fixed width to tend to zero. The cofinal width absorbs the initial
bounded interval. This gives a reverse transfer to occurrence PCC without a
translated third-moment premise. The affine floor and moment bound are inputs. -/
noncomputable section
open Filter MeasureTheory Set intervalIntegral Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.DistinctOrdinatePCC
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance
open MontgomeryPositiveGap MicroscopicPositiveGapProjection ProjectedDistinctSpacing
open ZeroDPPCollisionLoss

private theorem indicator_mono (T a b : ℝ) : Monotone (fun q => gapIndicator T q a b) := by
  intro u v huv
  unfold gapIndicator
  dsimp only
  split_ifs <;> grind

theorem distinctPositiveMass_monotone {T : ℝ} (hT : 1 < T) :
    Monotone (distinctPositiveMass T) := by
  intro u v huv
  have hD : 0 ≤ normalizer T :=
    div_nonneg (mul_nonneg (zero_lt_one.trans hT).le (Real.log_pos hT).le) (by positivity)
  apply div_le_div_of_nonneg_right _ hD
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  by_cases h : a = b
  · simp [h]
  · simp only [if_neg h]
    exact indicator_mono T a b huv

theorem multiplicityCorrection_monotone {T : ℝ} (hT : 1 < T) :
    Monotone (multiplicityCorrection T) := by
  intro u v huv
  have hD : 0 ≤ normalizer T :=
    div_nonneg (mul_nonneg (zero_lt_one.trans hT).le (Real.log_pos hT).le) (by positivity)
  have hm (a : ℝ) (ha : a ∈ actualOrdinateSupport T) :
      (1 : ℝ) ≤ actualOrdinateMultiplicity T a := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    have hp : 0 < actualOrdinateMultiplicity T (copyOrdinate T i) :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
    exact_mod_cast (show 1 ≤ actualOrdinateMultiplicity T (copyOrdinate T i) from hp)
  apply div_le_div_of_nonneg_right _ hD
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  apply mul_le_mul_of_nonneg_left (indicator_mono T a b huv)
  have hab := mul_le_mul (hm a ha) (hm b hb) (by norm_num : (0:ℝ) ≤ 1)
    ((by norm_num : (0:ℝ) ≤ 1).trans (hm a ha))
  linarith only [hab]

/-- Rational lower floors only for widths beyond a threshold depending on
the additive tolerance. -/
def RationalDistinctTailAffineLower : Prop :=
  ∀ η : ℝ, 0 < η → ∃ U : ℝ, 0 ≤ U ∧ ∀ r : ℚ, 0 < r → U ≤ (r:ℝ) →
    ∀ᶠ T : ℝ in atTop, (r:ℝ) - (1/2 + η) ≤ distinctPositiveMass T r

theorem rationalDistinctTailAffineLower_of_affine (h : RationalDistinctAffineLower) :
    RationalDistinctTailAffineLower :=
  fun η hη => ⟨0, le_rfl, fun r hr _ => h r hr η hη⟩

private theorem realDistinctTailLower (h : RationalDistinctTailAffineLower)
    {η : ℝ} (hη : 0 < η) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ u : ℝ, U ≤ u →
      ∀ᶠ T : ℝ in atTop, u - (1/2 + η) ≤ distinctPositiveMass T u := by
  obtain ⟨U,hU,hh⟩ := h (η/2) (half_pos hη)
  refine ⟨U+η, by linarith, ?_⟩
  intro u hu
  obtain ⟨r,hr,hr'⟩ := exists_rat_btwn (show u-η/2 < u by linarith)
  have hrU : U ≤ (r:ℝ) := by linarith
  have hr0 : (0:ℝ) < (r:ℝ) := by linarith
  filter_upwards [hh r (by exact_mod_cast hr0) hrU, eventually_gt_atTop (1:ℝ)] with T hR hT
  have hm := distinctPositiveMass_monotone hT hr'.le
  linarith only [hr,hR,hm]

theorem occurrenceLargeGapAffineLower_of_distinctTail (h : RationalDistinctTailAffineLower) :
    LargeGapAffineLower := by
  intro η hη
  obtain ⟨U,hU,hh⟩ := realDistinctTailLower h hη
  refine ⟨U,hU,?_⟩
  intro u hu
  filter_upwards [hh u hu, eventually_gt_atTop (1:ℝ)] with T hQ hT
  rw [positiveMass_eq_distinct_add_correction]
  exact hQ.trans (le_add_of_nonneg_right (correction_sandwich hT u).1)

/-- The tail floor forces density one of simple critical occurrences and
critical-line occurrences under the cofinal upper moment estimate. -/
theorem density_one_of_distinctTail (h : RationalDistinctTailAffineLower)
    (hm : CofinalShortWindowSecondMomentUpper) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ)/(Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (criticalLineCount T : ℝ)/(Ncount 0 T : ℝ)) atTop (𝓝 1) :=
  density_one_of_largeGapAffineLower (occurrenceLargeGapAffineLower_of_distinctTail h) hm

/-- Monotone quadrature retaining a constant in the integration variable
which can depend on height. -/
private theorem integral_lower_with_constant
    {U R c η : ℝ} (hUR : U < R) (hη : 0 < η) (extra : ℝ → ℝ)
    (h : ∀ u : ℝ, U ≤ u → ∀ᶠ T : ℝ in atTop, u - c + extra T ≤ positiveGapMass T u) :
    ∀ᶠ T : ℝ in atTop, (R^2-U^2)/2 - c*(R-U) - η*(R-U) + extra T*(R-U) ≤
      ∫ u in U..R, positiveGapMass T u := by
  let S := R-U
  have hS : 0 < S := sub_pos.mpr hUR
  obtain ⟨n,hn⟩ := exists_nat_gt (S/η)
  have hn' : 0 < (n:ℝ) := (div_pos hS hη).trans hn
  have hn0 : 0 < n := Nat.cast_pos.mp hn'
  let d := S/(n:ℝ)
  have hd : 0 ≤ d := div_nonneg hS.le hn'.le
  have hdη : d ≤ η := by
    apply (div_le_iff₀ hn').mpr
    rw [mul_comm η]
    exact (div_le_iff₀ hη).mp hn.le
  let g : ℝ → ℝ := fun v => v + (U-c)
  have hg : Monotone g := by
    intro a b hab
    dsimp only [g]
    linarith only [hab]
  have hnode (k : ℕ) : ∀ᶠ T : ℝ in atTop,
      g ((k:ℝ)*d) ≤ positiveGapMass T ((k:ℝ)*d+U) - extra T := by
    filter_upwards [h _ (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg k) hd))] with T hT
    dsimp only [g]
    linarith only [hT]
  have hnodes : ∀ᶠ T : ℝ in atTop, ∀ k ∈ Finset.range n,
      g ((k:ℝ)*d) ≤ positiveGapMass T ((k:ℝ)*d+U) - extra T :=
    (Finset.eventually_all (Finset.range n)).mpr (fun k _ => hnode k)
  have hIg : (∫ v in (0:ℝ)..S, g v) = (R^2-U^2)/2 - c*(R-U) := by
    change (∫ v in (0:ℝ)..S, v+(U-c)) = _
    have hid : IntervalIntegrable (fun v : ℝ => v) volume 0 S :=
      continuous_id.intervalIntegrable 0 S
    have hc : IntervalIntegrable (fun _ : ℝ => U-c) volume 0 S := intervalIntegrable_const
    rw [intervalIntegral.integral_add hid hc, integral_id, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    dsimp only [S]
    ring
  have hinc : g S - g 0 = S := by dsimp only [g]; ring
  have hG := (integral_sub_gapMeshSum_bounds hg hS.le hn0).2
  rw [hIg,hinc] at hG
  filter_upwards [hnodes,eventually_gt_atTop (1:ℝ)] with T hgrid hT
  let p := fun v : ℝ => positiveGapMass T (v+U) - extra T
  have hp0 : Monotone (fun v : ℝ => positiveGapMass T (v+U)) := by
    intro a b hab
    exact positiveGapMass_mono hT (by linarith only [hab] : a+U ≤ b+U)
  have hp : Monotone p := fun _ _ hab => sub_le_sub_right (hp0 hab) _
  have hpI := (integral_sub_gapMeshSum_bounds hp hS.le hn0).1
  have hs : gapMeshSum g S n ≤ gapMeshSum p S n :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum hgrid) hd
  have hi : (∫ v in (0:ℝ)..S, p v) = (∫ u in U..R, positiveGapMass T u) - S * extra T := by
    change (∫ v in (0:ℝ)..S, positiveGapMass T (v+U) - extra T) = _
    have hIc : IntervalIntegrable (fun _ : ℝ => extra T) volume 0 S := intervalIntegrable_const
    have hIp : IntervalIntegrable (fun v : ℝ => positiveGapMass T (v+U)) volume 0 S :=
      hp0.intervalIntegrable
    rw [intervalIntegral.integral_sub hIp hIc,
      intervalIntegral.integral_comp_add_right, intervalIntegral.integral_const]
    simp only [S,zero_add, sub_add_cancel,sub_zero,smul_eq_mul]
  rw [hi] at hpI
  have he := mul_le_mul_of_nonneg_right hdη hS.le
  change S/(n:ℝ)*S ≤ η*S at he
  dsimp only [S] at hpI hG he
  nlinarith only [hpI, hs, he, hG]

/-- At each fixed positive width, persistent multiplicity correction would
exceed the cofinal moment budget on the entire interval to its right. -/
theorem multiplicityCorrection_tendsto_of_distinctTail
    (h : RationalDistinctTailAffineLower) (hm : CofinalShortWindowSecondMomentUpper)
    {q : ℝ} (hq : 0 < q) : Tendsto (fun T => multiplicityCorrection T q) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    exact ha.trans_le (correction_sandwich hT q).1
  · intro b hb
    let η := b/8
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨U,hU,hh⟩ := realDistinctTailLower h hη
    let W := max U q
    have hWU : U ≤ W := le_max_left _ _
    have hWq : q ≤ W := le_max_right _ _
    have hW : 0 ≤ W := hq.le.trans hWq
    obtain ⟨R,hR,hmom⟩ := hm η hη (max (2*W+1) (W^2/η))
    have hwide := (le_max_left (2*W+1) (W^2/η)).trans hR
    have hWR : W < R := by linarith
    have hR0 := hW.trans_lt hWR
    have hsmall : W^2 ≤ η*R := by
      rw [mul_comm]
      exact (div_le_iff₀ hη).mp ((le_max_right _ _).trans hR)
    have hlow := integral_lower_with_constant (c:=1/2+η) hWR hη
      (fun T => multiplicityCorrection T q) (by
        intro u hu
        filter_upwards [hh u (hWU.trans hu), eventually_gt_atTop (1:ℝ)] with T hz hT
        rw [positiveMass_eq_distinct_add_correction]
        exact add_le_add hz (multiplicityCorrection_monotone hT (hWq.trans hu)))
    have hcoll := collision_limit_of_largeGapAffineLower
      (occurrenceLargeGapAffineLower_of_distinctTail h) hm
    filter_upwards [hmom, hlow, hcoll.eventually_const_lt (show 1-η < 1 by linarith),
      eventually_gt_atTop (1:ℝ)] with T hM hL hC hT
    have hP := positiveGapMass_mono hT
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
      (f:=positiveGapMass T) (a:=0) (b:=W) (c:=R) hP.intervalIntegrable hP.intervalIntegrable
    have hI0 := intervalIntegral.integral_nonneg_of_forall (μ:=volume) hW
      (positiveGapMass_nonneg hT)
    rw [physicalTriangle_eq_collision_add_positive_gaps hT hR0.le] at hM
    change R*((actualCollision T:ℝ)/(T*Real.log T/(2*Real.pi))) +
      2*(∫ u in (0:ℝ)..R, positiveGapMass T u) ≤ R^2+η*R at hM
    change 1-η < (actualCollision T:ℝ)/(T*Real.log T/(2*Real.pi)) at hC
    have hC' := mul_lt_mul_of_pos_left hC hR0
    have htail : (1+4*η)*(R-W) ≤ (1+4*η)*R :=
      mul_le_mul_of_nonneg_left (sub_le_self _ hW) (by positivity)
    by_contra! hx
    have hblock := mul_le_mul_of_nonneg_right hx (sub_nonneg.mpr hWR.le)
    have hhalf := mul_le_mul_of_nonneg_left (show R ≤ 2*(R-W) by linarith only [hwide]) hb.le
    have hsmallb : 7*η*R < b*R := by
      apply mul_lt_mul_of_pos_right _ hR0
      dsimp only [η]
      linarith
    nlinarith only [hC',hM,hL,hsplit,hI0,hsmall,htail,hblock,hhalf,hsmallb]

/-- Reverse PCC transfer at fixed rational widths using the cofinal
second-moment upper estimate alone as the supplemental analytic hypothesis. -/
theorem positiveGapPCC_of_distinctLaw_cofinalUpper
    (hd : DistinctPositiveGapLaw) (hm : CofinalShortWindowSecondMomentUpper) : PositiveGapPCC := by
  apply positiveGapPCC_iff_rationalWidthLimits.mpr
  intro q hq
  have hz := multiplicityCorrection_tendsto_of_distinctTail
    (rationalDistinctTailAffineLower_of_affine (rationalDistinctAffineLower_of_law hd)) hm
    (show (0:ℝ) < (q:ℝ) by exact_mod_cast hq)
  exact (actual_tendsto_iff_distinct_of_correction hz).mpr (hd q hq)


/-- The affine floor is negative below one half, whereas a pair mass is
nonnegative. Integrating the floor from one half retains the strict positive
constant 1/4 in the triangle energy. Thus arbitrarily small relative upper
errors in the short-window hypothesis require arbitrarily large widths. -/
theorem cofinalUpper_of_distinctAffine (h : RationalDistinctAffineLower)
    (hm : ShortWindowSecondMomentUpper) : CofinalShortWindowSecondMomentUpper := by
  intro ε hε B
  have hBpos : 0 < |B|+1 := by positivity
  let η := min ε ((1/48)/(|B|+1))
  have hη : 0 < η := lt_min hε (div_pos (by norm_num) hBpos)
  have hηB : η*(|B|+1) ≤ 1/48 :=
    (le_div_iff₀ hBpos).mp (min_le_right ε _)
  obtain ⟨R,hR,hM⟩ := hm η hη
  have hR0 := zero_lt_one.trans_le hR
  have hUR : (1/2:ℝ) < R := by linarith
  have hfloor (u : ℝ) (hu : 1/2 ≤ u) :
      ∀ᶠ T : ℝ in atTop, u-(1/2+η) ≤ positiveGapMass T u := by
    obtain ⟨r,hr,hr'⟩ := exists_rat_btwn
      (show max 0 (u-η/2) < u by apply max_lt <;> linarith)
    have hr0 := (le_max_left 0 (u-η/2)).trans_lt hr
    have hru := (le_max_right 0 (u-η/2)).trans_lt hr
    filter_upwards [h r (by exact_mod_cast hr0) (η/2) (half_pos hη),
      eventually_gt_atTop (1:ℝ)] with T hdist hT
    have hpos := correction_sandwich hT (r:ℝ)
    have he := positiveMass_eq_distinct_add_correction T (r:ℝ)
    have hmono := positiveGapMass_mono hT hr'.le
    linarith only [hru,hdist,hpos.1,he,hmono]
  have hI := eventually_integral_positiveGapMass_lower_of_affine hUR hη hfloor
  have hC := collision_limit_of_rationalDistinctAffineLower h hm
  have hBR : B ≤ R := by
    by_contra! hrb
    have hηR : η*R ≤ 1/48 :=
      (mul_le_mul_of_nonneg_left (show R ≤ |B| + 1 by linarith [le_abs_self B]) hη.le).trans hηB
    have hf : ∀ᶠ T : ℝ in atTop, False := by
      filter_upwards [hI,hM,hC.eventually_const_lt (show 1-η < 1 by linarith),
        eventually_gt_atTop (1:ℝ)] with T hl hmom hc hT
      have hP := positiveGapMass_mono hT
      have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
        (f:=positiveGapMass T) (a:=0) (b:=1/2) (c:=R) hP.intervalIntegrable hP.intervalIntegrable
      have hI0 := intervalIntegral.integral_nonneg_of_forall (μ:=volume)
        (show (0:ℝ) ≤ 1/2 by norm_num) (positiveGapMass_nonneg hT)
      rw [physicalTriangle_eq_collision_add_positive_gaps hT hR0.le] at hmom
      change R*((actualCollision T:ℝ)/(T*Real.log T/(2*Real.pi))) +
        2*(∫ u in (0:ℝ)..R, positiveGapMass T u) ≤ R^2+η*R at hmom
      change 1-η < (actualCollision T:ℝ)/(T*Real.log T/(2*Real.pi)) at hc
      have hc' := mul_lt_mul_of_pos_left hc hR0
      nlinarith only [hc',hmom,hsplit,hI0,hl,hηR,hη]
    obtain ⟨_,he⟩ := hf.exists
    exact he
  refine ⟨R,hBR,?_⟩
  filter_upwards [hM] with T hT
  have herr := mul_le_mul_of_nonneg_right (show η ≤ ε from min_le_left _ _) hR0.le
  linarith only [hT,herr]

/-- The reverse implication in the distinct-height criterion requires only the
same one-sided short-window second-moment upper estimate as the density argument. -/
theorem positiveGapPCC_of_distinctLaw_shortUpper
    (hd : DistinctPositiveGapLaw) (hm : ShortWindowSecondMomentUpper) : PositiveGapPCC :=
  positiveGapPCC_of_distinctLaw_cofinalUpper hd
    (cofinalUpper_of_distinctAffine (rationalDistinctAffineLower_of_law hd) hm)

end RiemannResearch.Analysis.DistinctOrdinatePCC
