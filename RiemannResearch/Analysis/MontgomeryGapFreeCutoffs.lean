import RiemannResearch.Analysis.MontgomeryPrescribedArgumentWidth
import RiemannResearch.Analysis.ActualZeroHeightTransfer
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.GoodHeights
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Observation cutoffs with no forward boundary clipping

The local zero count and the finite-set separation lemma provide an empty
forward interval of fixed positive unfolded width in every sufficiently
high physical unit interval. On these cutoffs the signed clipping term
vanishes simultaneously for every smaller width and every center.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroWindowVariance ActualZeroCollisionCertificate

/-- An empty forward band makes the upper cutoff correction exactly zero,
regardless of the chosen center. -/
theorem normalizedWindowClipError_eq_zero_of_empty_forward {T R : ℝ} (hT : 1 < T)
    (hR : 0 ≤ R) (hhT : R / (Real.log T / (2 * Real.pi)) ≤ T)
    (hempty : Ncount T (T + R / (Real.log T / (2 * Real.pi))) = 0) (c : ℝ) :
    normalizedWindowClipError T R c = 0 := by
  let h := R / (Real.log T / (2 * Real.pi))
  have hh : 0 ≤ h := div_nonneg hR (div_nonneg (Real.log_pos hT).le (by positivity))
  unfold normalizedWindowClipError
  rw [actualCenteredMoment_clip_error_eq hh hhT]
  change (∫ t in (T-h)..T, (((Ncount t T : ℝ)-c)^2 - ((Ncount t (t+h) : ℝ)-c)^2)) / T = 0
  have he : (∫ t in (T-h)..T, (((Ncount t T : ℝ)-c)^2 - ((Ncount t (t+h) : ℝ)-c)^2)) = 0 := by
    calc
      _ = ∫ t in (T-h)..T, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (show T-h ≤ T by linarith)] at ht
        have hth : T ≤ t+h := by linarith only [ht.1]
        have hle : Ncount T (t+h) ≤ Ncount T (T+h) :=
          Ncount_mono le_rfl (by linarith only [ht.2])
        have hzero : Ncount T (t+h) = 0 := Nat.eq_zero_of_le_zero (hle.trans_eq hempty)
        change ((Ncount t T : ℝ)-c)^2 - ((Ncount t (t+h) : ℝ)-c)^2 = 0
        rw [Ncount_add ht.2 hth,hzero,add_zero,sub_self]
      _ = _ := by simp
  rw [he,zero_div]

/-- Every sufficiently high physical unit interval contains a cutoff with an
empty forward band of the same fixed positive unfolded width. All actual
zero ordinates, including off-line ones, enter the separation argument. -/
theorem exists_gapFree_unfolded_cutoffs :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ U : ℝ in atTop, ∃ T ∈ Icc U (U+1),
      1 < T ∧ B / (Real.log T / (2 * Real.pi)) ≤ 1 ∧
      Ncount T (T + B / (Real.log T / (2 * Real.pi))) = 0 := by
  classical
  obtain ⟨A,hA,hcount⟩ := exists_shortWindow_count_bound
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  let B := 1 / (8 * Real.pi * (4*A+1))
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with U hU hlogU
  let F := (zerosIn_finite U (U+2)).toFinset
  let S := F.image Complex.im
  have hcard : S.card ≤ Ncount U (U+2) := by
    apply (Finset.card_image_le : S.card ≤ F.card).trans
    rw [Ncount,finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite U (U+2))]
    change F.card ≤ ∑ z ∈ F, zeroMult z
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun z hz => zetaSeam.one_le_mult z
      (((zerosIn_finite U (U+2)).mem_toFinset.mp hz).1)
  obtain ⟨T,hUT,hTU,hfar⟩ := WeilEF.exists_far_point S U
  have hT : 1 < T := by linarith
  have ht : 0 < T := zero_lt_one.trans hT
  have hlogT : 1 ≤ Real.log T := hlogU.trans (Real.log_le_log (by linarith) hUT)
  have hlog₄ : Real.log (U+4) ≤ 2 * Real.log T := by
    calc Real.log (U+4) ≤ Real.log (T^2) := Real.log_le_log (by linarith) (by nlinarith)
         _ = _ := by rw [Real.log_pow]; norm_num
  have hcc : (S.card : ℝ) + 1 ≤ (4*A+1)*Real.log T := by
    have h₁ : (S.card : ℝ) ≤ Ncount U (U+2) := by exact_mod_cast hcard
    have h₂ := hcount U (U+2) (by linarith) (by linarith) le_rfl
    have h₃ := mul_le_mul_of_nonneg_left hlog₄ (show 0 ≤ 2*A by positivity)
    linarith only [h₁,h₂,h₃,hlogT]
  let h := B / (Real.log T / (2 * Real.pi))
  have hp : 0 < h := div_pos hB (div_pos (Real.log_pos hT) (by positivity))
  have hprod : h * Real.log T = 2 * Real.pi * B := by
    dsimp [h]
    field_simp [(Real.log_pos hT).ne',Real.pi_ne_zero]
  have hden : 0 < 2 * ((S.card : ℝ)+1) := by positivity
  have hsep : h < 1 / (2 * ((S.card : ℝ)+1)) := by
    apply (lt_div_iff₀ hden).2
    calc h * (2 * ((S.card : ℝ)+1)) ≤ h * (2 * ((4*A+1)*Real.log T)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcc (by norm_num)) hp.le
         _ = (h * Real.log T) * (2*(4*A+1)) := by ring
         _ = 1/2 := by
           rw [hprod]
           dsimp [B]
           field_simp [Real.pi_ne_zero,show 4*A+1 ≠ 0 by positivity]
           ring
         _ < _ := by norm_num
  have hh₁ : h ≤ 1 := hsep.le.trans (div_le_self zero_le_one (by
    linarith only [(Nat.cast_nonneg S.card : 0 ≤ (S.card : ℝ))]))
  refine ⟨T,⟨hUT,hTU⟩,hT,hh₁,?_⟩
  change Ncount T (T+h) = 0
  have he : zerosIn T (T+h) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hzeta,hlo,hhi⟩ := hz
    have hzF : z ∈ F := (zerosIn_finite U (U+2)).mem_toFinset.mpr
      ⟨hzeta,hUT.trans_lt hlo,by linarith only [hhi,hTU,hh₁]⟩
    have hzS : z.im ∈ S := Finset.mem_image.mpr ⟨z,hzF,rfl⟩
    have hbad := hfar _ hzS
    rw [abs_of_neg (sub_neg.mpr hlo)] at hbad
    linarith only [hhi,hsep,hbad]
  simp [Ncount,he]

/-- There is a single cutoff per high physical unit interval where all
smaller unfolded widths and every real center have zero boundary error. -/
theorem exists_unclipped_unfolded_cutoffs :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ U : ℝ in atTop, ∃ T ∈ Icc U (U+1),
      1 < T ∧ ∀ R ∈ Icc (0 : ℝ) B, ∀ c : ℝ, normalizedWindowClipError T R c = 0 := by
  obtain ⟨B,hB,he⟩ := exists_gapFree_unfolded_cutoffs
  refine ⟨B,hB,?_⟩
  filter_upwards [he] with U hU
  obtain ⟨T,hTU,hT,hh,hem⟩ := hU
  refine ⟨T,hTU,hT,?_⟩
  intro R hR c
  have hdom := div_le_div_of_nonneg_right hR.2
    (div_nonneg (Real.log_pos hT).le (show 0 ≤ 2 * Real.pi by positivity))
  have hz : Ncount T (T + R / (Real.log T / (2 * Real.pi))) ≤
      Ncount T (T + B / (Real.log T / (2 * Real.pi))) :=
    Ncount_mono le_rfl (by linarith only [hdom])
  exact normalizedWindowClipError_eq_zero_of_empty_forward hT hR.1 (hdom.trans (hh.trans hT.le))
    (Nat.eq_zero_of_le_zero (hz.trans_eq hem)) c


/-- The absolute collision main term and the positive-gap primitive account
for the whole prescribed-width argument variance, up to its signed clipping
term and an error of order the width times the zero-count normalizer. -/
theorem eventually_absolute_pureArgument_gap_error_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ R ∈ Ioc (0 : ℝ) 1,
      let D := T * Real.log T / (2 * Real.pi)
      |D * (pureArgumentWidthMoment T R / R) - (actualCollision T : ℝ) -
        (2 * D / R) * (∫ u in (0 : ℝ)..R, positiveGapMass T u) +
        (D/R) * normalizedWindowClipError T R R| ≤ K * (D * R) := by
  obtain ⟨B,hB,hfull⟩ := eventually_full_sub_pureArgument_quadratic
  refine ⟨3+2*B,by positivity,?_⟩
  have hm := (unfoldedWindowMean_tendsto 1).eventually
    (Ioo_mem_nhds (show (0:ℝ) < 1 by norm_num) (show (1:ℝ) < 2 by norm_num))
  filter_upwards [hfull,eventually_pureArgument_sub_collision_eq (show (0:ℝ) ≤ 1 by norm_num),
    hm,eventually_gt_atTop (1 : ℝ),Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)]
    with T hg he hmT hT hl R hr
  let D := T * Real.log T / (2 * Real.pi)
  let m := unfoldedWindowMean T 1
  let I := ∫ u in (0 : ℝ)..R, positiveGapMass T u
  let A := pureArgumentWidthMoment T R
  let F := fullArgumentWidthMoment T R - A
  let C := (actualCollision T : ℝ)
  let e := normalizedWindowClipError T R R
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hraw := he R ⟨hr.1.le,hr.2⟩
  change A - R*(C/D) = 2*I - R^2*(2*m-1) - e - F at hraw
  have hid : D*(A/R)-C-(2*D/R)*I+(D/R)*e =
      (D/R)*(-(R^2*(2*m-1))-F) := by
    calc D*(A/R)-C-(2*D/R)*I+(D/R)*e = (D/R)*(A-R*(C/D)-2*I+e) := by
           field_simp [hD.ne',hr.1.ne']
         _ = _ := by rw [hraw]; ring
  have hmean : |2*m-1| ≤ 3 := abs_le.mpr ⟨by linarith only [hmT.1],by linarith only [hmT.2]⟩
  have hlog2 : 1 ≤ (Real.log T)^2 := by nlinarith only [hl,sq_nonneg (Real.log T-1)]
  have hrate : B/T + B/(Real.log T)^2 ≤ 2*B := by
    linarith only [div_le_self hB hT.le,div_le_self hB hlog2]
  have hgam : |F| ≤ 2*B*R^2 := (hg R ⟨hr.1.le,hr.2⟩).trans
    (mul_le_mul_of_nonneg_right hrate (sq_nonneg _))
  have hrest : |-(R^2*(2*m-1))-F| ≤ (3+2*B)*R^2 := by
    calc _ ≤ |-(R^2*(2*m-1))| + |F| := abs_sub _ _
         _ ≤ R^2*3 + (2*B)*R^2 := by
           rw [abs_neg,abs_mul,abs_of_nonneg (sq_nonneg _)]
           exact add_le_add (mul_le_mul_of_nonneg_left hmean (sq_nonneg _)) hgam
         _ = _ := by ring
  change |D*(A/R)-C-(2*D/R)*I+(D/R)*e| ≤ (3+2*B)*(D*R)
  rw [hid,abs_mul,abs_of_pos (div_pos hD hr.1)]
  exact (mul_le_mul_of_nonneg_left hrest (div_pos hD hr.1).le).trans_eq (by
    field_simp [hr.1.ne'])

/-- At an appropriate cutoff in each sufficiently high physical unit interval
the actual integer collision count and positive-gap primitive recover the bare
variance with vanishing absolute error for any prescribed inverse-count-small
width. The endpoint term is exactly zero on the selected cutoffs. -/
theorem eventually_exists_absolute_pureArgument_gap_approx (r : ℝ → ℝ)
    (hr : ∀ᶠ T : ℝ in atTop, 0 < r T)
    (hscale : Tendsto (fun T : ℝ => (T * Real.log T / (2 * Real.pi)) * r T) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ U : ℝ in atTop, ∃ T ∈ Icc U (U+1), 1 < T ∧
      let D := T * Real.log T / (2 * Real.pi)
      |D * (pureArgumentWidthMoment T (r T) / r T) - (actualCollision T : ℝ) -
        (2 * D / r T) * (∫ u in (0 : ℝ)..r T, positiveGapMass T u)| < ε := by
  obtain ⟨B,hB,hgood⟩ := exists_unclipped_unfolded_cutoffs
  obtain ⟨K,hK,he⟩ := eventually_absolute_pureArgument_gap_error_le
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
  have hsmall : Tendsto (fun T : ℝ => K * ((T * Real.log T / (2 * Real.pi)) * r T))
      atTop (𝓝 0) := by simpa using hscale.const_mul K
  obtain ⟨t,ht⟩ := eventually_atTop.mp (he.and (hr.and ((hr₀.eventually_lt_const
    (lt_min hB zero_lt_one)).and (hsmall.eventually_lt_const hε))))
  filter_upwards [hgood,eventually_ge_atTop t] with U hU hot
  obtain ⟨T,hTU,hT,hclip⟩ := hU
  obtain ⟨hbound,hpos,hmin,hsmallT⟩ := ht T (hot.trans hTU.1)
  have hRB := (lt_min_iff.mp hmin).1.le
  have hR1 := (lt_min_iff.mp hmin).2.le
  have hest := hbound (r T) ⟨hpos,hR1⟩
  dsimp only at hest
  rw [hclip (r T) ⟨hpos.le,hRB⟩ (r T),mul_zero,add_zero] at hest
  exact ⟨T,hTU,hT,hest.trans_lt hsmallT⟩

end RiemannResearch.Analysis.MontgomeryPositiveGap
