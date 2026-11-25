import RiemannResearch.Analysis.MontgomerySampledCountError
import RiemannResearch.Analysis.MontgomeryLocalMass
import Mathlib.Algebra.Order.Chebyshev

/-! # Signed argument increments at the zero ordinates

The exact gamma counting function and the elementary Riemann–von Mangoldt
main term have uniformly bounded difference of slopes above the smallest
positive ordinate. Sampling every forward window at the actual ordinate
occurrences therefore changes its signed error by O(R/D(T)), uniformly
in its unfolded width R.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroDiscrepancy DyadicZeroWasserstein

private def gammaMainRemainder (t : ℝ) : ℝ := smoothCount t-countMain t

private theorem exists_gammaMain_remainder_Lipschitz {v : ℝ} (hv : 0 < v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t u : ℝ, v ≤ t → t ≤ u →
      |gammaMainRemainder u-gammaMainRemainder t| ≤ K*(u-t) := by
  let d := fun t => Zeta23.mu t - DyadicZeroWasserstein.slope t
  let U := max 1 v
  have hμ := RvM.mu_continuous gammaFacts
  have hc (t : ℝ) (ht : 0 < t) : ContinuousAt d t := by
    let g := fun u : ℝ => u/(2*Real.pi)
    have hz : g t ≠ 0 := div_ne_zero ht.ne' (by positivity)
    have hh : ContinuousAt g t := (continuous_id.div_const _).continuousAt
    have hlog : ContinuousAt Real.log (g t) := Real.continuousAt_log hz
    exact hμ.continuousAt.sub ((hlog.comp hh).div_const _)
  have hc' : ContinuousOn d (Icc v U) :=
    fun t ht => (hc t (hv.trans_le ht.1)).continuousWithinAt
  have hU : v ≤ U := le_max_right _ _
  obtain ⟨z,_,hz⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hU) hc'.abs
  obtain ⟨C,hC⟩ := gammaFacts.stirling
  let K := max |d z| |C|
  refine ⟨K,le_max_of_le_left (abs_nonneg _),?_⟩
  have hbound (s : ℝ) (hs : v ≤ s) : |d s| ≤ K := by
    by_cases h : s ≤ U
    · exact (hz (show s ∈ Icc v U from ⟨hs,h⟩)).trans (le_max_left _ _)
    have h₁ : 1 ≤ s := (le_max_left 1 v).trans (le_of_not_ge h)
    have hs₀ := hv.trans_le hs
    have he := hC s (by simpa only [abs_of_pos hs₀] using h₁)
    rw [abs_of_pos hs₀] at he
    have hsq : 1 ≤ s^2 := by nlinarith only [h₁,mul_nonneg (sub_nonneg.mpr h₁) hs₀.le]
    have ha : C/s^2 ≤ |C| := (div_le_div_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
      (div_le_self (abs_nonneg _) hsq)
    exact (by simpa only [d,DyadicZeroWasserstein.slope,div_eq_mul_inv,one_mul,mul_comm] using
      he.trans ha : |d s| ≤ |C|).trans (le_max_right _ _)
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt gammaMainRemainder (d t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hμ.intervalIntegrable 0 t)
      hμ.stronglyMeasurable.stronglyMeasurableAtFilter hμ.continuousAt).sub (countMain_deriv ht)
  intro t u ht hu
  rcases hu.eq_or_lt with rfl | htu
  · simp
  have ht₀ := hv.trans_le ht
  obtain ⟨s,hs,he⟩ := exists_hasDerivAt_eq_slope gammaMainRemainder d htu
    (fun s hs => (hd s (ht₀.trans_le hs.1)).continuousAt.continuousWithinAt)
    (fun s hs => hd s (ht₀.trans hs.1))
  rw [← (eq_div_iff (sub_pos.mpr htu).ne').mp he,abs_mul,abs_of_pos (sub_pos.mpr htu)]
  exact mul_le_mul_of_nonneg_right (hbound _ (ht.trans hs.1.le)) (sub_pos.mpr htu).le

private theorem gammaMain_remainder_weighted {v : ℝ} (hv : 0 < v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t u : ℝ, v ≤ t → t ≤ u →
      |gammaMainRemainder u-gammaMainRemainder t| ≤ K*(u-t)*MontgomeryPoisson.cauchyWeight t := by
  obtain ⟨B,hB,hglobal⟩ := exists_gammaMain_remainder_Lipschitz hv
  obtain ⟨C,hC,hlarge⟩ := smoothCount_main_variation
  let K := 2*(B+C)
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro t u ht htu
  have ht₀ := hv.trans_le ht
  have hu₀ := ht₀.trans_le htu
  have hgap := sub_nonneg.mpr htu
  by_cases h1 : 1 ≤ t
  · have htv := hlarge t u h1 htu
    have hs : 1 ≤ t^2 := by nlinarith only [h1,mul_nonneg (sub_nonneg.mpr h1) ht₀.le]
    have hw : 1/t^2 ≤ 2*MontgomeryPoisson.cauchyWeight t := by
      unfold MontgomeryPoisson.cauchyWeight
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (sq_pos_of_pos ht₀) (by positivity)).mpr
      nlinarith only [hs]
    have hm : t^2 ≤ t*u := by simpa only [pow_two] using mul_le_mul_of_nonneg_left htu ht₀.le
    calc
      _ ≤ C*(t⁻¹-u⁻¹) := htv
      _ = C*(u-t)/(t*u) := by field_simp [ht₀.ne',hu₀.ne'] <;> ring
      _ ≤ C*(u-t)/t^2 := div_le_div_of_nonneg_left (mul_nonneg hC hgap) (sq_pos_of_pos ht₀) hm
      _ = C*(u-t)*(1/t^2) := by ring
      _ ≤ C*(u-t)*(2*MontgomeryPoisson.cauchyWeight t) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hC hgap)
      _ ≤ _ := by
        dsimp only [K]
        nlinarith only [mul_nonneg (mul_nonneg hB hgap) (MontgomeryLocalMass.cauchyWeight_nonneg t)]
  · have hsq : t^2 ≤ 1 := by nlinarith only [mul_nonneg (sub_nonneg.mpr (le_of_not_ge h1)) (by linarith : 0 ≤ 1+t)]
    have hw : 1 ≤ 2*MontgomeryPoisson.cauchyWeight t := by
      unfold MontgomeryPoisson.cauchyWeight
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith only [hsq]
    calc
      _ ≤ B*(u-t) := hglobal t u ht htu
      _ ≤ B*(u-t)*(2*MontgomeryPoisson.cauchyWeight t) :=
        le_mul_of_one_le_right (mul_nonneg hB hgap) hw
      _ ≤ _ := by
        dsimp only [K]
        nlinarith only [mul_nonneg (mul_nonneg hC hgap) (MontgomeryLocalMass.cauchyWeight_nonneg t)]

/-- Signed zero-count argument increments with the exact smooth gamma count
subtracted, averaged over the actual base ordinate occurrences. -/
def sampledArgumentIncrement (T R : ℝ) : ℝ := sampledHeightIncrement discrepancy T R

/-- The gamma comparison is uniform over all positive widths, even widths
shrinking faster than any power of the cutoff. -/
theorem exists_sampled_argument_error_comparison :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T R : ℝ, 3 ≤ T → 0 < R →
      |sampledRvMError T R - sampledArgumentIncrement T R|/R ≤
        K/unfoldedCutoff T := by
  classical
  obtain ⟨v,hv,hmin⟩ := exists_ordinate_floor
  obtain ⟨K,hK,hbound⟩ := gammaMain_remainder_weighted hv
  obtain ⟨C,hC,hrowbound⟩ := MontgomeryLocalMass.exists_actual_cauchy_row_bound
  refine ⟨4*Real.pi*K*C,by positivity,?_⟩
  intro T R hT₃ hR
  have hT : 1 < T := by linarith
  have hD : 0 < unfoldedCutoff T := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hL : 0 < unfoldingScale T := div_pos (Real.log_pos hT) (by positivity)
  let H := R/unfoldingScale T
  let t := copyOrdinate T
  let u := fun i : Copies T => min T (t i+H)
  have hH : 0 < H := div_pos hR hL
  have hrow (i : Copies T) :
      |(countError (u i)-countError (t i)) - (discrepancy (u i)-discrepancy (t i))| ≤ K*H*MontgomeryPoisson.cauchyWeight (t i) := by
    have htu : t i ≤ u i := le_min (mem_cutoff.mp i.1.property).2.2 (le_add_of_nonneg_right hH.le)
    have hlen : u i-t i ≤ H := by linarith only [min_le_right T (t i+H)]
    have he : (countError (u i)-countError (t i)) - (discrepancy (u i)-discrepancy (t i)) =
        gammaMainRemainder (u i)-gammaMainRemainder (t i) := by
      unfold countError discrepancy gammaMainRemainder
      ring
    rw [he]
    exact (hbound _ _ (hmin T i) htu).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlen hK) (MontgomeryLocalMass.cauchyWeight_nonneg _))
  rw [sampledRvMError,sampledArgumentIncrement,sampledHeightIncrement,sampledHeightIncrement,
    ←sub_div,← Finset.sum_sub_distrib,abs_div,abs_of_pos hD]
  have h := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Copies T))) => hrow i))
  rw [← Finset.mul_sum] at h
  have hsum := hrowbound T (zero_le_one.trans hT.le) 0
  simp only [zero_sub,MontgomeryLocalMass.cauchyWeight_neg] at hsum
  have ht := zero_lt_one.trans hT
  have hlogs : Real.log (T+3) ≤ 2*Real.log T := by
    have hs : T+3 ≤ T*T := by nlinarith only [hT₃,mul_nonneg (sub_nonneg.mpr hT₃) ht.le]
    simpa only [Real.log_mul ht.ne' ht.ne',two_mul] using Real.log_le_log (by linarith : 0<T+3) hs
  have htotal := h.trans (mul_le_mul_of_nonneg_left
    (hsum.trans (mul_le_mul_of_nonneg_left hlogs hC.le)) (mul_nonneg hK hH.le))
  apply (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right htotal hD.le) hR.le).trans_eq
  dsimp only [H,unfoldingScale]
  field_simp [hD.ne',hR.ne',(Real.log_pos hT).ne',Real.pi_ne_zero] <;> ring

/-- Replacing the geometric RvM error by the exact argument discrepancy
adds a vanishing relative correction at every eventually positive width. -/
theorem sampled_argument_comparison_tendsto {R : ℝ → ℝ} (hR : ∀ᶠ T : ℝ in atTop, 0 < R T) :
    Tendsto (fun T : ℝ => sampledRvMError T (R T)/R T - sampledArgumentIncrement T (R T)/R T)
      atTop (𝓝 0) := by
  obtain ⟨K,hK,hm⟩ := exists_sampled_argument_error_comparison
  have hD : Tendsto unfoldedCutoff atTop atTop :=
    (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop).atTop_div_const (by positivity)
  have hu := (tendsto_inv_atTop_zero.comp hD).const_mul K
  simp only [mul_zero] at hu
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hu
  filter_upwards [hR,eventually_ge_atTop (3:ℝ)] with T hr ht
  rw [Real.norm_eq_abs,←sub_div,abs_div,abs_of_pos hr]
  simpa only [Function.comp_def,div_eq_mul_inv] using hm T (R T) ht hr

/-- At fixed unfolded widths the conjectural sine deficit is precisely the
signed cumulative argument fluctuation sampled at the actual zeros. -/
theorem positiveGapPCC_iff_sampledArgumentIncrement :
    PositiveGapPCC ↔ ∀ R : ℝ, 0 < R →
      Tendsto (fun T => sampledArgumentIncrement T R) atTop (𝓝 (sineGapMass R-R)) := by
  rw [positiveGapPCC_iff_sampledRvMError]
  have hdiff (R : ℝ) (hR : 0 < R) :
      Tendsto (fun T : ℝ => sampledRvMError T R - sampledArgumentIncrement T R) atTop (𝓝 0) := by
    have h := (sampled_argument_comparison_tendsto (R:=fun _ => R) (Eventually.of_forall fun _ => hR)).mul_const R
    simpa only [←sub_div,div_mul_cancel₀ _ hR.ne',zero_mul] using h
  constructor
  · intro h R hR
    have ht := (h R hR).sub (hdiff R hR)
    simpa only [sub_sub_cancel,sub_zero] using ht
  · intro h R hR
    have ht := (hdiff R hR).add (h R hR)
    simpa only [sub_add_cancel,zero_add] using ht

/-- Unit density at a moving positive, submacroscopic width is equivalent
to cancellation of the measured signed argument increment at that width. -/
theorem positiveGapMass_div_width_tendsto_iff_sampledArgumentIncrement {R : ℝ → ℝ} {ℓ : ℝ}
    (hR : ∀ᶠ T : ℝ in atTop, 0 < R T)
    (hsmall : Tendsto (fun T : ℝ => R T/unfoldedCutoff T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => positiveGapMass T (R T)/R T) atTop (𝓝 ℓ) ↔
      Tendsto (fun T : ℝ => sampledArgumentIncrement T (R T)/R T) atTop (𝓝 (ℓ-1)) := by
  rw [positiveGapMass_div_width_tendsto_iff_sampledRvMError hR hsmall]
  have hd := sampled_argument_comparison_tendsto hR
  constructor
  · intro h
    simpa only [sub_sub_cancel,sub_zero] using h.sub hd
  · intro h
    simpa only [sub_add_cancel,zero_add] using hd.add h

/-- The measured second moment of the signed argument increments at the
base zeros, normalized by the unfolded cutoff. -/
def sampledArgumentIncrementEnergy (T R : ℝ) : ℝ :=
  (∑ i : Copies T, (discrepancy (min T (copyOrdinate T i+R/unfoldingScale T)) -
    discrepancy (copyOrdinate T i))^2) / unfoldedCutoff T

/-- The exact finite Cauchy bound for the signed sampled argument statistic. -/
theorem sampledArgumentIncrement_sq_le {T : ℝ} (hT : 1 < T) (R : ℝ) :
    (sampledArgumentIncrement T R)^2 ≤
      ((Ncount 0 T : ℝ)/unfoldedCutoff T)*sampledArgumentIncrementEnergy T R := by
  let D := unfoldedCutoff T
  let a := fun i : Copies T => discrepancy (min T (copyOrdinate T i+R/unfoldingScale T)) -
    discrepancy (copyOrdinate T i)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have h : (∑ i : Copies T, a i)^2 ≤ (Ncount 0 T : ℝ)*(∑ i : Copies T, (a i)^2) := by
    simpa only [Finset.card_univ,card_copies] using
      (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Copies T))) (f:=a))
  change ((∑ i : Copies T, a i)/D)^2 ≤ ((Ncount 0 T : ℝ)/D)*((∑ i : Copies T, (a i)^2)/D)
  rw [div_pow, div_mul_div_comm,←pow_two]
  exact div_le_div_of_nonneg_right h (sq_nonneg _)

/-- Subquadratic sampled argument variance is a sufficient moving-width
input for the actual positive-gap unit-density law. This applies throughout
the range R=o(D), including unfolded widths smaller than log T. -/
theorem positiveGapMass_div_width_tendsto_of_sampledArgumentEnergy {R : ℝ → ℝ}
    (hR : ∀ᶠ T : ℝ in atTop, 0 < R T)
    (hsmall : Tendsto (fun T : ℝ => R T/unfoldedCutoff T) atTop (𝓝 0))
    (henergy : Tendsto (fun T : ℝ => sampledArgumentIncrementEnergy T (R T)/(R T)^2)
      atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => positiveGapMass T (R T)/R T) atTop (𝓝 1) := by
  apply (positiveGapMass_div_width_tendsto_iff_sampledArgumentIncrement hR hsmall).mpr
  rw [sub_self]
  have hs : Tendsto (fun T : ℝ => (sampledArgumentIncrement T (R T)/R T)^2) atTop (𝓝 0) := by
    have hu := tendsto_count_div_mainTerm.mul henergy
    simp only [mul_zero] at hu
    apply squeeze_zero' (Eventually.of_forall fun T => sq_nonneg _) _ hu
    filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
    rw [div_pow]
    apply (div_le_div_of_nonneg_right (sampledArgumentIncrement_sq_le hT (R T)) (sq_nonneg _)).trans_eq
    dsimp only [unfoldedCutoff]
    ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,Real.sqrt_zero,Real.norm_eq_abs] using
    (Real.continuous_sqrt.continuousAt (x:=0)).tendsto.comp hs

/-- Positive rational widths suffice for the actual signed argument test. -/
theorem positiveGapPCC_iff_rationalSampledArgumentIncrement :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q →
      Tendsto (fun T : ℝ => sampledArgumentIncrement T q) atTop (𝓝 (sineGapMass q-q)) := by
  constructor
  · intro h q hq
    exact positiveGapPCC_iff_sampledArgumentIncrement.mp h q (by exact_mod_cast hq)
  · intro h
    apply positiveGapPCC_iff_rationalSampledRvMError.mpr
    intro q hq
    have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
    have hd := (sampled_argument_comparison_tendsto (R:=fun _ => (q:ℝ))
      (Eventually.of_forall fun _ => hqr)).mul_const (q:ℝ)
    have hd' : Tendsto (fun T : ℝ => sampledRvMError T q-sampledArgumentIncrement T q) atTop (𝓝 0) := by
      simpa only [←sub_div,div_mul_cancel₀ _ hqr.ne',zero_mul] using hd
    simpa only [sub_add_cancel,zero_add] using hd'.add (h q hq)

end RiemannResearch.Analysis.MontgomeryPositiveGap

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapPCC_iff_rationalSampledArgumentIncrement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_rationalSampledArgumentIncrement

end RiemannResearch.Analysis.MontgomeryPositiveGap
