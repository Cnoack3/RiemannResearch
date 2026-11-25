import RiemannResearch.Analysis.MontgomerySampledArgumentError
import RiemannResearch.Analysis.MontgomeryGapIntegratedCriterion
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # One-sided shell comparisons for ordinary positive-gap pair correlation

A majorant for the mass of each fixed rational interval gives one side of the
sine law. To recover its other side it suffices that, for every tolerance,
the cumulative masses approach the affine lower bound at arbitrarily large
fixed integer widths. The width is chosen before taking the height limit.
-/

noncomputable section
open Filter Set MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate

private theorem strict_gapMass_at_zero (T : ℝ) : positiveGapMass T 0 = 0 := by
  have h (x : ℝ) : ¬ (0 < x ∧ x ≤ 0) := fun hx => (not_lt_of_ge hx.2) hx.1
  change (∑ i : Copies T, ∑ j : Copies T, if
    0 < Real.log T / (2 * Real.pi) * (copyOrdinate T j - copyOrdinate T i) ∧
    Real.log T / (2 * Real.pi) * (copyOrdinate T j - copyOrdinate T i) ≤ 0
    then (1 : ℝ) else 0) / (T * Real.log T / (2 * Real.pi)) = 0
  simp [h]

/-- The affine intercept of the ordinary sine gap law is exactly minus one half. -/
theorem sineGapMass_sub_id_tendsto_neg_half :
    Tendsto (fun r : ℝ => sineGapMass r - r) atTop (𝓝 (-(1 / 2 : ℝ))) := by
  have hi : IntegrableOn (fun x : ℝ => Real.sinc (Real.pi * x) ^ 2) (Ioi 0) := by
    by_contra hn
    have h := integral_undef hn
    rw [integral_sinc_sq_pi_Ioi] at h
    norm_num at h
  have ht := intervalIntegral_tendsto_integral_Ioi 0 hi (tendsto_id : Tendsto id (atTop : Filter ℝ) atTop)
  rw [integral_sinc_sq_pi_Ioi] at ht
  apply ht.neg.congr'
  filter_upwards with r
  simp only [sineGapMass, intervalIntegral.integral_sub intervalIntegrable_const
    (Continuous.intervalIntegrable (by fun_prop : Continuous
      (fun x : ℝ => Real.sinc (Real.pi * x) ^ 2)) _ _),
    intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one, id_eq]
  ring

/-- Upper estimates on individual shells and a sparse lower normalization
suffice for the full sine law. The lower estimate only requires the affine
main term at arbitrarily large integers, with a separate height threshold at
each chosen integer. Both hypotheses follow from ordinary positive-gap PCC. -/
theorem positiveGapPCC_iff_rationalShellUpper_and_cofinalAffineLower :
    PositiveGapPCC ↔
      (∀ a b : ℚ, 0 ≤ a → a < b → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ T : ℝ in atTop, positiveGapMass T b - positiveGapMass T a ≤
          sineGapMass b - sineGapMass a + ε) ∧
      (∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ n : ℕ, m < n ∧
        ∀ᶠ T : ℝ in atTop, (n : ℝ) - 1 / 2 - ε ≤ positiveGapMass T n) := by
  constructor
  · intro hp
    have hlim (a : ℚ) (ha : 0 ≤ a) :
        Tendsto (fun T : ℝ => positiveGapMass T a) atTop (𝓝 (sineGapMass a)) := by
      rcases eq_or_lt_of_le ha with he | ha'
      · subst a
        simpa only [Rat.cast_zero, strict_gapMass_at_zero, sineGapMass,
          intervalIntegral.integral_same] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
      · exact positiveGapPCC_iff_rationalWidthLimits.mp hp a ha'
    constructor
    · intro a b ha hab ε hε
      exact (((hlim b (ha.trans hab.le)).sub (hlim a ha)).eventually_lt_const
        (lt_add_of_pos_right _ hε)).mono (fun _ h => h.le)
    · intro ε hε m
      refine ⟨m + 1, Nat.lt_succ_self _, ?_⟩
      let n : ℕ := m + 1
      have hn : 0 < (n : ℝ) := by dsimp [n]; positivity
      filter_upwards [hp n n hn le_rfl ε hε] with T ht
      have hl := (abs_le.mp (ht n ⟨le_rfl, le_rfl⟩)).1
      change (n : ℝ) - 1 / 2 - ε ≤ positiveGapMass T n
      linarith only [sineGapMass_lower hn.le, hl]
  · rintro ⟨hshell, hanchor⟩
    apply positiveGapPCC_iff_rationalWidthLimits.mpr
    intro q hq
    apply tendsto_order.2
    constructor
    · intro l hl
      let δ := (sineGapMass q - l) / 4
      have hδ : 0 < δ := by dsimp [δ]; linarith only [hl]
      have hs := sineGapMass_sub_id_tendsto_neg_half.eventually_lt_const
        (lt_add_of_pos_right (-(1 / 2 : ℝ)) hδ)
      obtain ⟨U, hU⟩ := eventually_atTop.1 hs
      obtain ⟨m, hm⟩ := exists_nat_gt (max U (q : ℝ))
      obtain ⟨n, hmn, hn⟩ := hanchor δ hδ m
      have hlarge : max U (q : ℝ) < n := hm.trans (by exact_mod_cast hmn)
      have hqr : (q : ℝ) < n := (le_max_right _ _).trans_lt hlarge
      have hqn : q < (n : ℚ) := by exact_mod_cast hqr
      have hmodel := hU n ((le_max_left _ _).trans hlarge.le)
      filter_upwards [hn, hshell q n hq.le hqn δ hδ] with T hlow hband
      simp only [Rat.cast_natCast] at hband
      dsimp only [δ] at hmodel hlow hband
      linarith only [hmodel, hlow, hband, hl]
    · intro u hu
      let δ := (u - sineGapMass q) / 2
      have hδ : 0 < δ := by dsimp [δ]; linarith only [hu]
      filter_upwards [hshell 0 q le_rfl hq δ hδ] with T h
      simp only [Rat.cast_zero, strict_gapMass_at_zero,
        show sineGapMass 0 = 0 by simp [sineGapMass], sub_zero] at h
      dsimp only [δ] at h
      linarith only [h, hu]

open ActualZeroCollisionCertificate ActualZeroWindowVariance

private theorem eventually_shell_upper_on_compact
    {q : ℚ} {U R δ : ℝ} (hU : (q : ℝ) ≤ U) (hδ : 0 < δ)
    (hshell : ∀ b : ℚ, q < b → ∀ᶠ T : ℝ in atTop,
      positiveGapMass T b - positiveGapMass T q ≤ sineGapMass b - sineGapMass q + δ) :
    ∀ᶠ T : ℝ in atTop, ∀ r ∈ Icc U R,
      positiveGapMass T r - positiveGapMass T q ≤ sineGapMass r - sineGapMass q + 2 * δ := by
  classical
  let W (b : {b : ℚ // q < b}) := Ioo ((b.val : ℝ) - δ) (b.val : ℝ)
  have hcover : Icc U R ⊆ ⋃ b, W b := by
    intro r hr
    obtain ⟨b, hrb, hbd⟩ := exists_rat_btwn (lt_add_of_pos_right r hδ)
    have hqb : (q : ℝ) < b := (hU.trans hr.1).trans_lt hrb
    apply mem_iUnion.mpr
    refine ⟨⟨b, by exact_mod_cast hqb⟩, ?_⟩
    change (b : ℝ) - δ < r ∧ r < b
    exact ⟨by linarith only [hbd], hrb⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover W (fun _ => isOpen_Ioo) hcover
  have he : ∀ᶠ T : ℝ in atTop, ∀ b ∈ s,
      positiveGapMass T (b.val : ℝ) - positiveGapMass T q ≤
        sineGapMass (b.val : ℝ) - sineGapMass q + δ :=
    (Filter.eventually_all_finset s).mpr (fun b _ => hshell b.val b.property)
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with T ht hT r hr
  obtain ⟨b, hb⟩ := mem_iUnion.mp (hs hr)
  obtain ⟨hbs, hrb⟩ := mem_iUnion.mp hb
  change (b.val : ℝ) - δ < r ∧ r < b.val at hrb
  linarith only [ht b hbs, positiveGapMass_mono hT hrb.2.le,
    (sineGapMass_increment_bounds hrb.2.le).2, hrb.1]

/-- Actual nonnegative translated-window variance supplies the lower half of
the gap law once equal-ordinate collisions have asymptotic mass one and
each positive-gap shell has its sine-model one-sided upper estimate. -/
theorem positiveGapPCC_of_rationalShellUpper_and_collision
    (hshell : ∀ a b : ℚ, 0 ≤ a → a < b → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ T : ℝ in atTop, positiveGapMass T b - positiveGapMass T a ≤
        sineGapMass b - sineGapMass a + ε)
    (hC : Tendsto (fun T : ℝ => (actualCollision T : ℝ) /
      (T * Real.log T / (2 * Real.pi))) atTop (𝓝 1)) : PositiveGapPCC := by
  apply positiveGapPCC_iff_rationalWidthLimits.mpr
  intro q hq
  apply tendsto_order.2
  constructor
  · intro l hl
    let δ := (sineGapMass q - l) / 8
    have hδ : 0 < δ := by dsimp [δ]; linarith only [hl]
    have hdiff : l = sineGapMass q - 8 * δ := by dsimp only [δ]; ring
    have hm := sineGapMass_sub_id_tendsto_neg_half.eventually_lt_const
      (lt_add_of_pos_right (-(1 / 2 : ℝ)) hδ)
    obtain ⟨u₀, hu₀⟩ := eventually_atTop.1 hm
    let U := max u₀ (q : ℝ)
    have hqU : (q : ℝ) ≤ U := le_max_right _ _
    have hU : 0 < U := (by exact_mod_cast hq : (0 : ℝ) < q).trans_le hqU
    let K := U ^ 2 / 2 + (1 / 2 + 5 * δ) * U
    obtain ⟨R, hR⟩ := exists_gt (max U (K / (4 * δ)))
    have hUR := (le_max_left _ _).trans_lt hR
    have hR0 := hU.trans hUR
    have hbudget : K < 4 * δ * R := by
      have hv := (div_lt_iff₀ (show 0 < 4 * δ by positivity)).mp
        ((le_max_right _ _).trans_lt hR)
      linarith only [hv, mul_comm R (4 * δ)]
    have hwin := eventually_shell_upper_on_compact (R := R) hqU hδ
      (fun b hb => hshell q b hq.le hb δ hδ)
    filter_upwards [hwin, hC.eventually_lt_const (lt_add_of_pos_right 1 hδ),
      eventually_physicalTriangle_ge_sq_sub hR0 (mul_pos hδ hR0),
      eventually_gt_atTop (1 : ℝ)] with T hband hc henergy hT
    by_contra! hbad
    have htail (r : ℝ) (hr : r ∈ Icc U R) :
        positiveGapMass T r ≤ r - (1 / 2 + 5 * δ) := by
      have hmodel := hu₀ r ((le_max_left _ _).trans hr.1)
      linarith only [hband r hr, hmodel, hbad, hdiff]
    have hhead : (∫ r in (0 : ℝ)..U, positiveGapMass T r) ≤ U ^ 2 := by
      have hPU := htail U ⟨le_rfl, hUR.le⟩
      have hI := intervalIntegral.integral_mono_on (μ := volume) hU.le
        (positiveGapMass_mono hT).intervalIntegrable (f := positiveGapMass T)
        (g := fun _ : ℝ => U) intervalIntegrable_const (fun r hr =>
          (positiveGapMass_mono hT hr.2).trans (by linarith only [hPU, hδ]))
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, pow_two] using hI
    have hI := intervalIntegral.integral_mono_on (μ := volume) hUR.le
      (positiveGapMass_mono hT).intervalIntegrable
      ((continuous_id.sub continuous_const).intervalIntegrable U R) htail
    have hlinear : (∫ r in U..R, r - (1 / 2 + 5 * δ)) =
        (R ^ 2 - U ^ 2) / 2 - (R - U) * (1 / 2 + 5 * δ) := by
      rw [intervalIntegral.integral_sub (f := fun r : ℝ => r) (g := fun _ => 1 / 2 + 5 * δ) (continuous_id.intervalIntegrable U R)
        intervalIntegrable_const, integral_id, intervalIntegral.integral_const, smul_eq_mul]
    change (∫ r in U..R, positiveGapMass T r) ≤ (∫ r in U..R, r - (1 / 2 + 5 * δ)) at hI
    rw [hlinear] at hI
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := positiveGapMass T) (a := 0) (b := U) (c := R)
      (positiveGapMass_mono hT).intervalIntegrable (positiveGapMass_mono hT).intervalIntegrable
    rw [physicalTriangle_eq_collision_add_positive_gaps hT hR0.le] at henergy
    have hcollision := mul_le_mul_of_nonneg_left hc.le hR0.le
    dsimp only [K] at hbudget
    nlinarith only [henergy, hcollision, hI, hhead, hadd, hbudget]
  · intro u hu
    let δ := (u - sineGapMass q) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith only [hu]
    filter_upwards [hshell 0 q le_rfl hq δ hδ] with T h
    simp only [Rat.cast_zero, strict_gapMass_at_zero,
      show sineGapMass 0 = 0 by simp [sineGapMass], sub_zero] at h
    dsimp only [δ] at h
    linarith only [h, hu]

/-- With the short-window upper input used in the GLSS collision theorem,
the shell majorants and the single collision limit are also necessary. -/
theorem positiveGapPCC_iff_rationalShellUpper_and_collision
    (hw : ShortWindowSecondMomentUpper) :
    PositiveGapPCC ↔
      (∀ a b : ℚ, 0 ≤ a → a < b → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ T : ℝ in atTop, positiveGapMass T b - positiveGapMass T a ≤
          sineGapMass b - sineGapMass a + ε) ∧
      Tendsto (fun T : ℝ => (actualCollision T : ℝ) /
        (T * Real.log T / (2 * Real.pi))) atTop (𝓝 1) := by
  exact ⟨fun h => ⟨(positiveGapPCC_iff_rationalShellUpper_and_cofinalAffineLower.mp h).1,
    collision_limit_of_positiveGapPCC h hw⟩,
    fun h => positiveGapPCC_of_rationalShellUpper_and_collision h.1 h.2⟩


/-- A one-sided comparison for physical interval masses. The interval with
left endpoint zero includes the entire equal-ordinate atom. Every other
interval is open at its left endpoint. The sine model has unit atom at zero. -/
def FullOrdinateIntervalUpper : Prop :=
  ∀ a b : ℚ, 0 ≤ a → a < b → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ T : ℝ in atTop, positiveGapMass T b - positiveGapMass T a +
      (if a = 0 then (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) - 1 else 0) ≤
        sineGapMass b - sineGapMass a + ε

/-- The diagonal lower count and the one-sided tests touching the origin
determine the entire normalized equal-ordinate atom. -/
theorem collision_limit_of_fullOrdinateIntervalUpper (h : FullOrdinateIntervalUpper) :
    Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))
      atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro l hl
    filter_upwards [tendsto_count_div_mainTerm.eventually_const_lt hl,
      eventually_gt_atTop (1 : ℝ)] with T hN hT
    have hCN : Ncount 0 T ≤ actualCollision T := by
      rw [actualCollision_eq_count_add_excess T]
      omega
    have hD : 0 ≤ T * Real.log T / (2 * Real.pi) :=
      div_nonneg (mul_nonneg (zero_le_one.trans hT.le) (Real.log_nonneg hT.le)) (by positivity)
    exact hN.trans_le (div_le_div_of_nonneg_right (by exact_mod_cast hCN) hD)
  · intro u hu
    let δ := (u - 1) / 3
    have hδ : 0 < δ := by dsimp only [δ]; linarith only [hu]
    obtain ⟨b, h₀, hb⟩ := exists_rat_btwn hδ
    have hbq : 0 < b := by exact_mod_cast h₀
    have hz : sineGapMass 0 = 0 := by simp [sineGapMass]
    have hS := (sineGapMass_increment_bounds h₀.le).2
    simp only [hz, sub_zero] at hS
    filter_upwards [h 0 b le_rfl hbq δ hδ, eventually_gt_atTop (1 : ℝ)] with T hB hT
    simp only [Rat.cast_zero, strict_gapMass_at_zero, sub_zero, if_true, hz] at hB
    dsimp only [δ] at hB hb
    linarith only [hB, hb, hS, positiveGapMass_nonneg hT b, hu]

/-- Upper bounds alone suffice on ordinary rational physical intervals when
the tests reaching the origin retain the measured equal-ordinate atom. -/
theorem positiveGapPCC_of_fullOrdinateIntervalUpper (h : FullOrdinateIntervalUpper) :
    PositiveGapPCC := by
  have hC := collision_limit_of_fullOrdinateIntervalUpper h
  apply positiveGapPCC_of_rationalShellUpper_and_collision _ hC
  intro a b ha hab ε hε
  by_cases hz : a = 0
  · have hc := hC.eventually_const_lt (show 1 - ε / 2 < 1 by linarith only [hε])
    filter_upwards [h a b ha hab (ε / 2) (half_pos hε), hc] with T hband hC₀
    rw [if_pos hz] at hband
    linarith only [hband, hC₀]
  · simpa only [if_neg hz, add_zero] using h a b ha hab ε hε

/-- The reverse implication uses the GLSS short-window input for the
equal-ordinate atom. The sufficient direction above needs no such input. -/
theorem positiveGapPCC_iff_fullOrdinateIntervalUpper (hw : ShortWindowSecondMomentUpper) :
    PositiveGapPCC ↔ FullOrdinateIntervalUpper := by
  refine ⟨?_, positiveGapPCC_of_fullOrdinateIntervalUpper⟩
  intro hp a b ha hab ε hε
  obtain ⟨hs, hc⟩ := (positiveGapPCC_iff_rationalShellUpper_and_collision hw).mp hp
  by_cases hz : a = 0
  · filter_upwards [hs a b ha hab (ε / 2) (half_pos hε),
      hc.eventually_lt_const (show 1 < 1 + ε / 2 by linarith only [hε])] with T hband hC
    rw [if_pos hz]
    linarith only [hband, hC]
  · simpa only [if_neg hz, add_zero] using hs a b ha hab ε hε

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapPCC_of_fullOrdinateIntervalUpper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_of_fullOrdinateIntervalUpper

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapPCC_iff_rationalShellUpper_and_cofinalAffineLower' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_rationalShellUpper_and_cofinalAffineLower

end RiemannResearch.Analysis.MontgomeryPositiveGap
