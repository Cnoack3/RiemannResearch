import RiemannResearch.Analysis.MontgomerySampledArgumentError

/-! # Moving the left endpoint off a zero ordinate

A shift to the right retains the strictly positive gap convention at every
zero, including repeated ordinates. Averaging those shifts replaces the
atomic base-height law by a one-sided box convolution. The two errors in
undoing the shift are finite, explicitly measurable gap masses.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate

/-- Normalized neighbor count with both endpoints shifted right by s
unfolded units and clipped to the actual cutoff. -/
def rightShiftedOrdinateCount (T q s : ℝ) : ℝ :=
  (∑ i : Copies T, (Ncount
    (min T (copyOrdinate T i + s / unfoldingScale T))
    (min T (copyOrdinate T i + (q+s) / unfoldingScale T)) : ℝ)) / unfoldedCutoff T

/-- The clipped rows implement the difference of two cumulative positive-gap
masses exactly. No diagonal or equal-height term is introduced. -/
theorem rightShiftedOrdinateCount_eq {T q s : ℝ}
    (hT : 1 < T) (hq : 0 < q) (hs : 0 < s) :
    rightShiftedOrdinateCount T q s = positiveGapMass T (q+s) - positiveGapMass T s := by
  have hL : 0 < unfoldingScale T := div_pos (Real.log_pos hT) (by positivity)
  have he (r : ℝ) (hr : 0 < r) := positiveGapMass_eq_ordinate_window_counts hT (div_pos hr hL)
  have hleft := he s hs
  have hright := he (q+s) (add_pos hq hs)
  rw [div_mul_cancel₀ _ hL.ne'] at hleft hright
  rw [rightShiftedOrdinateCount, hright, hleft, ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have h₁ : copyOrdinate T i ≤ min T (copyOrdinate T i + s / unfoldingScale T) :=
    le_min (mem_cutoff.mp i.1.property).2.2 (le_add_of_nonneg_right (div_nonneg hs.le hL.le))
  have h₂ : min T (copyOrdinate T i + s / unfoldingScale T) ≤
      min T (copyOrdinate T i + (q+s) / unfoldingScale T) := by
    exact min_le_min le_rfl (add_le_add le_rfl
      (div_le_div_of_nonneg_right (le_add_of_nonneg_left hq.le) hL.le))
  rw [Ncount_add h₁ h₂, Nat.cast_add]
  ring

/-- Box average of the shifted ordinate rows. The representation through the
positive-gap cumulative function also gives integrability directly. -/
def rightSmoothedOrdinateCount (T q η : ℝ) : ℝ :=
  (∫ s in (0:ℝ)..η, positiveGapMass T (q+s) - positiveGapMass T s) / η

/-- One-sided boundary-strip bound for box smoothing at actual ordinates.
The lost mass is charged only to positive gaps near zero. The gained mass
is charged only to (q,q+η]. -/
theorem rightSmoothedOrdinateCount_sub_bounds {T q η : ℝ}
    (hT : 1 < T) (hη : 0 < η) :
    -positiveGapMass T η ≤ rightSmoothedOrdinateCount T q η - positiveGapMass T q ∧
    rightSmoothedOrdinateCount T q η - positiveGapMass T q ≤
      positiveGapMass T (q+η) - positiveGapMass T q := by
  let G := positiveGapMass T
  have hg : Monotone G := positiveGapMass_mono hT
  have hshift : Monotone (fun s => G (q+s)) := fun _ _ h => hg (add_le_add le_rfl h)
  have hi : IntervalIntegrable (fun s => G (q+s) - G s) volume 0 η :=
    hshift.intervalIntegrable.sub hg.intervalIntegrable
  have hlo := intervalIntegral.integral_mono_on (μ := volume) hη.le
    (f := fun _ => G q - G η) intervalIntegrable_const hi
    (fun s hs => sub_le_sub (hg (le_add_of_nonneg_right hs.1)) (hg hs.2))
  have hhi := intervalIntegral.integral_mono_on (μ := volume) hη.le hi
    (g := fun _ => G (q+η)) intervalIntegrable_const
    (fun s hs => (sub_le_self _ (positiveGapMass_nonneg hT s)).trans (hg (add_le_add le_rfl hs.2)))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hlo hhi
  change -G η ≤ (∫ s in (0:ℝ)..η, G (q+s) - G s) / η - G q ∧
    (∫ s in (0:ℝ)..η, G (q+s) - G s) / η - G q ≤ G (q+η) - G q
  have hl : G q - G η ≤ (∫ s in (0:ℝ)..η, G (q+s) - G s) / η :=
    (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hlo)
  have hu : (∫ s in (0:ℝ)..η, G (q+s) - G s) / η ≤ G (q+η) :=
    (div_le_iff₀ hη).mpr (by simpa only [mul_comm] using hhi)
  constructor <;> linarith only [hl, hu]

/-- A finite polarization identity for two adjoining observation windows.
Every equal-height contribution cancels in the three triangle energies. -/
theorem rightSmoothedOrdinateCount_eq_windowEnergy {T q η : ℝ}
    (hT : 1 < T) (hq : 0 ≤ q) (hη : 0 < η) :
    rightSmoothedOrdinateCount T q η =
      (unfoldedWindowEnergy T (q+η) - unfoldedWindowEnergy T q -
        unfoldedWindowEnergy T η) / (2*η) := by
  have hP := positiveGapMass_mono hT
  have hshift : Monotone (fun s => positiveGapMass T (q+s)) :=
    fun _ _ h => hP (add_le_add le_rfl h)
  have hchange : (∫ s in (0:ℝ)..η, positiveGapMass T (q+s)) =
      ∫ s in q..q+η, positiveGapMass T s := by
    simpa only [zero_add, add_zero, add_comm] using
      (intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := η) (positiveGapMass T) q)
  rw [rightSmoothedOrdinateCount, intervalIntegral.integral_sub
    hshift.intervalIntegrable hP.intervalIntegrable, hchange, unfoldedWindowEnergy,
    unfoldedWindowEnergy, unfoldedWindowEnergy,
    physicalTriangle_sub_eq_collision_add_positiveGapBand hT hq (le_add_of_nonneg_right hη.le),
    physicalTriangle_eq_collision_add_positive_gaps hT hη.le]
  field_simp [hη.ne'] <;> ring

/-- Desmoothing at any prescribed vanishing positive scale. A single
near-origin positive-gap count fixes the mass lost by mollifying at the
sampling jumps, simultaneously for all rational widths. -/
theorem positiveGapPCC_iff_rightSmoothedOrdinateCounts {η : ℝ → ℝ}
    (hη : Tendsto η atTop (𝓝 0)) (hpos : ∀ᶠ T : ℝ in atTop, 0 < η T) :
    PositiveGapPCC ↔
      Tendsto (fun T : ℝ => positiveGapMass T (η T)) atTop (𝓝 0) ∧
      ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ => rightSmoothedOrdinateCount T q (η T))
        atTop (𝓝 (sineGapMass q)) := by
  constructor
  · intro h
    have hz := shrinking_positive_gap_limit h hη
    refine ⟨hz, ?_⟩
    intro q hq
    have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
    have hlo := (positiveGapPCC_iff_rationalWidthLimits.mp h q hq).sub hz
    rw [sub_zero] at hlo
    apply tendsto_order.2
    constructor
    · intro l hl
      filter_upwards [hlo.eventually_const_lt hl, eventually_gt_atTop (1:ℝ), hpos]
        with T hsmall hT hδ
      have hb := (rightSmoothedOrdinateCount_sub_bounds (q := (q:ℝ)) hT hδ).1
      change l < positiveGapMass T q - positiveGapMass T (η T) at hsmall
      linarith only [hsmall, hb]
    · intro u hu
      let d := (u - sineGapMass q) / 3
      have hd : 0 < d := by dsimp [d]; linarith only [hu]
      have hc := h (q:ℝ) ((q:ℝ)+1) hqr (le_add_of_nonneg_right zero_le_one) d hd
      filter_upwards [hc, hη.eventually (gt_mem_nhds hd), hη.eventually (gt_mem_nhds zero_lt_one),
        eventually_gt_atTop (1:ℝ), hpos] with T hclose hδd hδ₁ hT hδ
      have hb := (rightSmoothedOrdinateCount_sub_bounds (q := (q:ℝ)) hT hδ).2
      have hmem : (q:ℝ) + η T ∈ Icc (q:ℝ) ((q:ℝ)+1) :=
        ⟨le_add_of_nonneg_right hδ.le, add_le_add le_rfl hδ₁.le⟩
      have hbound := (abs_le.mp (hclose _ hmem)).2
      have hsine := (sineGapMass_increment_bounds hmem.1).2
      dsimp only [d] at hbound hδd
      linarith only [hb, hbound, hsine, hδd, hu]
  · rintro ⟨hz, hs⟩
    apply positiveGapPCC_iff_rationalWidthLimits.mpr
    intro q hq
    have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
    apply tendsto_order.2
    constructor
    · intro l hl
      obtain ⟨p,hp,hpq⟩ := exists_rat_btwn (show max 0 ((q:ℝ)-(sineGapMass q-l)) < (q:ℝ)
        from max_lt hqr (by linarith only [hl]))
      have hp₀ := (le_max_left _ _).trans_lt hp
      have hpl : l < sineGapMass p := by
        linarith only [(sineGapMass_increment_bounds hpq.le).2, (le_max_right _ _).trans_lt hp]
      have hPQ : 0 < (q:ℝ) - p := sub_pos.mpr hpq
      filter_upwards [(hs p (by exact_mod_cast hp₀)).eventually_const_lt hpl,
        hη.eventually (gt_mem_nhds hPQ), eventually_gt_atTop (1:ℝ), hpos] with T hsm hδq hT hδ
      have hb := (rightSmoothedOrdinateCount_sub_bounds (q := (p:ℝ)) hT hδ).2
      have hμ : positiveGapMass T ((p:ℝ)+η T) ≤ positiveGapMass T q :=
        positiveGapMass_mono hT (by linarith only [hδq])
      change l < rightSmoothedOrdinateCount T p (η T) at hsm
      linarith only [hb, hμ, hsm]
    · intro u hu
      have hh := (hs q hq).add hz
      rw [add_zero] at hh
      filter_upwards [hh.eventually_lt_const hu, eventually_gt_atTop (1:ℝ), hpos] with T hsm hT hδ
      have hb := (rightSmoothedOrdinateCount_sub_bounds (q := (q:ℝ)) hT hδ).1
      change rightSmoothedOrdinateCount T q (η T) + positiveGapMass T (η T) < u at hsm
      linarith only [hb, hsm]

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.rightSmoothedOrdinateCount_eq_windowEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rightSmoothedOrdinateCount_eq_windowEnergy

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapPCC_iff_rightSmoothedOrdinateCounts' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_rightSmoothedOrdinateCounts

end RiemannResearch.Analysis.MontgomeryPositiveGap
