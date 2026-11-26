import RiemannResearch.Analysis.MicroscopicPositiveGapProjection
import RiemannResearch.Analysis.MontgomeryMicroscopicNeighborDensity

/-! A rational lower certificate for the repository's Montgomery–Taylor constant.
The double-angle identity propagates upper bounds for v cos(v) / sin(v).
Eleven range reductions suffice for the strict constant 269/400. -/
noncomputable section
open Filter Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap

private lemma doubleAngleUpper {v A B : ℝ} (hv : 0 ≤ v)
    (hs : 0 ≤ Real.sin v) (hc : 0 ≤ Real.cos v) (hA : 0 < A)
    (hAB : A^2-v^2 ≤ A*B) (h : v*Real.cos v ≤ A*Real.sin v) :
    (2*v)*Real.cos (2*v) ≤ B*Real.sin (2*v) := by
  have he : A*(B*Real.sin (2*v)-(2*v)*Real.cos (2*v)) =
      2*(A*Real.cos v+v*Real.sin v)*(A*Real.sin v-v*Real.cos v)
        + 2*Real.cos v*Real.sin v*(A*B-(A^2-v^2)) := by
    rw [show 2*v = v+v by ring, Real.sin_add, Real.cos_add]
    ring
  have hn : 0 ≤ A*(B*Real.sin (2*v)-(2*v)*Real.cos (2*v)) := by
    rw [he]
    have h1 := sub_nonneg.mpr h
    have h2 := sub_nonneg.mpr hAB
    positivity
  by_contra! hlt
  exact (not_lt_of_ge hn) (mul_neg_of_pos_of_neg hA (sub_neg.mpr hlt))

theorem montgomeryTaylor_fraction_gt_269_div_400 : (269/400 : ℝ) < ThmD.HD 1 := by
  let x := (Real.sqrt 2)⁻¹
  have hx : 0 < x := by dsimp [x]; positivity
  have hx2 : x^2 = 1/2 := by
    dsimp [x]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hx1 : x ≤ 1 := by nlinarith only [hx2, sq_nonneg (x-1)]
  let upper (m B : ℝ) := (x/m)*Real.cos (x/m) ≤ B*Real.sin (x/m)
  have step (m A B : ℝ) (hm : 1 ≤ m) (hA : 0 < A)
      (hAB : A^2-1/(2*(2*m)^2) ≤ A*B) (hold : upper (2*m) A) : upper m B := by
    have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
    let v := x/(2*m)
    have hv : 0 < v := div_pos hx (by positivity)
    have hv1 : v ≤ 1 := by
      apply (div_le_iff₀ (show 0 < 2*m by positivity)).mpr
      linarith
    have hv2 : v^2 = 1/(2*(2*m)^2) := by
      dsimp only [v]
      rw [div_pow, hx2]
      ring
    have hs := Real.sin_pos_of_pos_of_lt_pi hv (by linarith [Real.pi_gt_three] : v < Real.pi)
    have hc : 0 < Real.cos v := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
    have h := doubleAngleUpper hv.le hs.le hc.le hA (by rw [hv2]; exact hAB) hold
    have hvd : 2*v = x/m := by dsimp only [v]; field_simp
    change (x/m)*Real.cos (x/m) ≤ B*Real.sin (x/m)
    rw [← hvd]
    exact h
  have h11 : upper 2048 (10000000199/10000000000) := by
    let v := x/2048
    have hv : 0 < v := by dsimp only [v]; positivity
    have hv2 : v^2 = 1/8388608 := by dsimp only [v]; rw [div_pow, hx2]; norm_num
    have hv3 : v^3 = v/8388608 := by rw [pow_succ, hv2]; ring
    have hs := Real.sin_ge_sub_cube hv.le
    rw [hv3] at hs
    have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one v) hv.le
    change v*Real.cos v ≤ (10000000199/10000000000)*Real.sin v
    linarith only [hh, hs, hv]
  have h10 := step 1024 (10000000199/10000000000) (9999999007/10000000000) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (2:ℝ)*1024 = 2048 by norm_num] using h11)
  have h9 := step 512 (9999999007/10000000000) (9999994239/10000000000) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (2:ℝ)*512 = 1024 by norm_num] using h10)
  have h8 := step 256 (9999994239/10000000000) (4999987583/5000000000) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (2:ℝ)*256 = 512 by norm_num] using h9)
  have h7 := step 128 (4999987583/5000000000) (1249987359/1250000000) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (2:ℝ)*128 = 256 by norm_num] using h8)
  have h6 := step 64 (1249987359/1250000000) (4999796847/5000000000) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (2:ℝ)*64 = 128 by norm_num] using h7)
  have h5 := step 32 (4999796847/5000000000) (4999186471/5000000000) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (2:ℝ)*32 = 64 by norm_num] using h6)
  have h4 := step 16 (4999186471/5000000000) (1998697867/2000000000) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (2:ℝ)*16 = 32 by norm_num] using h5)
  have h3 := step 8 (1998697867/2000000000) (9973945361/10000000000) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (2:ℝ)*8 = 16 by norm_num] using h4)
  have h2 := step 4 (9973945361/10000000000) (4947808139/5000000000) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (2:ℝ)*4 = 8 by norm_num] using h3)
  have h1 := step 2 (4947808139/5000000000) (4789909939/5000000000) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (2:ℝ)*2 = 4 by norm_num] using h2)
  have h0 := step 1 (4789909939/5000000000) (330999747/400000000) (by norm_num) (by norm_num)
    (by norm_num) (by simpa only [show (2:ℝ)*1 = 2 by norm_num] using h1)
  have hc : x*Real.cos x ≤ (330999747/400000000)*Real.sin x := by
    simpa only [upper,div_one] using h0
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_gt_three])
  have hr : x*(Real.cos x/Real.sin x) ≤ 330999747/400000000 := by
    rw [← mul_div_assoc, div_le_iff₀ hs]
    exact hc
  rw [ThmD.HD_one]
  change 269/400 < 3/2-x*(Real.cos x/Real.sin x)
  linarith only [hr]

/-- At width 3/2 more than 7/1200 of the unfolded cutoff is represented by
distinct base heights with a distinct microscopic neighbor in either direction. -/
theorem eventually_microscopicNeighborBases_three_halves_gt (forward : Bool) :
    ∀ᶠ T : ℝ in atTop, 7/1200 < ((microscopicNeighborBases T (3/2)
      forward 1).card : ℝ)/unfoldedCutoff T := by
  apply eventually_microscopicNeighborBases_lower (by norm_num) forward 1
  norm_num
  linarith only [montgomeryTaylor_fraction_gt_269_div_400]

theorem eventually_positiveGapMass_three_halves_gt :
    ∀ᶠ T : ℝ in atTop, 7/1200 < positiveGapMass T (3/2) := by
  apply eventually_microscopic_gap_ge_montgomeryTaylor (by norm_num : (0:ℝ) < 3/2) 1
  norm_num
  linarith only [montgomeryTaylor_fraction_gt_269_div_400]

open ActualZeroOrdinate ActualZeroCollisionCertificate
open MicroscopicPositiveGapProjection ProjectedDistinctSpacing
open scoped BigOperators

private theorem real_filter_card {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    ((s.filter p).card : ℝ) = ∑ x ∈ s, if p x then (1:ℝ) else 0 := by
  calc
    _ = ∑ _ ∈ s.filter p, (1:ℝ) := by simp
    _ = _ := by rw [Finset.sum_filter]

/-- The unweighted statistic is the sum of all strictly forward distinct
neighbor counts. A repeated occurrence contributes no extra partner height. -/
theorem distinctPairTest_eq_sum_forwardNeighborCards (T q : ℝ) :
    distinctPairTest T (gapIndicator T q) =
      ∑ x ∈ distinctOrdinates T, ((microscopicNeighborHeights T q true x).card : ℝ) := by
  classical
  have hs : actualOrdinateSupport T = distinctOrdinates T := by
    ext y
    constructor
    · intro h
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
      exact copyOrdinate_mem_distinct T j
    · intro h
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
      let j : Copies T := ⟨⟨z,hz⟩,⟨0,multiplicity_pos hz⟩⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hd (x y : ℝ) :
      (if x = y then 0 else gapIndicator T q x y) = gapIndicator T q x y := by
    by_cases h : x = y
    · subst y
      simp [gapIndicator]
    · simp [h]
  unfold distinctPairTest
  rw [hs]
  simp_rw [hd]
  apply Finset.sum_congr rfl
  intro x _
  symm
  unfold microscopicNeighborHeights gapIndicator
  simpa using real_filter_card (distinctOrdinates T)
    (fun y : ℝ => 0 < Real.log T / (2 * Real.pi) * (y-x) ∧
      Real.log T / (2 * Real.pi) * (y-x) ≤ q)

/-- Each base with m forward neighbors contributes exactly min(J,m) to the
first J layers. Their total is bounded by the full distinct pair count. -/
theorem sum_microscopicNeighborBases_le_distinctPairTest (T q : ℝ) (J : ℕ) :
    (∑ k ∈ Finset.range J, ((microscopicNeighborBases T q true (k+1)).card : ℝ)) ≤
      distinctPairTest T (gapIndicator T q) := by
  classical
  have hrow (m : ℕ) :
      (∑ k ∈ Finset.range J, if k+1 ≤ m then (1:ℝ) else 0) ≤ (m:ℝ) := by
    have he : (Finset.range J).filter (fun k => k+1 ≤ m) = Finset.range (min J m) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
      omega
    rw [← real_filter_card (Finset.range J) (fun k => k+1 ≤ m), he, Finset.card_range]
    exact_mod_cast min_le_right J m
  rw [distinctPairTest_eq_sum_forwardNeighborCards]
  simp_rw [microscopicNeighborBases, real_filter_card]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun x _ => hrow (microscopicNeighborHeights T q true x).card

/-- The sum of the individual Montgomery–Taylor floors up to any fixed
rank J is an eventual lower bound for the unweighted distinct-height law. -/
theorem eventually_distinctPositiveMass_gt_rank_sum {q z : ℝ} (hq : 0 < q) (J : ℕ)
    (hz : z < ∑ k ∈ Finset.range J, (ThmD.HD 1 - ((k+1 : ℕ):ℝ)/q)) :
    ∀ᶠ T : ℝ in atTop, z < distinctPositiveMass T q := by
  let floor (k : ℕ) := ThmD.HD 1 - ((k+1 : ℕ):ℝ)/q
  let base (T : ℝ) (k : ℕ) :=
    ((microscopicNeighborBases T q true (k+1)).card : ℝ) / unfoldedCutoff T
  have hsum (n : ℕ) (ε : ℝ) (he : 0 < ε) :
      ∀ᶠ T : ℝ in atTop,
        (∑ k ∈ Finset.range n, floor k) - ε < ∑ k ∈ Finset.range n, base T k := by
    induction n generalizing ε with
    | zero => simp [he]
    | succ n ih =>
      have hb : ∀ᶠ T : ℝ in atTop, floor n - ε/2 < base T n :=
        eventually_microscopicNeighborBases_lower hq true (n+1)
          (by change floor n-ε/2 < floor n; linarith)
      filter_upwards [ih (ε/2) (half_pos he), hb] with T hA hB
      simp only [Finset.sum_range_succ]
      linarith only [hA,hB]
  change z < ∑ k ∈ Finset.range J, floor k at hz
  filter_upwards [hsum J ((∑ k ∈ Finset.range J, floor k)-z) (sub_pos.mpr hz),
    eventually_gt_atTop (1:ℝ)] with T hS hT
  have hZ : z < ∑ k ∈ Finset.range J, base T k := by
    simpa only [sub_sub_cancel] using hS
  apply hZ.trans_le
  change (∑ k ∈ Finset.range J, ((microscopicNeighborBases T q true (k+1)).card : ℝ)
    / unfoldedCutoff T) ≤ distinctPairTest T (gapIndicator T q) / unfoldedCutoff T
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (sum_microscopicNeighborBases_le_distinctPairTest T q J)
    (div_nonneg (mul_nonneg (zero_lt_one.trans hT).le (Real.log_pos hT).le) (by positivity))


/-- At width 3/2 the unweighted distinct-ordinate mass eventually exceeds 7/1200. -/
theorem eventually_distinctPositiveMass_three_halves_gt :
    ∀ᶠ T : ℝ in atTop, 7/1200 < distinctPositiveMass T (3/2) := by
  apply eventually_distinctPositiveMass_gt_rank_sum (by norm_num : (0:ℝ) < 3/2) 1
  norm_num
  linarith only [montgomeryTaylor_fraction_gt_269_div_400]

end RiemannResearch.Analysis.MontgomeryPositiveGap
