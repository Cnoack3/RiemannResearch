import RiemannResearch.Analysis.MontgomeryOrdinateWindowPolarization

/-!
# Translation averages of positive zeta-zero gaps

Write `P_T(u)` for the normalized number of gaps in `(0,u]`.
The box average of `P_T(s+w) - P_T(s)` over `0 ≤ s ≤ R`,
divided by `w`, tends to one whenever `log T = o(R)`, `R = o(T log T)`,
and `0 < w = o(R)`. This permits widths tending to zero.
The proof uses the actual mesoscopic cumulative count
and the finite triangle-energy identity.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/-- Swapping the width and the averaging range preserves the density:
both sides are the same normalized mixed difference of the window energy. -/
theorem rightSmoothedOrdinateCount_div_swap {T w R : ℝ}
    (hT : 1 < T) (hw : 0 < w) (hR : 0 < R) :
    rightSmoothedOrdinateCount T w R / w = rightSmoothedOrdinateCount T R w / R := by
  rw [rightSmoothedOrdinateCount_eq_windowEnergy hT hw.le hR,
    rightSmoothedOrdinateCount_eq_windowEnergy hT hR.le hw, add_comm R w]
  ring

/-- The normalized translation average is bounded by endpoint counts. -/
theorem translatedGapDensity_bounds {T w R : ℝ} (hT : 1 < T) (hw : 0 < w) (hR : 0 < R) :
    (positiveGapMass T R - positiveGapMass T w) / R ≤
        rightSmoothedOrdinateCount T w R / w ∧
    rightSmoothedOrdinateCount T w R / w ≤ positiveGapMass T (R+w) / R := by
  rw [rightSmoothedOrdinateCount_div_swap hT hw hR]
  obtain ⟨hl, hu⟩ := rightSmoothedOrdinateCount_sub_bounds (q := R) hT hw
  constructor <;> apply div_le_div_of_nonneg_right _ hR.le <;> linarith

/-- Any positive interval of width `w(T) = o(R(T))` has mean pair density
one after uniformly averaging its starting offset from zero to `R(T)`.
All pairs count analytic multiplicity and the left endpoint is open. -/
theorem translatedGapDensity_tendsto_one {R w : ℝ → ℝ}
    (hg : Tendsto (fun T : ℝ => R T / Real.log T) atTop atTop)
    (hs : Tendsto (fun T => R T / unfoldedCutoff T) atTop (𝓝 0))
    (hw : ∀ᶠ T in atTop, 0 < w T)
    (hwR : Tendsto (fun T => w T / R T) atTop (𝓝 0)) :
    Tendsto (fun T => rightSmoothedOrdinateCount T (w T) (R T) / w T) atTop (𝓝 1) := by
  have hR : ∀ᶠ T : ℝ in atTop, 0 < R T := by
    filter_upwards [hg.eventually_gt_atTop 0, eventually_gt_atTop (1 : ℝ)] with T hp ht
    exact (div_pos_iff.mp hp).resolve_right (fun hn => (Real.log_pos ht).not_gt hn.2) |>.1
  have hscaled (c : ℝ) (hc : 0 < c) :
      Tendsto (fun T => positiveGapMass T (c * R T) / R T) atTop (𝓝 c) := by
    have hg' : Tendsto (fun T : ℝ => (c * R T) / Real.log T) atTop atTop := by
      simpa only [mul_div_assoc] using hg.const_mul_atTop hc
    have hs' : Tendsto (fun T => (c * R T) / unfoldedCutoff T) atTop (𝓝 0) := by
      simpa only [mul_div_assoc, mul_zero] using hs.const_mul c
    have hp := (positiveGapMass_mesoscopic_tendsto hg' hs').mul_const c
    rw [one_mul] at hp
    apply hp.congr'
    filter_upwards [hR] with T hT
    field_simp [hT.ne', hc.ne']
  have hbase := positiveGapMass_mesoscopic_tendsto hg hs
  apply tendsto_order.2
  constructor
  · intro l hl
    let c := (1-l)/2
    have hc : 0 < c := by dsimp [c]; linarith
    have hlim := hbase.sub (hscaled c hc)
    have hlt : l < 1-c := by dsimp [c]; linarith
    filter_upwards [hlim.eventually_const_lt hlt, hwR.eventually_lt_const hc,
      eventually_gt_atTop (1 : ℝ), hw, hR] with T hlow hwidth ht hwt hRt
    have hmass := positiveGapMass_mono ht ((div_lt_iff₀ hRt).mp hwidth).le
    have hbd := (translatedGapDensity_bounds ht hwt hRt).1
    have hcomp := div_le_div_of_nonneg_right hmass hRt.le
    change l < positiveGapMass T (R T) / R T - positiveGapMass T (c * R T) / R T at hlow
    rw [sub_div] at hbd
    linarith only [hlow, hcomp, hbd]
  · intro u hu
    let c := (1+u)/2
    have hc : 0 < c := by dsimp [c]; linarith
    have hc1 : 0 < c-1 := by dsimp [c]; linarith
    have hcu : c < u := by dsimp [c]; linarith
    filter_upwards [(hscaled c hc).eventually_lt_const hcu, hwR.eventually_lt_const hc1,
      eventually_gt_atTop (1 : ℝ), hw, hR] with T hupper hwidth ht hwt hRt
    have hsize := (div_lt_iff₀ hRt).mp hwidth
    have hmass := positiveGapMass_mono ht (show R T + w T ≤ c * R T by
      linarith only [hsize, sub_mul c 1 (R T), one_mul (R T)])
    exact ((translatedGapDensity_bounds ht hwt hRt).2.trans
      (div_le_div_of_nonneg_right hmass hRt.le)).trans_lt hupper

/-- With a fixed microscopic width, the concrete averaging range `(log T)^2`
already gives the full width as the limiting translated pair mass. -/
theorem rightSmoothedOrdinateCount_logSq_tendsto {q : ℝ} (hq : 0 < q) :
    Tendsto (fun T : ℝ => rightSmoothedOrdinateCount T q (Real.log T ^ 2)) atTop (𝓝 q) := by
  have hg : Tendsto (fun T : ℝ => Real.log T ^ 2 / Real.log T) atTop atTop := by
    apply Real.tendsto_log_atTop.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    field_simp [(Real.log_pos hT).ne']
  have hLT : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hs : Tendsto (fun T : ℝ => Real.log T ^ 2 / unfoldedCutoff T) atTop (𝓝 0) := by
    have h := hLT.mul_const (2 * Real.pi)
    rw [zero_mul] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    unfold unfoldedCutoff
    field_simp [(Real.log_pos hT).ne', (zero_lt_one.trans hT).ne', Real.pi_ne_zero] <;> ring
  have hL : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop := by
    simpa only [sq] using Real.tendsto_log_atTop.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hqL : Tendsto (fun T : ℝ => q / Real.log T ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hL).const_mul q
  have h := (translatedGapDensity_tendsto_one hg hs (Eventually.of_forall fun _ => hq) hqL).mul_const q
  simpa only [one_mul, div_mul_cancel₀ _ hq.ne'] using h

/-- The ordinary positive-gap conjecture is equivalent to the loss from
anchoring a fixed interval at the sampled zero instead of averaging its
offset up to `(log T)^2`. Its predicted loss at width `q` is the integrated
squared sinc, `q - sineGapMass q`. -/
theorem positiveGapPCC_iff_translationDeficit :
    PositiveGapPCC ↔ ∀ q : ℚ, 0 < q → Tendsto (fun T : ℝ =>
      rightSmoothedOrdinateCount T q (Real.log T ^ 2) - positiveGapMass T q)
      atTop (𝓝 ((q : ℝ) - sineGapMass q)) := by
  rw [positiveGapPCC_iff_rationalWidthLimits]
  constructor
  · intro h q hq
    exact (rightSmoothedOrdinateCount_logSq_tendsto (q := (q : ℝ)) (by exact_mod_cast hq)).sub
      (h q hq)
  · intro h q hq
    have hlim := (rightSmoothedOrdinateCount_logSq_tendsto
      (q := (q : ℝ)) (by exact_mod_cast hq)).sub (h q hq)
    simpa only [sub_sub_cancel] using hlim

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapPCC_iff_translationDeficit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_translationDeficit

end RiemannResearch.Analysis.MontgomeryPositiveGap
