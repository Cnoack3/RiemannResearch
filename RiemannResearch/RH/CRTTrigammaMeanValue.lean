import RiemannResearch.RH.CRTExactDigamma
import RiemannResearch.RH.ParetoProgressionDigamma
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Canonical trigamma mean-value points for residue weights

Source: user-provided argument, 21 September 2026; NIST DLMF 5.15.1
(https://dlmf.nist.gov/5.15#E1) supports the reciprocal-square series.
Existence, uniqueness, endpoint monotonicity, and error estimates use actual
real digamma derivatives. The stronger scaled monotonicity is not assumed.
-/

namespace RiemannResearch.RH.CRTBlock
noncomputable section
open Pareto
open scoped BigOperators

def digammaSlope (a b : ℝ) : ℝ := (realDigamma b - realDigamma a) / (b - a)

theorem exists_trigamma_mean {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ x ∈ Set.Ioo a b, trigamma x = digammaSlope a b := by
  obtain ⟨x, hx, he⟩ := exists_deriv_eq_slope realDigamma hab
    (fun y hy => (hasDerivAt_re_digamma_pos (lt_of_lt_of_le ha hy.1)).continuousAt.continuousWithinAt)
    (fun y hy => (hasDerivAt_re_digamma_pos (lt_trans ha hy.1)).differentiableAt.differentiableWithinAt)
  exact ⟨x, hx, he⟩

theorem existsUnique_trigamma_mean {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃! x, x ∈ Set.Ioo a b ∧ trigamma x = digammaSlope a b := by
  obtain ⟨x, hx, he⟩ := exists_trigamma_mean ha hab
  refine ⟨x, ⟨hx, he⟩, ?_⟩
  intro y hy
  exact trigamma_strictAntiOn.injOn (lt_trans ha hy.1.1) (lt_trans ha hx.1)
    (hy.2.trans he.symm)

theorem hasSum_digammaSlope {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    HasSum (fun k : ℕ => 1 / (((k : ℝ) + a) * ((k : ℝ) + b)))
      (digammaSlope a b) := by
  have hb : 0 < b := lt_trans ha hab
  have hg : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have h := ((hasSum_reciprocal_difference_positive ha).sub
    (hasSum_reciprocal_difference_positive hb)).div_const (b - a)
  have hvalue :
      (-(Complex.digamma (a : ℂ)).re - Real.eulerMascheroniConstant -
        (-(Complex.digamma (b : ℂ)).re - Real.eulerMascheroniConstant)) / (b - a) =
          digammaSlope a b := by
    unfold digammaSlope realDigamma
    ring
  rw [hvalue] at h
  refine h.congr_fun ?_
  intro k
  have ha' : (k : ℝ) + a ≠ 0 := by positivity
  have hb' : (k : ℝ) + b ≠ 0 := by positivity
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem digammaSlope_strictAnti_endpoints {a b c d : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d)
    (hac : a < c) (hbd : b ≤ d) : digammaSlope c d < digammaSlope a b := by
  have hb : 0 < b := lt_trans ha hab
  have hd : 0 < d := lt_trans hc hcd
  rw [← (hasSum_digammaSlope hc hcd).tsum_eq,
    ← (hasSum_digammaSlope ha hab).tsum_eq]
  apply Summable.tsum_lt_tsum (i := 0)
  · intro k
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  · simp only [Nat.cast_zero, zero_add]
    apply one_div_lt_one_div_of_lt (by positivity)
    exact mul_lt_mul hac hbd (lt_trans ha hab) (le_of_lt hc)
  · exact (hasSum_digammaSlope hc hcd).summable
  · exact (hasSum_digammaSlope ha hab).summable

/-- Comparing the actual means, with no provider assumption on the slope. -/
theorem trigamma_mean_lt_of_endpoints {a b c d x y : ℝ}
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hcd : c < d)
    (hac : a < c) (hbd : b ≤ d)
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo c d)
    (hxe : trigamma x = digammaSlope a b)
    (hye : trigamma y = digammaSlope c d) : x < y := by
  have h := digammaSlope_strictAnti_endpoints ha hab hc hcd hac hbd
  rw [← hxe, ← hye] at h
  by_contra hxy
  have hyx : y ≤ x := le_of_not_gt hxy
  rcases hyx.eq_or_lt with he | he
  · subst y
    exact (lt_irrefl _ h)
  · have h' := trigamma_strictAntiOn (lt_trans hc hy.1) (lt_trans ha hx.1) he
    linarith

/-- The uniquely determined positive-axis MVT point. -/
def trigammaMean (a b : ℝ) (ha : 0 < a) (hab : a < b) : ℝ :=
  Classical.choose (exists_trigamma_mean ha hab)

theorem trigammaMean_spec (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    trigammaMean a b ha hab ∈ Set.Ioo a b ∧
      trigamma (trigammaMean a b ha hab) = digammaSlope a b :=
  Classical.choose_spec (exists_trigamma_mean ha hab)

def progressionAlpha (r L : ℝ) (hr : 0 < r) (hL : 0 < L) : ℝ :=
  trigammaMean (r / L) ((r + 1) / L) (div_pos hr hL)
    ((div_lt_div_iff_of_pos_right hL).2 (by linarith))

theorem progressionAlpha_spec (r L : ℝ) (hr : 0 < r) (hL : 0 < L) :
    progressionAlpha r L hr hL ∈ Set.Ioo (r / L) ((r + 1) / L) ∧
      trigamma (progressionAlpha r L hr hL) =
        digammaSlope (r / L) ((r + 1) / L) :=
  trigammaMean_spec _ _ _ _

theorem progressionAlpha_strictMono_r {r s L : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hL : 0 < L) (hrs : r < s) :
    progressionAlpha r L hr hL < progressionAlpha s L hs hL := by
  have hx := progressionAlpha_spec r L hr hL
  have hy := progressionAlpha_spec s L hs hL
  exact trigamma_mean_lt_of_endpoints (div_pos hr hL)
    ((div_lt_div_iff_of_pos_right hL).2 (by linarith)) (div_pos hs hL)
    ((div_lt_div_iff_of_pos_right hL).2 (by linarith))
    ((div_lt_div_iff_of_pos_right hL).2 hrs)
    ((div_le_div_iff_of_pos_right hL).2 (by linarith)) hx.1 hy.1 hx.2 hy.2

theorem progressionAlpha_strictAnti_L {r L M : ℝ}
    (hr : 0 < r) (hL : 0 < L) (hM : 0 < M) (hLM : L < M) :
    progressionAlpha r M hr hM < progressionAlpha r L hr hL := by
  have hx := progressionAlpha_spec r M hr hM
  have hy := progressionAlpha_spec r L hr hL
  apply trigamma_mean_lt_of_endpoints (div_pos hr hM)
    ((div_lt_div_iff_of_pos_right hM).2 (by linarith)) (div_pos hr hL)
    ((div_lt_div_iff_of_pos_right hL).2 (by linarith)) ?_ ?_ hx.1 hy.1 hx.2 hy.2
  · exact div_lt_div_of_pos_left hr hL hLM
  · exact le_of_lt (div_lt_div_of_pos_left (by linarith : 0 < r + 1) hL hLM)

/-- Exact trigamma intermediate point for the actual arithmetic weight. -/
theorem progressionWeight_eq_trigammaAlpha (Q r : ℕ) (hQ : 0 < Q)
    (hr : 0 < r) (hrQ : r ≤ Q) :
    progressionWeight Q r = trigamma (progressionAlpha (r : ℝ) (Q : ℝ)
      (by exact_mod_cast hr) (by exact_mod_cast hQ)) / (Q : ℝ)^2 := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [(progressionAlpha_spec (r : ℝ) (Q : ℝ) hrR hQr).2,
    progressionWeight_eq_digamma Q r hQ hr hrQ]
  unfold digammaSlope realDigamma
  have hQ0 : (Q : ℝ) ≠ 0 := ne_of_gt hQr
  have hdiff : ((r : ℝ) + 1) / Q - (r : ℝ) / Q = 1 / Q := by ring
  rw [hdiff]
  field_simp

theorem trigammaMean_lt_midpoint (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    trigammaMean a b ha hab < (a + b) / 2 := by
  have hb : 0 < b := lt_trans ha hab
  have hm : 0 < (a + b) / 2 := by positivity
  have hgap : 0 < (b - a)^2 := sq_pos_of_pos (sub_pos.mpr hab)
  have hs : trigamma ((a + b) / 2) < digammaSlope a b := by
    rw [trigamma_eq_series hm, ← (hasSum_digammaSlope ha hab).tsum_eq]
    apply Summable.tsum_lt_tsum (i := 0)
    · intro k
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    · simp only [Nat.cast_zero, zero_add]
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    · exact reciprocalSquareSeries_summable_pos hm
    · exact (hasSum_digammaSlope ha hab).summable
  have hx := trigammaMean_spec a b ha hab
  rw [← hx.2] at hs
  by_contra h
  have hle : (a + b) / 2 ≤ trigammaMean a b ha hab := le_of_not_gt h
  rcases hle.eq_or_lt with he | he
  · rw [← he] at hs
    exact (lt_irrefl _ hs)
  · have h' := trigamma_strictAntiOn hm (lt_trans ha hx.1.1) he
    linarith

theorem sqrt_mul_lt_trigammaMean (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Real.sqrt (a * b) < trigammaMean a b ha hab := by
  have hb : 0 < b := lt_trans ha hab
  have hp : 0 < a * b := mul_pos ha hb
  have hm : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 hp
  have hm2 : (Real.sqrt (a * b))^2 = a * b := Real.sq_sqrt hp.le
  have hgap : 0 < (b - a)^2 := sq_pos_of_pos (sub_pos.mpr hab)
  have hmean : 2 * Real.sqrt (a * b) < a + b := by nlinarith
  have hs : digammaSlope a b < trigamma (Real.sqrt (a * b)) := by
    rw [trigamma_eq_series hm, ← (hasSum_digammaSlope ha hab).tsum_eq]
    apply Summable.tsum_lt_tsum (i := 1)
    · intro k
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [mul_nonneg hk (le_of_lt (sub_pos.mpr hmean))]
    · norm_num only [Nat.cast_one]
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    · exact (hasSum_digammaSlope ha hab).summable
    · exact reciprocalSquareSeries_summable_pos hm
  have hx := trigammaMean_spec a b ha hab
  rw [← hx.2] at hs
  by_contra h
  have hle : trigammaMean a b ha hab ≤ Real.sqrt (a * b) := le_of_not_gt h
  rcases hle.eq_or_lt with he | he
  · rw [he] at hs
    exact (lt_irrefl _ hs)
  · have h' := trigamma_strictAntiOn (lt_trans ha hx.1.1) hm he
    linarith

theorem trigammaMean_sq_sub_mul_le (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    (trigammaMean a b ha hab)^2 - a * b ≤
      trigamma 1 * (a * b) * (trigammaMean a b ha hab)^2 := by
  let x := trigammaMean a b ha hab
  have hx := trigammaMean_spec a b ha hab
  have hxpos : 0 < x := lt_trans ha hx.1.1
  have hb : 0 < b := lt_trans ha hab
  have habpos : 0 < a * b := mul_pos ha hb
  have hx2pos : 0 < x^2 := sq_pos_of_pos hxpos
  have hhead : 1 / (a * b) ≤ digammaSlope a b := by
    have h := (hasSum_digammaSlope ha hab).summable.sum_le_tsum ({0} : Finset ℕ)
      (fun k _ => by positivity)
    simpa only [Finset.sum_singleton, Nat.cast_zero, zero_add,
      (hasSum_digammaSlope ha hab).tsum_eq] using h
  have hshift : trigamma x = 1 / x^2 + trigamma (x + 1) := by
    rw [trigamma_eq_series hxpos, trigamma_eq_series (by positivity)]
    exact reciprocalSquareSeries_shift hxpos
  have htail : trigamma (x + 1) ≤ trigamma 1 :=
    (trigamma_strictAntiOn
      (show (0 : ℝ) < 1 by norm_num)
      (show (0 : ℝ) < x + 1 by positivity)
      (show (1 : ℝ) < x + 1 by linarith)).le
  have hbound : 1 / (a * b) ≤ 1 / x^2 + trigamma 1 := by
    rw [← hx.2] at hhead
    change 1 / (a * b) ≤ trigamma x at hhead
    rw [hshift] at hhead
    linarith
  have hmul := mul_le_mul_of_nonneg_right hbound (le_of_lt (mul_pos habpos hx2pos))
  have hab0 : a * b ≠ 0 := ne_of_gt habpos
  have hx20 : x^2 ≠ 0 := ne_of_gt hx2pos
  field_simp at hmul
  dsimp only [x] at hmul ⊢
  nlinarith

/-- An explicit squared-distance bound, for arbitrary real L > 0. -/
theorem progressionAlpha_scaled_sq_error (r L : ℝ) (hr : 0 < r) (hL : 0 < L) :
    (L * progressionAlpha r L hr hL)^2 - r * (r + 1) ≤
      trigamma 1 * r * (r + 1) * (r + 1)^2 / L^2 := by
  have h := trigammaMean_sq_sub_mul_le (r / L) ((r + 1) / L)
    (div_pos hr hL) ((div_lt_div_iff_of_pos_right hL).2 (by linarith))
  change (progressionAlpha r L hr hL)^2 - r / L * ((r + 1) / L) ≤
    trigamma 1 * (r / L * ((r + 1) / L)) * (progressionAlpha r L hr hL)^2 at h
  have hx := progressionAlpha_spec r L hr hL
  have hxpos : 0 < progressionAlpha r L hr hL := lt_trans (div_pos hr hL) hx.1.1
  have hxupper : (progressionAlpha r L hr hL)^2 ≤ ((r + 1) / L)^2 := by
    nlinarith [hx.1.2]
  have ht : 0 < trigamma 1 := trigamma_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg L)
  have L0 : L ≠ 0 := ne_of_gt hL
  have he1 : ((progressionAlpha r L hr hL)^2 - r / L * ((r + 1) / L)) * L^2 =
      (L * progressionAlpha r L hr hL)^2 - r * (r + 1) := by field_simp
  have he2 : (trigamma 1 * (r / L * ((r + 1) / L)) *
      (progressionAlpha r L hr hL)^2) * L^2 =
      trigamma 1 * r * (r + 1) * (progressionAlpha r L hr hL)^2 := by field_simp
  rw [he1, he2] at hmul
  calc
    _ ≤ trigamma 1 * r * (r + 1) * (progressionAlpha r L hr hL)^2 := hmul
    _ ≤ trigamma 1 * r * (r + 1) * ((r + 1) / L)^2 :=
      mul_le_mul_of_nonneg_left hxupper (by positivity)
    _ = _ := by ring

open Filter
open scoped Topology

/-- The squared error is nonnegative, by the strict geometric-mean bound. -/
theorem progressionAlpha_scaled_sq_error_nonneg (r L : ℝ)
    (hr : 0 < r) (hL : 0 < L) :
    0 ≤ (L * progressionAlpha r L hr hL)^2 - r * (r + 1) := by
  have hgeom := sqrt_mul_lt_trigammaMean (r / L) ((r + 1) / L)
    (div_pos hr hL) ((div_lt_div_iff_of_pos_right hL).2 (by linarith))
  change Real.sqrt (r / L * ((r + 1) / L)) < progressionAlpha r L hr hL at hgeom
  have hx := progressionAlpha_spec r L hr hL
  have hxpos : 0 < progressionAlpha r L hr hL := lt_trans (div_pos hr hL) hx.1.1
  have hp : 0 < r / L * ((r + 1) / L) := by positivity
  have hsqrt := Real.sq_sqrt hp.le
  have hsqrtnonneg := Real.sqrt_nonneg (r / L * ((r + 1) / L))
  have hsq : 0 ≤ (progressionAlpha r L hr hL)^2 - r / L * ((r + 1) / L) := by
    nlinarith
  have hmul := mul_nonneg hsq (sq_nonneg L)
  have L0 : L ≠ 0 := ne_of_gt hL
  have he : ((progressionAlpha r L hr hL)^2 - r / L * ((r + 1) / L)) * L^2 =
      (L * progressionAlpha r L hr hL)^2 - r * (r + 1) := by
    field_simp
  rw [he] at hmul
  exact hmul

/-- Actual fixed-residue asymptotics along every positive real conductor sequence.
No unproved analytic provider is assumed: the only sequence hypotheses are
positivity and divergence of the conductors. -/
theorem progressionAlpha_scaled_tendsto_sqrt (r : ℝ) (hr : 0 < r)
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (hLt : Tendsto L atTop atTop) :
    Tendsto (fun n => L n * progressionAlpha r (L n) hr (hL n))
      atTop (𝓝 (Real.sqrt (r * (r + 1)))) := by
  let C : ℝ := trigamma 1 * r * (r + 1) * (r + 1)^2
  let b : ℕ → ℝ := fun n => L n * progressionAlpha r (L n) hr (hL n)
  have hbpos (n : ℕ) : 0 < b n := by
    have hx := progressionAlpha_spec r (L n) hr (hL n)
    exact mul_pos (hL n) (lt_trans (div_pos hr (hL n)) hx.1.1)
  have hinv : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    apply hLt.inv_tendsto_atTop.congr'
    exact Filter.Eventually.of_forall (fun n => rfl)
  have hupper : Tendsto (fun n => C / (L n)^2) atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul
      (hinv.pow 2)
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero] using h
  have herr : Tendsto (fun n => (b n)^2 - r * (r + 1)) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero
      (fun n => progressionAlpha_scaled_sq_error_nonneg r (L n) hr (hL n))
      (fun n => progressionAlpha_scaled_sq_error r (L n) hr (hL n)) hupper
  have hsquare : Tendsto (fun n => (b n)^2) atTop (𝓝 (r * (r + 1))) := by
    have h := herr.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => r * (r + 1)) atTop (𝓝 (r * (r + 1))))
    simpa only [sub_add_cancel, zero_add] using h
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  have he (n : ℕ) : Real.sqrt ((b n)^2) = b n := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (hbpos n)]
  apply hsqrt.congr'
  apply Filter.Eventually.of_forall
  intro n
  change Real.sqrt ((b n)^2) = b n
  exact he n

end
end RiemannResearch.RH.CRTBlock
