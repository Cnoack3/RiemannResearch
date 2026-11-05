import RiemannResearch.RH.MertensEndpointEnvelope
import RiemannResearch.RH.MertensLeeLeongCriterion
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Wiener

/-!
# The leading Lee–Leong coefficient in a displacement bound

Lee–Leong, arXiv:2208.06141v5, Theorem 1.1, inequality (11) in the PDF,
gives an ordinary Mertens bound with a positive second-order correction.
We use part of this correction to dominate the signed witness pairing at
the full leading coefficient. The external estimate is an explicit premise.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity

/-- Every positive multiple of the square root of the VK profile eventually
dominates the double logarithm. -/
private theorem endpoint_loglog_le_sqrt (k : ℝ) (hk : 0 < k) :
    ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ≤ k * Real.sqrt (vkProfile x) := by
  filter_upwards [vkProfile_dominates_logLog_sq (k ^ 2) (sq_pos_of_pos hk),
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ))] with x h hV
  refine le_of_sq_le_sq ?_ (mul_nonneg hk.le (Real.sqrt_nonneg _))
  simpa only [mul_pow, Real.sq_sqrt hV] using h

/-- The logarithmic factor in the published estimate leaves one full
square root of the profile in the exponent after fixing its leading coefficient. -/
theorem mertens_endpoint_of_leeLeong (h : LeeLeongMertensEstimate) :
    ∀ᶠ x : ℝ in atTop, |M x| ≤
      Real.exp (-leeLeongRate * vkProfile x - Real.sqrt (vkProfile x)) * x := by
  have hbase : 0 < 5 / (3 * (53.99 : ℝ) ^ 3) := by positivity
  have hA : 0 < leeLeongRate := Real.rpow_pos_of_pos hbase _
  have hr : 0 < Real.log (53.99 : ℝ) := Real.log_pos (by norm_num)
  let k := leeLeongRate * Real.log 53.99 / 10
  have hk : 0 < k := by dsimp [k]; positivity
  have hk' : k < leeLeongRate * Real.log 53.99 / 5 := by
    dsimp only [k]
    linarith only [mul_pos hA hr]
  have hL := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hfac : ∀ᶠ x : ℝ in atTop, |M x| ≤ 25.85 * x * Real.log x *
      Real.exp (-(leeLeongRate *
        (1 - Real.log 53.99 / Real.log (Real.log x)) ^ (-(1 / 5 : ℝ)) * vkProfile x)) := by
    filter_upwards [eventually_ge_atTop (Real.exp (Real.exp (10.01 : ℝ))),
      hL.eventually (eventually_gt_atTop (Real.log (53.99 : ℝ)))] with x hx hlog
    change Real.log (53.99 : ℝ) < Real.log (Real.log x) at hlog
    have hδ : 0 ≤ 1 - Real.log 53.99 / Real.log (Real.log x) :=
      sub_nonneg.mpr ((div_le_one (hr.trans hlog)).mpr hlog.le)
    have he := (h x hx).le
    rw [Real.mul_rpow hbase.le (inv_nonneg.mpr hδ), Real.inv_rpow hδ,
      ← Real.rpow_neg hδ] at he
    exact he
  have hM := vk_second_order_of_variable_coefficient M leeLeongRate (Real.log 53.99)
    25.85 k hA (by norm_num) hk' hfac
  filter_upwards [hM, endpoint_loglog_le_sqrt k hk,
    hL.eventually (eventually_gt_atTop (0 : ℝ)),
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with x hx hl hlog hV hx0
  change 0 < Real.log (Real.log x) at hlog
  have hcorr : Real.sqrt (vkProfile x) ≤ k * (vkProfile x / Real.log (Real.log x)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hlog).mpr
    calc
      _ ≤ Real.sqrt (vkProfile x) * (k * Real.sqrt (vkProfile x)) :=
        mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg _)
      _ = k * Real.sqrt (vkProfile x) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hV]
  calc
    _ ≤ _ := hx
    _ ≤ x * Real.exp (-leeLeongRate * vkProfile x - Real.sqrt (vkProfile x)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hcorr])) hx0
    _ = _ := mul_comm _ _

/-- A pointwise bound with any secondary coefficient below 1/8 gives
the pure endpoint absolute moment. -/
theorem summable_endpoint_moment_of_displacement_bound (A D t : ℝ) (ht : t < 1 / 8)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (A * vkProfile (n : ℝ) + t * Real.sqrt (vkProfile (n : ℝ)))) :
    Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-A * vkProfile (n : ℝ) - Real.sqrt (vkProfile (n : ℝ)) / 8)) *
        |qSequence displacement n|) := by
  let C := |D|
  have hC : 0 ≤ C := abs_nonneg D
  have hgap : 0 < (1 / 8 - t) / 2 := by linarith
  apply (summable_inv_mul_log_sq.mul_left (C / zetaTwo)).of_norm_bounded_eventually_nat
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hd, hnat.eventually (endpoint_loglog_le_sqrt ((1 / 8 - t) / 2) hgap),
    eventually_ge_atTop (2 : ℕ)] with n hnD hlog hn
  let V := vkProfile (n : ℝ)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn := Real.log_pos hn1
  have hmajor : |qSequence displacement n| ≤ C * Real.exp (A * V + t * Real.sqrt V) :=
    hnD.trans (mul_le_mul_of_nonneg_right (le_abs_self D) (Real.exp_pos _).le)
  have he : Real.exp (-A * V - Real.sqrt V / 8) * |qSequence displacement n| ≤
      C * Real.exp ((t - 1 / 8) * Real.sqrt V) := by
    calc
      _ ≤ Real.exp (-A * V - Real.sqrt V / 8) * (C * Real.exp (A * V + t * Real.sqrt V)) :=
        mul_le_mul_of_nonneg_left hmajor (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hsave : Real.exp ((t - 1 / 8) * Real.sqrt V) ≤ 1 / (Real.log (n : ℝ)) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hlogn)).mpr
    have heq : Real.log (n : ℝ) ^ 2 = Real.exp (2 * Real.log (Real.log (n : ℝ))) := by
      rw [two_mul, Real.exp_add, Real.exp_log hlogn, pow_two]
    rw [heq, ← Real.exp_add]
    apply Real.exp_le_one_iff.mpr
    change Real.log (Real.log (n : ℝ)) ≤ ((1 / 8 - t) / 2) * Real.sqrt V at hlog
    linarith only [hlog]
  have hfin := he.trans (mul_le_mul_of_nonneg_left hsave hC)
  have hNN : 0 ≤ positiveQWeight n * ((n : ℝ) * Real.exp (-A * V - Real.sqrt V / 8)) *
      |qSequence displacement n| :=
    mul_nonneg (mul_nonneg (positiveQWeight_nonneg n) (mul_nonneg hn0.le (Real.exp_pos _).le))
      (by positivity)
  change ‖positiveQWeight n * ((n : ℝ) * Real.exp (-A * V - Real.sqrt V / 8)) *
      |qSequence displacement n|‖ ≤ (C / zetaTwo) * ((n : ℝ) * Real.log (n : ℝ) ^ 2)⁻¹
  rw [Real.norm_eq_abs, abs_of_nonneg hNN]
  calc
    _ = (positiveQWeight n * (n : ℝ)) *
        (Real.exp (-A * V - Real.sqrt V / 8) * |qSequence displacement n|) := by ring
    _ ≤ (positiveQWeight n * (n : ℝ)) * (C * (1 / Real.log (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hfin (mul_nonneg (positiveQWeight_nonneg n) hn0.le)
    _ = _ := by
      unfold positiveQWeight
      field_simp [zetaTwo_pos.ne', hn0.ne', hlogn.ne']
      <;> ring

/-- A square-root saving in the ordinary Mertens estimate suffices for signed
pairing against the pure endpoint moment of the physical displacement. -/
theorem residual_zero_of_endpoint_displacement_moment (A : ℝ) (hA : 0 < A)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ Real.exp (-A * vkProfile x - Real.sqrt (vkProfile x)) * x)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-A * vkProfile (n : ℝ) - Real.sqrt (vkProfile (n : ℝ)) / 8)) *
        |qSequence displacement n|)) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  classical
  choose p hp hprime using (fun j : ℕ => Nat.exists_infinite_primes (j + 2))
  let q : ℕ → ℕ := fun j => p j - 1
  have hq : Tendsto q atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with j hj
    have := hp j
    dsimp [q]; omega
  have hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1) := by
    apply Eventually.of_forall
    intro j
    have hqp : q j + 1 = p j := by have := hp j; dsimp [q]; omega
    rw [hqp]; exact (hprime j).squarefree
  have hqr : Tendsto (fun j => (q j : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hq
  let ε : ℕ → ℝ := fun j => Real.exp (-A * vkProfile (q j : ℝ) - Real.sqrt (vkProfile (q j : ℝ)))
  have hlarge : ∀ᶠ j : ℕ in atTop, 6 ≤ A * vkProfile (q j : ℝ) :=
    (Tendsto.const_mul_atTop hA (vkProfile_tendsto_atTop.comp hqr)).eventually (eventually_ge_atTop 6)
  have hε : ∀ᶠ j : ℕ in atTop, 0 < ε j ∧ ε j ≤ 1 ∧
      ε j * (1 + Real.log (1 / ε j)) ≤ 1 / 2 := by
    filter_upwards [hlarge] with j hj
    let V := vkProfile (q j : ℝ)
    change 6 ≤ A * V at hj
    have hu : 6 ≤ A * V + Real.sqrt V := by linarith [Real.sqrt_nonneg V]
    have he : ε j = Real.exp (-(A * V + Real.sqrt V)) := by
      dsimp [ε, V]; congr 1; ring
    rw [he]
    exact ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), exponential_entropy_small _ hu⟩
  obtain ⟨L, hL⟩ := eventually_atTop.1 hM
  have htail : ∀ᶠ j : ℕ in atTop, ∀ y : ℝ, (q j : ℝ) ≤ y → |M y| ≤ ε j * y := by
    filter_upwards [hqr.eventually (eventually_ge_atTop L),
      hqr.eventually vkProfile_eventually_mono] with j hj hmono y hy
    apply (hL y (hj.trans hy)).trans
    apply mul_le_mul_of_nonneg_right _ ((Nat.cast_nonneg (q j)).trans hy)
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left (hmono y hy) hA.le
    have h2 := Real.sqrt_le_sqrt (hmono y hy)
    linarith only [h1, h2]
  obtain ⟨K, hK, henv⟩ := errorEnvelope_eventually_le_vk_endpoint A hA
  let F : ℕ → ℝ := fun n => positiveQWeight n * (1 + |qSequence displacement n|)
  let H : ℕ → ℝ := fun n => positiveQWeight n * ((n : ℝ) *
    Real.exp (-A * vkProfile (n : ℝ) - Real.sqrt (vkProfile (n : ℝ)) / 8)) *
      (1 + |qSequence displacement n|)
  have hF : Summable F := by
    refine (positiveQWeight_summable.add (qSequence_product_summable qOne displacement).abs).congr ?_
    intro n
    by_cases hn : n = 0
    · subst n; simp [F, positiveQWeight]
    · simp [F, qOneSequence, hn, abs_mul, abs_of_nonneg (positiveQWeight_nonneg n), mul_add]
  have hconst : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-A * vkProfile (n : ℝ) - Real.sqrt (vkProfile (n : ℝ)) / 8))) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (positiveQWeight_nonneg n)
      (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)) _ (summable_vk_first_moment_constant A hA)
    intro n
    apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg n)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    exact Real.exp_le_exp.mpr (sub_le_self _ (div_nonneg (Real.sqrt_nonneg _) (by norm_num)))
  have hH : Summable H := by
    refine (hconst.add hd).congr ?_
    intro n
    dsimp only [H]
    ring
  apply residual_zero_of_summable_mertens_first_moment q hq ε hlegal hε htail
    (fun n => 2 * F n + K * H n) ((hF.mul_left 2).add (hH.mul_left K))
  filter_upwards [hq.eventually henv] with j hj n
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hj n) (positiveQWeight_nonneg n))
    (show 0 ≤ 1 + |qSequence displacement n| by positivity)
  apply h.trans
  dsimp only [F, H]
  exact le_of_eq (by ring)

/-- A Mertens estimate with a square-root margin suffices at the exact
leading exponent A in the physical displacement. -/
theorem riemannHypothesis_of_endpoint_displacement (A D : ℝ) (hA : 0 < A)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ Real.exp (-A * vkProfile x - Real.sqrt (vkProfile x)) * x)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (A * vkProfile (n : ℝ))) : RiemannHypothesis := by
  refine rh_of_zero_projection_residual (residual_zero_of_endpoint_displacement_moment A hA hM ?_)
  apply summable_endpoint_moment_of_displacement_bound A D 0 (by norm_num)
  simpa only [zero_mul, add_zero] using hd

/-- At A = (5/(3 · 53.99³))^(1/5), the printed Lee–Leong Mertens estimate
and the endpoint displacement bound imply Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_of_leeLeong_endpoint (h : LeeLeongMertensEstimate) (D : ℝ)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (leeLeongRate * vkProfile (n : ℝ))) : RiemannHypothesis :=
  riemannHypothesis_of_endpoint_displacement leeLeongRate D
    (Real.rpow_pos_of_pos (by positivity : 0 < 5 / (3 * (53.99 : ℝ) ^ 3)) _)
    (mertens_endpoint_of_leeLeong h) hd

/-- At the leading Lee–Leong coefficient, the pure weighted first moment is
equivalent to a vanishing projection residual. -/
theorem residual_zero_iff_leeLeong_endpoint_displacement_moment (h : LeeLeongMertensEstimate) :
    ZetaTwoOptimizerStage.limitingResidual = 0 ↔
    Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-leeLeongRate * vkProfile (n : ℝ) - Real.sqrt (vkProfile (n : ℝ)) / 8)) *
        |qSequence displacement n|) := by
  constructor
  · intro hr
    rw [displacement_eq_zero_of_residual_eq_zero hr]
    have hz (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by
      cases n <;> simp [qSequence]
    simp only [hz, abs_zero, mul_zero, summable_zero]
  · exact residual_zero_of_endpoint_displacement_moment leeLeongRate
      (Real.rpow_pos_of_pos (by positivity : 0 < 5 / (3 * (53.99 : ℝ) ^ 3)) _)
      (mertens_endpoint_of_leeLeong h)

/-- At the leading coefficient, convergence of the pure endpoint moment implies RH. -/
theorem riemannHypothesis_of_leeLeong_endpoint_displacement_moment (h : LeeLeongMertensEstimate)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-leeLeongRate * vkProfile (n : ℝ) - Real.sqrt (vkProfile (n : ℝ)) / 8)) *
        |qSequence displacement n|)) : RiemannHypothesis :=
  rh_of_zero_projection_residual ((residual_zero_iff_leeLeong_endpoint_displacement_moment h).mpr hd)

/-- The displacement may exceed the leading exponential by exp(t √Φ) for
any fixed t < 1/8 while still implying RH under the published arithmetic input. -/
theorem riemannHypothesis_of_leeLeong_endpoint_sqrt_displacement (h : LeeLeongMertensEstimate)
    (D t : ℝ) (ht : t < 1 / 8) (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (leeLeongRate * vkProfile (n : ℝ) + t * Real.sqrt (vkProfile (n : ℝ)))) :
    RiemannHypothesis :=
  riemannHypothesis_of_leeLeong_endpoint_displacement_moment h
    (summable_endpoint_moment_of_displacement_bound leeLeongRate D t ht hd)

end RiemannResearch.RH.QMertensFirstMoment
