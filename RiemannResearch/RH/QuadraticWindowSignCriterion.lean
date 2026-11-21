import RiemannResearch.Analysis.QuadraticWindowSqueeze
import RiemannResearch.RH.ParetoMobiusWindowPairing
import RiemannResearch.RH.ScreenedParityOneSided
import RiemannResearch.RH.QuadraticWindowCover
import RiemannResearch.RH.ParetoWindowExcess
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.QuadraticWindowMertens
import RiemannResearch.RH.ScreenedParityWindowCounts
import RiemannResearch.RH.QuadraticWindowClassicalMertens

/-! # Quadratic-window excursions of the limiting screened parity packet

A count of deep excursions on a cofinal sequence of physical windows controls
the complete Möbius pairing. Either sign may be controlled on each window.
The final theorems specialize the arithmetic rate to the published Lee–Leong
estimate and to the classical contour estimate proved in this repository.

Source: Christian Noack's Pareto quadratic-window handoff.
-/

noncomputable section

/-! ## The quadratic-window pairing for the limiting parity packet

Source: Christian Noack's quadratic-window handoff. The hypotheses measure the
actual first-moment tails of the projection residual, and the two finite Möbius
sums used by the canonical approximant. The conclusion identifies the Hilbert
vector itself.
-/

open Filter
open scoped Topology BigOperators InnerProductSpace
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- Two first-moment bounds and a quantitative Möbius estimate on the same
cofinal quadratic windows force the normalized screened parity packet to be one. -/
theorem normalizedScreenedTwo_eq_one_of_quadratic_window_tails
    (N : ℕ → ℕ) (ε δ : ℕ → ℝ) (A d C L : ℝ)
    (hN : Tendsto N atTop atTop) (hA : 0 < A) (hd : 0 < d) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hε : ∀ᶠ j in atTop, 0 ≤ ε j) (hδ : ∀ᶠ j in atTop, 0 ≤ δ j)
    (hrate : ∀ᶠ j in atTop, ε j ≤ L * Real.exp (-(5 * A + d) * Real.sqrt (Real.log (N j))))
    (hout : Tendsto (fun j => (N j : ℝ) * δ j) atTop (𝓝 0))
    (hM : ∀ᶠ j in atTop, ∀ t : ℕ, N j ≤ t →
      |∑ n ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius n : ℝ)| ≤ ε j * (t : ℝ))
    (hm : ∀ᶠ j in atTop, |mobiusReciprocalSum (N j)| ≤ ε j)
    (htails : ∀ᶠ j in atTop,
      let x : ℝ := N j
      let f := Real.exp (A * Real.sqrt (Real.log x))
      let K : ℕ := ⌈f ^ 2⌉₊
      (∑' n : ℕ, positiveWeight (n + N j) * |hilbertSequence limitResidual (n + N j)|) ≤
          C * f/x + δ j ∧
      (∑' n : ℕ, positiveWeight (n + K * (N j)) * |hilbertSequence limitResidual (n + K * (N j))|) ≤
          C * f/((K : ℝ) * x)+δ j) : normalizedScreenedTwo = hilbertOne := by
  have hzero : |inner ℝ limitResidual hilbertOne| = 0 := by
    apply RiemannResearch.Analysis.quadratic_window_budget_squeeze N ε δ A d C L _
      hN hA hd hC hL (abs_nonneg _) hε hδ hrate hout
    filter_upwards [htails, hM, hm, hε, hδ, hN.eventually (eventually_gt_atTop 0)]
      with j htail hMj hmj hεj hδj hNj
    let x : ℝ := N j
    let f := Real.exp (A * Real.sqrt (Real.log x))
    let K : ℕ := ⌈f ^ 2⌉₊
    have hf : 0 < f := Real.exp_pos _
    simpa only [Nat.cast_add, Nat.cast_one] using
      annihilator_mean_abs_le_mobius_window limitResidual limitResidual_mem_orthogonal (N j) K
        hNj (ε j) (C * f/x) (C * f/((K : ℝ) * x)) (δ j) hεj (by positivity) hδj
        hMj hmj htail.1 htail.2
  have hE : limitEnergy = 0 := limitResidual_inner_one.symm.trans (abs_eq_zero.mp hzero)
  have herr := normalizedScreenedTwo_error_sq_eq_limitEnergy
  rw [hE, zero_div, pow_two, mul_eq_zero, or_self, norm_eq_zero, sub_eq_zero] at herr
  exact herr

end RiemannResearch.RH.Pareto.PrimePowerSchur

/-! ## Deep excursions of either sign of the limiting screened packet

The cofinal count concerns the physical coordinates of the Hilbert projection.
The analytic input bounds the ordinary and reciprocal Möbius partial sums.
Source: Christian Noack's Pareto quadratic-window handoff.
-/

open Filter
open scoped BigOperators Topology InnerProductSpace
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

private theorem post_square_tail_bound (N : ℕ) (hN : 0 < N) :
    (∑' k : ℕ, positiveWeight (k + N ^ 2 + 1) * |hilbertSequence limitResidual (k + N ^ 2 + 1)|) ≤
      ‖hilbertTailShift limitResidual (N ^ 2)‖ / (N : ℝ) := by
  let T := ∑' k : ℕ, positiveWeight (k + N ^ 2 + 1) * |hilbertSequence limitResidual (k + N ^ 2 + 1)|
  let V := ‖hilbertTailShift limitResidual (N ^ 2)‖
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have h : T ^ 2 ≤ V ^ 2/((N:ℝ) ^ 2 + 1) := by
    rw [show (N : ℝ) ^ 2 = ((N ^ 2 : ℕ) : ℝ) by norm_cast]
    exact pareto_absolute_tail_sq_le limitResidual (N ^ 2)
  have hT : 0 ≤ T := tsum_nonneg (fun k => mul_nonneg (positiveWeight_nonneg _) (abs_nonneg _))
  have hV : 0 ≤ V := norm_nonneg _
  change T ≤ V / (N:ℝ)
  apply (sq_le_sq₀ hT (div_nonneg hV hn.le)).mp
  rw [div_pow]
  exact h.trans (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hn) (by linarith))

/-- An upper count for either sign on [N,N²] bounds the actual residual's
absolute first-moment tail uniformly at each intermediate cutoff H. -/
theorem screenedTwo_tail_le_of_quadratic_oneSided_count (N H : ℕ) (hN : 0 < N)
    (hNH : N ≤ H) (hHX : H ≤ N ^ 2) (F : ℝ) (hF : 1 ≤ F)
    (hcount : (((Finset.Icc N (N ^ 2)).filter
      (fun n => hilbertSequence normalizedScreenedTwo n < -F)).card : ℝ) ≤ F ^ 2 ∨
      (((Finset.Icc N (N ^ 2)).filter
      (fun n => F < hilbertSequence normalizedScreenedTwo n)).card : ℝ) ≤ F ^ 2) :
    (∑' k : ℕ, positiveWeight (k + H) * |hilbertSequence limitResidual (k + H)|) ≤
      256 * (1 + (1-limitEnergy) + ‖limitResidual‖) * F/(H:ℝ) +
        129 * ‖hilbertTailShift limitResidual (N ^ 2)‖/(N:ℝ) := by
  classical
  let L := N ^ 2 + 1 - H
  let W := (Finset.range L).image (fun k => k + H)
  let c := 1 - limitEnergy
  let C := 1 + c * F
  have hH : 0 < H := hN.trans_le hNH
  have hHR : (0:ℝ) < H := by exact_mod_cast hH
  have hc : 0 ≤ c := by
    change 0 ≤ 1 - limitEnergy
    rw [← limitProjection_norm_sq]
    exact sq_nonneg _
  have hF0 : 0 ≤ F := zero_le_one.trans hF
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hLH : L + H = N ^ 2 + 1 := by dsimp [L]; omega
  have hW {n : ℕ} (hn : n ∈ W) : H ≤ n ∧ n ≤ N ^ 2 := by
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    have hkl := Finset.mem_range.mp hk
    omega
  have hinj : Set.InjOn (fun k : ℕ => k + H) (↑(Finset.range L)) := by
    intro a _ b _ hab
    exact Nat.add_right_cancel hab
  have hneg (n : ℕ) : hilbertSequence (-limitResidual) n = -hilbertSequence limitResidual n := by
    rw [← anchoredEvaluationCLM_apply, map_neg, anchoredEvaluationCLM_apply]
  obtain ⟨z, horth, habs, hnorm, hcard⟩ : ∃ z : ThresholdHilbert, z ∈ closedSpaceᗮ ∧
      (∀ n, |hilbertSequence z n| = |hilbertSequence limitResidual n|) ∧
      ‖z‖ = ‖limitResidual‖ ∧
      ((W.filter (fun n => C < hilbertSequence z n)).card : ℝ) ≤ F ^ 2 := by
    rcases hcount with hlow | hhigh
    · refine ⟨limitResidual, limitResidual_mem_orthogonal, fun _ => rfl, rfl, ?_⟩
      refine (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans hlow
      intro n hn
      obtain ⟨hnW, hnz⟩ := Finset.mem_filter.mp hn
      obtain ⟨hHn, hnX⟩ := hW hnW
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hNH.trans hHn, hnX⟩, ?_⟩
      rw [limitResidual_at_pos_eq_screenedTwo n (hH.trans_le hHn)] at hnz
      change 1 + c * F < 1 - c * hilbertSequence normalizedScreenedTwo n at hnz
      apply lt_of_not_ge
      intro hn'
      linarith only [hnz, mul_le_mul_of_nonneg_left hn' hc]
    · refine ⟨-limitResidual, closedSpace.orthogonal.neg_mem limitResidual_mem_orthogonal,
        fun n => by rw [hneg n, abs_neg], norm_neg _, ?_⟩
      refine (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans hhigh
      intro n hn
      obtain ⟨hnW, hnz⟩ := Finset.mem_filter.mp hn
      obtain ⟨hHn, hnX⟩ := hW hnW
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hNH.trans hHn, hnX⟩, ?_⟩
      rw [hneg, limitResidual_at_pos_eq_screenedTwo n (hH.trans_le hHn)] at hnz
      change 1 + c * F < -(1 - c * hilbertSequence normalizedScreenedTwo n) at hnz
      apply lt_of_not_ge
      intro hn'
      linarith only [hnz, mul_le_mul_of_nonneg_left hn' hc]
  let excess := fun n => positiveWeight n * max (hilbertSequence z n-C) 0
  have hexc : (∑ k ∈ Finset.range L, excess (k + H)) ≤ F * ‖z‖/(H:ℝ) := by
    have hb := window_excess_sq_le_exception_count z W H hH (fun n hn => (hW hn).1) C hC
    have hb' : (∑ n ∈ W, excess n) ^ 2 ≤ (F * ‖z‖/(H:ℝ)) ^ 2 := by
      calc
        _ ≤ _ := hb
        _ ≤ (F ^ 2/(H:ℝ) ^ 2) * ‖z‖ ^ 2 := by gcongr
        _ = _ := by ring
    rw [show (∑ n ∈ W, excess n) = ∑ k ∈ Finset.range L, excess (k + H) from Finset.sum_image hinj] at hb'
    apply (sq_le_sq₀ _ (by positivity)).mp hb'
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (positiveWeight_nonneg _) (le_max_right _ _))
  have hmass : (∑ k ∈ Finset.range L, positiveWeight (k + H)) ≤ 1/(H:ℝ) := by
    rw [← positiveWeight_tail_tsum H hH]
    exact ((summable_nat_add_iff H).mpr positiveWeight_summable).sum_le_tsum _
      (fun k _ => positiveWeight_nonneg _)
  obtain ⟨q,hq,hb,hz,hl⟩ := quadraticWindowTest_exists H hH
  have hNHsq : N ^ 2 ≤ H ^ 2 := Nat.pow_le_pow_left hNH 2
  have h := annihilator_absolute_tail_le_window_excess q z hq
    horth H L (a := 1/32) (b := 4) (C := C) (by norm_num) hC hz
    (fun k hk => hl _ (by omega) (by omega)) hb
  simp only [habs] at h
  rw [hnorm] at hexc
  have ht : (∑' k : ℕ, positiveWeight (k + L + H) * |hilbertSequence limitResidual (k + L + H)|) ≤
      ‖hilbertTailShift limitResidual (N ^ 2)‖ / (N:ℝ) := by
    simpa only [Nat.add_assoc, hLH] using (show
      (∑' k : ℕ, positiveWeight (k + (N ^ 2 + 1))* |hilbertSequence limitResidual (k + (N ^ 2 + 1))|) ≤ _
      from by simpa only [Nat.add_assoc] using post_square_tail_bound N hN)
  have hCf : C ≤ (1 + c) * F := by dsimp [C]; linarith
  have hmass' : C * (∑ k ∈ Finset.range L, positiveWeight (k + H)) ≤ (1 + c) * F/(H:ℝ) :=
    (mul_le_mul_of_nonneg_left hmass hC).trans (by simpa only [mul_one_div] using div_le_div_of_nonneg_right hCf hHR.le)
  change (1/32:ℝ) * _ ≤ 2 * 4 * (C * _ + ∑ k ∈ Finset.range L, excess (k + H)) + (1/32 + 4)*_ at h
  change _ ≤ 256 * (1 + c + ‖limitResidual‖) * F/(H:ℝ) + 129 * ‖hilbertTailShift limitResidual (N ^ 2)‖/(N:ℝ)
  have step := h.trans (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add hmass' hexc) (by norm_num : 0 ≤ (2 * 4:ℝ)))
    (mul_le_mul_of_nonneg_left ht (by norm_num : 0 ≤ (1/32 + 4:ℝ))))
  have scaled := mul_le_mul_of_nonneg_left step (by norm_num : 0 ≤ (32:ℝ))
  calc
    _ = 32 * ((1 / 32 : ℝ) * (∑' k : ℕ, positiveWeight (k + H) *
      |hilbertSequence limitResidual (k + H)|)) := by ring
    _ ≤ 32 * (2 * 4 * ((1 + c) * F / (H : ℝ) + F * ‖limitResidual‖ / (H : ℝ)) +
      (1 / 32 + 4) * (‖hilbertTailShift limitResidual (N ^ 2)‖ / (N : ℝ))) := scaled
    _ = _ := by ring

/-- Cofinal quadratic windows with few deep sites of either sign force attainment.
The rate is supplied explicitly for both Möbius sums on that sequence. -/
theorem normalizedScreenedTwo_eq_one_of_quadratic_oneSided_count
    (N : ℕ → ℕ) (ε : ℕ → ℝ) (A d L : ℝ)
    (hN : Tendsto N atTop atTop) (hA : 0 < A) (hd : 0 < d) (hL : 0 ≤ L)
    (hε : ∀ᶠ j in atTop, 0 ≤ ε j)
    (hrate : ∀ᶠ j in atTop, ε j ≤ L * Real.exp (-(5 * A + d) * Real.sqrt (Real.log (N j))))
    (hM : ∀ᶠ j in atTop, ∀ t : ℕ, N j ≤ t →
      |∑ n ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius n : ℝ)| ≤ ε j * (t : ℝ))
    (hm : ∀ᶠ j in atTop, |mobiusReciprocalSum (N j)| ≤ ε j)
    (hcount : ∀ᶠ j in atTop,
      let F := Real.exp (A * Real.sqrt (Real.log (N j)))
      (((Finset.Icc (N j) ((N j) ^ 2)).filter
        (fun n => hilbertSequence normalizedScreenedTwo n < -F)).card : ℝ) ≤ F ^ 2 ∨
      (((Finset.Icc (N j) ((N j) ^ 2)).filter
        (fun n => F < hilbertSequence normalizedScreenedTwo n)).card : ℝ) ≤ F ^ 2) :
    normalizedScreenedTwo = hilbertOne := by
  let δ := fun j => 129 * ‖hilbertTailShift limitResidual ((N j) ^ 2)‖/(N j:ℝ)
  have hc : 0 ≤ 1 - limitEnergy := limitProjection_norm_sq ▸ sq_nonneg _
  have hN2 : Tendsto (fun j => (N j) ^ 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hN.eventually (eventually_ge_atTop b),
      hN.eventually (eventually_ge_atTop 1)] with j hb hj
    exact hb.trans (by nlinarith)
  have htail : Tendsto (fun j => ‖hilbertTailShift limitResidual ((N j) ^ 2)‖) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp
      ((hilbertTailShift_energy_tendsto_zero limitResidual).comp hN2)
    change Tendsto (fun j => Real.sqrt (‖hilbertTailShift limitResidual ((N j) ^ 2)‖ ^ 2))
      atTop (𝓝 (Real.sqrt 0)) at h
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using h
  have hout : Tendsto (fun j => (N j:ℝ)*δ j) atTop (𝓝 0) := by
    apply Tendsto.congr' _ (show Tendsto (fun j => 129 * ‖hilbertTailShift limitResidual ((N j) ^ 2)‖)
      atTop (𝓝 0) from by simpa using htail.const_mul 129)
    filter_upwards [hN.eventually (eventually_gt_atTop 0)] with j hj
    dsimp only [δ]
    field_simp [show (N j : ℝ) ≠ 0 by exact_mod_cast hj.ne']
  apply normalizedScreenedTwo_eq_one_of_quadratic_window_tails N ε δ A d
    (256 * (1 + (1-limitEnergy) + ‖limitResidual‖)) L hN hA hd (by positivity) hL hε
    (Filter.Eventually.of_forall (fun j => by dsimp [δ]; positivity)) hrate hout hM hm
  let t := fun j => Real.sqrt (Real.log (N j : ℝ))
  have hx : Tendsto (fun j => (N j:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have ht : Tendsto t atTop atTop := Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp hx)
  filter_upwards [hcount, hN.eventually (eventually_ge_atTop 1), ht.eventually_ge_atTop (2 * A)]
    with j hj hjN hjt
  let F := Real.exp (A * t j)
  let K := ⌈F ^ 2⌉₊
  have hNj : 0 < N j := by omega
  have hNr : (1:ℝ) ≤ N j := by exact_mod_cast hjN
  have hf : 1 ≤ F := Real.one_le_exp (mul_nonneg hA.le (Real.sqrt_nonneg _))
  have hK1 : 1 ≤ K := by
    have hh : F ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
    by_contra hh'
    have hk : K = 0 := by omega
    rw [hk,Nat.cast_zero] at hh
    nlinarith [sq_nonneg (F-1)]
  have hK : K ≤ N j := by
    apply Nat.ceil_le.mpr
    have hs : t j ^2 = Real.log (N j : ℝ) := Real.sq_sqrt (Real.log_nonneg hNr)
    have hf2 : F ^ 2 = Real.exp (2 * (A * t j)) := by
      dsimp only [F]
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hf2, ← Real.exp_log (show 0 < (N j:ℝ) by positivity)]
    apply Real.exp_le_exp.mpr
    have ht0 : 0 ≤ t j := Real.sqrt_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr hjt) ht0]
  have hNN : N j ≤ (N j) ^ 2 := by nlinarith
  have hNear := screenedTwo_tail_le_of_quadratic_oneSided_count (N j) (N j) hNj le_rfl hNN F hf hj
  have hFar := screenedTwo_tail_le_of_quadratic_oneSided_count (N j) (K * N j) hNj
    (by simpa using Nat.mul_le_mul_right (N j) hK1)
    (by simpa [pow_two] using Nat.mul_le_mul_right (N j) hK) F hf hj
  exact ⟨hNear, by simpa only [Nat.cast_mul] using hFar⟩

end RiemannResearch.RH.Pareto.PrimePowerSchur

/-! ## Pareto quadratic-window rigidity from the Lee–Leong estimate

Source: Christian Noack's quadratic-window handoff and Lee–Leong, Theorem 1.1.
-/

open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization
open RiemannResearch.NumberTheory.PrimeNumberTheorem RiemannResearch.Analysis
open RiemannResearch.RH.QMertensFirstMoment

/-- Under the stated published Mertens estimate, a cofinal family of quadratic
windows with at most F² deep sites of either sign gives equality of Hilbert vectors. -/
theorem normalizedScreenedTwo_eq_one_of_leeLeong_quadratic_oneSided_count
    (hLL : LeeLeongMertensEstimate) (N : ℕ → ℕ) (A : ℝ)
    (hN : Tendsto N atTop atTop) (hA : 0 < A)
    (hcount : ∀ᶠ j in atTop,
      let F := Real.exp (A * Real.sqrt (Real.log (N j : ℝ)))
      (((Finset.Icc (N j) ((N j) ^ 2)).filter
        (fun n => hilbertSequence normalizedScreenedTwo n < -F)).card : ℝ) ≤ F ^ 2 ∨
      (((Finset.Icc (N j) ((N j) ^ 2)).filter
        (fun n => F < hilbertSequence normalizedScreenedTwo n)).card : ℝ) ≤ F ^ 2) :
    normalizedScreenedTwo = hilbertOne := by
  let ε := fun j => 5 * Real.exp (-(5 * A + 1) * Real.sqrt (Real.log (N j : ℝ)))
  have h := hN.eventually (mobius_quadratic_window_rates_of_leeLeong hLL
    (5 * A + 1) (by linarith))
  apply normalizedScreenedTwo_eq_one_of_quadratic_oneSided_count N ε A 1 5 hN hA
    (by norm_num) (by norm_num)
    (Filter.Eventually.of_forall (fun j => by dsimp [ε]; positivity))
    (Filter.Eventually.of_forall (fun _ => le_rfl)) _ _ hcount
  · filter_upwards [h] with j hj
    exact hj.1
  · filter_upwards [h] with j hj
    exact hj.2

/-- The right tail of the conductor cutoff can be tested separately on each
physical window. No rate of norm convergence is needed. -/
theorem normalizedScreenedTwo_eq_one_of_frequent_finite_window_counts
    (hLL : LeeLeongMertensEstimate) (N : ℕ → ℕ) (A : ℝ) (hN : Tendsto N atTop atTop)
    (hA : 0 < A) (hfinite : ∀ᶠ j in atTop,
      let F := Real.exp (A * Real.sqrt (Real.log (N j : ℝ)))
      ∃ᶠ L : ℕ in atTop, ((Finset.Icc (N j) ((N j) ^ 2)).filter
        (fun n => hilbertSequence (fixedTwoTrial L) n < -F)).card ≤ ⌊F ^ 2⌋₊) :
    normalizedScreenedTwo = hilbertOne := by
  apply normalizedScreenedTwo_eq_one_of_leeLeong_quadratic_oneSided_count hLL N A hN hA
  filter_upwards [hfinite] with j hj
  let F := Real.exp (A * Real.sqrt (Real.log (N j : ℝ)))
  have h := screenedTwo_excursion_count_le_of_frequently (Finset.Icc (N j) ((N j) ^ 2))
    (-F) ⌊F ^ 2⌋₊ hj
  exact Or.inl ((Nat.cast_le.mpr h).trans (Nat.floor_le (sq_nonneg F)))

/-- If the packet differs from one, both signs have more than F² deep sites
on every sufficiently large quadratic window. -/
theorem screenedTwo_quadratic_excursions_eventually
    (hLL : LeeLeongMertensEstimate) (A : ℝ) (hA : 0 < A)
    (hu : normalizedScreenedTwo ≠ hilbertOne) :
    ∀ᶠ n : ℕ in atTop,
      let F := Real.exp (A * Real.sqrt (Real.log (n : ℝ)))
      F ^ 2 < (((Finset.Icc n (n ^ 2)).filter
        (fun k => hilbertSequence normalizedScreenedTwo k < -F)).card : ℝ) ∧
      F ^ 2 < (((Finset.Icc n (n ^ 2)).filter
        (fun k => F < hilbertSequence normalizedScreenedTwo k)).card : ℝ) := by
  classical
  let F := fun n : ℕ => Real.exp (A * Real.sqrt (Real.log (n : ℝ)))
  let lo := fun n : ℕ => (((Finset.Icc n (n ^ 2)).filter
    (fun k => hilbertSequence normalizedScreenedTwo k < -(F n))).card : ℝ)
  let hi := fun n : ℕ => (((Finset.Icc n (n ^ 2)).filter
    (fun k => F n < hilbertSequence normalizedScreenedTwo k)).card : ℝ)
  change ∀ᶠ n in atTop, (F n) ^ 2 < lo n ∧ (F n) ^ 2 < hi n
  by_contra hn
  have hbad := Filter.not_eventually.mp hn
  choose N hge hwin using (Filter.frequently_atTop.mp hbad)
  have hN : Tendsto N atTop atTop := tendsto_atTop.2 (fun b =>
    (eventually_ge_atTop b).mono (fun j hj => hj.trans (hge j)))
  apply hu (normalizedScreenedTwo_eq_one_of_leeLeong_quadratic_oneSided_count hLL N A hN hA _)
  apply Filter.Eventually.of_forall
  intro j
  change lo (N j) ≤ (F (N j)) ^ 2 ∨ hi (N j) ≤ (F (N j)) ^ 2
  by_cases h : (F (N j)) ^ 2 < lo (N j)
  · exact Or.inr (le_of_not_gt (fun h' => hwin j ⟨h,h'⟩))
  · exact Or.inl (le_of_not_gt h)

end RiemannResearch.RH.Pareto.PrimePowerSchur

/-! ## Cofinal negative excursion criterion at classical contour rates

Source: Christian Noack's quadratic-window handoff and the classical contour
estimate from the repository's prime-number-theorem development.
-/

open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- For this range of window depths the repository's classical contour theorem
discharges both Möbius bounds unconditionally. -/
theorem normalizedScreenedTwo_eq_one_of_classical_quadratic_oneSided_count
    (N : ℕ → ℕ) (A : ℝ) (hN : Tendsto N atTop atTop) (hA : 0 < A)
    (hAe : 5 * A < Quantitative.MobiusContour.contourEndpoint)
    (hcount : ∀ᶠ j in atTop,
      let F := Real.exp (A * Real.sqrt (Real.log (N j : ℝ)))
      (((Finset.Icc (N j) ((N j) ^ 2)).filter
        (fun n => hilbertSequence normalizedScreenedTwo n < -F)).card : ℝ) ≤ F ^ 2 ∨
      (((Finset.Icc (N j) ((N j) ^ 2)).filter
        (fun n => F < hilbertSequence normalizedScreenedTwo n)).card : ℝ) ≤ F ^ 2) :
    normalizedScreenedTwo = hilbertOne := by
  obtain ⟨c,hc,hce⟩ := exists_between hAe
  obtain ⟨C,hC,hbound⟩ := mobius_quadratic_window_rates_of_classical_contour c (by linarith) hce
  let ε := fun j => C * Real.exp (-c * Real.sqrt (Real.log (N j : ℝ)))
  have h := hN.eventually hbound
  apply normalizedScreenedTwo_eq_one_of_quadratic_oneSided_count N ε A (c-5 * A) C hN hA
    (by linarith) hC
    (Filter.Eventually.of_forall (fun j => by dsimp [ε]; positivity))
    (Filter.Eventually.of_forall (fun j => by
      dsimp [ε]
      rw [show 5 * A + (c - 5 * A) = c by ring])) _ _ hcount
  · filter_upwards [h] with j hj
    exact hj.1
  · filter_upwards [h] with j hj
    exact hj.2

end RiemannResearch.RH.Pareto.PrimePowerSchur
