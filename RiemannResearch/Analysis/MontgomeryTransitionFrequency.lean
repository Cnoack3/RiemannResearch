/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.MontgomeryFormFactor
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import RiemannResearch.Analysis.MontgomeryHorizontalPairing
import RiemannResearch.Analysis.WeightedSqrtTransfer
import RiemannResearch.Analysis.MontgomeryLoglogTransfer
import RiemannResearch.Analysis.MontgomeryHorizontalLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The transition of the raw Montgomery form factor

At phase frequency `(log log T + c) / 2`, the leading term of the complex
form factor tends to `exp (-c)`. The shrinking-frequency comparison carries
that value to the actual ordinates. The analytic input is the corrected
complex-zero estimate of Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh,
arXiv:2501.14545v3, §3, (3.5), for both ordinates in (0,T]. Its first line
supplies the sharper error below. The paper proves this input unconditionally.
The Lean theorems take the analytic estimate as a premise and give a raw
transition rate uniform for bounded shifts.
https://arxiv.org/html/2501.14545v3#S3.E5
-/

noncomputable section
open Filter Set
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open ActualZeroOrdinate MontgomeryHorizontalTransfer MontgomeryFormFactor

/-- Normalized form of the corrected complex-zero estimate of Baluyot, Goldston,
Suriajaya and Turnage-Butterbaugh, equation (3.5) for the cutoff (0,T].
See https://arxiv.org/abs/2501.14545v3. The additive error survives normalization. -/
def CorrectedComplexFormFactorEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ α ∈ Icc (0 : ℝ) 1,
    let spike := Real.exp (-2 * (α * Real.log T)) * Real.log T
    |sharpFormFactor T α - (spike + α)| ≤ C * (spike + 1) / Real.sqrt (Real.log T)

/-- The first line of BGSTB, arXiv:2501.14545v3, (3.5), for both ordinates in
`(0,T]`. The constant absorbs the fixed factors of `2π` in its two errors. -/
def BGSTBPositiveCutoffEstimate : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc (1 : ℝ) T,
    |(actualComplexPairSum T (Real.log x)).re -
      T / (2 * Real.pi) * (Real.log T ^ 2 / x ^ 2 + Real.log x)| ≤
      C * (T / (2 * Real.pi)) * (Real.log T / x ^ 2 + Real.sqrt (Real.log T))

private theorem exp_neg_two_mul (u : ℝ) : Real.exp (-2 * u) = 1 / Real.exp u ^ 2 := by
  rw [show -2 * u = -(u + u) by ring, Real.exp_neg, Real.exp_add]
  simp only [pow_two, one_div]

/-- Exact signed change of normalization for the positive-cutoff pair sum. -/
theorem sharpFormFactor_sub_main_eq_pair_remainder (T α : ℝ) (hT : 1 < T) :
    let L := Real.log T
    let u := α * L
    let x := Real.exp u
    sharpFormFactor T α - (Real.exp (-2 * u) * L + α) =
      ((actualComplexPairSum T (Real.log x)).re -
        T / (2 * Real.pi) * (L ^ 2 / x ^ 2 + Real.log x)) /
        (T * L / (2 * Real.pi)) := by
  let L := Real.log T
  let u := α * L
  let x := Real.exp u
  let k := T / (2 * Real.pi)
  have hk : 0 < k := div_pos (zero_lt_one.trans hT) (by positivity)
  have hd := mul_pos hk (Real.log_pos hT)
  have hmain : (1 / x ^ 2 * L + α) * (k * L) = k * (L ^ 2 / x ^ 2 + u) := by
    dsimp only [u]
    ring
  change sharpFormFactor T α - (Real.exp (-2 * u) * L + α) =
    ((actualComplexPairSum T (Real.log x)).re - k * (L ^ 2 / x ^ 2 + Real.log x)) /
      (T * L / (2 * Real.pi))
  rw [sharpFormFactor_eq_actualComplexPairSum, show Real.log x = u from Real.log_exp u,
    exp_neg_two_mul, show T * L / (2 * Real.pi) = k * L by dsimp [k]; ring,
    ← hmain, sub_div, mul_div_cancel_right₀ _ hd.ne']

/-- Normalizing the signed remainder in (3.5) preserves its sharper spike error. -/
theorem sharpFormFactor_bound_of_bgstb (h : BGSTBPositiveCutoffEstimate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ α ∈ Icc (0 : ℝ) 1,
      let decay := Real.exp (-2 * (α * Real.log T))
      |sharpFormFactor T α - (decay * Real.log T + α)| ≤
        C * (decay + 1 / Real.sqrt (Real.log T)) := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with T hb hT
  intro α hα
  let L := Real.log T
  let u := α * L
  let x := Real.exp u
  let k := T / (2 * Real.pi)
  have hTpos : 0 < T := lt_trans zero_lt_one hT
  have hL : 0 < L := Real.log_pos hT
  have hk : 0 < k := div_pos hTpos (by positivity)
  have hroot : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hx : x ∈ Icc (1 : ℝ) T := by
    constructor
    · exact Real.one_le_exp (mul_nonneg hα.1 hL.le)
    · calc
        Real.exp u ≤ Real.exp L := Real.exp_le_exp.mpr (by
          dsimp [u]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hα.2 hL.le)
        _ = T := Real.exp_log hTpos
  have herror : C * (1 / x ^ 2 + 1 / Real.sqrt L) * (k * L) =
      C * k * (L / x ^ 2 + Real.sqrt L) := by
    have hs : L / Real.sqrt L = Real.sqrt L := (div_eq_iff hroot.ne').2
      (by rw [← sq, Real.sq_sqrt hL.le])
    calc
      _ = C * k * (L / x ^ 2 + L / Real.sqrt L) := by ring
      _ = _ := by rw [hs]
  have hd := mul_pos hk hL
  change |sharpFormFactor T α - (Real.exp (-2 * u) * L + α)| ≤
    C * (Real.exp (-2 * u) + 1 / Real.sqrt L)
  rw [sharpFormFactor_sub_main_eq_pair_remainder T α hT]
  change |((actualComplexPairSum T (Real.log x)).re -
      k * (L ^ 2 / x ^ 2 + Real.log x)) / (T * L / (2 * Real.pi))| ≤
    C * (Real.exp (-2 * u) + 1 / Real.sqrt L)
  rw [exp_neg_two_mul, show T * L / (2 * Real.pi) = k * L by dsimp [k]; ring,
    abs_div, abs_of_pos hd, div_le_iff₀ hd, herror]
  exact hb x hx

/-- The sharper positive-cutoff estimate supplies the existing uniform hypothesis. -/
theorem correctedComplexFormFactorEstimate_of_bgstb (h : BGSTBPositiveCutoffEstimate) :
    CorrectedComplexFormFactorEstimate := by
  obtain ⟨C, hC, hbound⟩ := sharpFormFactor_bound_of_bgstb h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hb hL
  intro α hα
  let q := Real.exp (-2 * (α * Real.log T))
  have hLpos : 0 < Real.log T := lt_of_lt_of_le zero_lt_one hL
  have hs := Real.sqrt_pos.2 hLpos
  have hsL : Real.sqrt (Real.log T) ≤ Real.log T := by
    calc
      Real.sqrt (Real.log T) ≤ Real.sqrt (Real.log T ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hLpos.le (sub_nonneg.mpr hL)])
      _ = Real.log T := Real.sqrt_sq hLpos.le
  have hle : q + 1 / Real.sqrt (Real.log T) ≤
      (q * Real.log T + 1) / Real.sqrt (Real.log T) := by
    rw [le_div_iff₀ hs, add_mul, div_mul_cancel₀ _ hs.ne']
    exact add_le_add (mul_le_mul_of_nonneg_left hsL (Real.exp_pos _).le) le_rfl
  exact (hb α hα).trans ((mul_le_mul_of_nonneg_left hle hC).trans_eq
    (mul_div_assoc C _ _).symm)

/-- At this frequency the leading term of the complex form factor is exp(-c). -/
def transitionFrequency (c T : ℝ) : ℝ :=
  ((Real.log (Real.log T) + c) / 2) / Real.log T

private theorem transitionFrequency_mul_log (c T : ℝ) (hT : 1 < T) :
    transitionFrequency c T * Real.log T = (Real.log (Real.log T) + c) / 2 :=
  div_mul_cancel₀ _ (Real.log_pos hT).ne'

/-- At the transition the normalized complex spike is exactly constant in the height. -/
theorem transition_spike (c T : ℝ) (hT : 1 < T) :
    Real.exp (-2 * (transitionFrequency c T * Real.log T)) * Real.log T = Real.exp (-c) := by
  have hL := Real.log_pos hT
  rw [transitionFrequency_mul_log c T hT,
    show -2 * ((Real.log (Real.log T) + c) / 2) = -c - Real.log (Real.log T) by ring,
    Real.exp_sub, Real.exp_log hL, div_mul_cancel₀ _ hL.ne']

/-- Any fixed power of the iterated logarithm is negligible compared with log T. -/
theorem loglog_pow_div_log_tendsto_zero (n : ℕ) :
    Tendsto (fun T : ℝ => (Real.log (Real.log T)) ^ n / Real.log T) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT
  simp only [Function.comp_def, Real.exp_neg, Real.exp_log hT, div_eq_mul_inv]

private theorem transitionFrequency_tendsto_zero (c : ℝ) :
    Tendsto (transitionFrequency c) atTop (𝓝 0) := by
  have h := (((loglog_pow_div_log_tendsto_zero 1).add
    ((loglog_pow_div_log_tendsto_zero 0).const_mul c)).div_const 2)
  simpa only [mul_zero, zero_add, zero_div] using h.congr
    (fun T => by unfold transitionFrequency; simp only [pow_one, pow_zero]; ring)

private theorem transitionFrequency_rate (c : ℝ) :
    Tendsto (fun T => (transitionFrequency c T * Real.log T) ^ 2 * horizontalLogRate T)
      atTop (𝓝 0) := by
  have h := ((((loglog_pow_div_log_tendsto_zero 4).add
      ((loglog_pow_div_log_tendsto_zero 3).const_mul (2 * c))).add
      ((loglog_pow_div_log_tendsto_zero 2).const_mul (c ^ 2))).div_const 4)
  simp only [mul_zero, zero_add, zero_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  rw [transitionFrequency_mul_log c T hT]
  unfold horizontalLogRate
  ring

/-- Complex-zero transition limit from the uniform estimate. -/
theorem sharp_transition_limit_of_corrected_complex_estimate
    (hMT : CorrectedComplexFormFactorEstimate) (c : ℝ) :
    Tendsto (fun T => sharpFormFactor T (transitionFrequency c T)) atTop (𝓝 (Real.exp (-c))) := by
  obtain ⟨C, hC, hbound⟩ := hMT
  have ha := transitionFrequency_tendsto_zero c
  have herror : Tendsto (fun T => sharpFormFactor T (transitionFrequency c T) -
      (Real.exp (-c) + transitionFrequency c T)) atTop (𝓝 0) := by
    have hmajor : Tendsto (fun T => C * (Real.exp (-c) + 1) / Real.sqrt (Real.log T))
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
    apply squeeze_zero_norm' _ hmajor
    filter_upwards [hbound, eventually_gt_atTop (1 : ℝ),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (-c),
      ha.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with T hb hT hl hα
    change -c ≤ Real.log (Real.log T) at hl
    have hL := Real.log_pos hT
    have ha0 : 0 ≤ transitionFrequency c T :=
      div_nonneg (div_nonneg (by linarith) (by norm_num)) hL.le
    simpa only [Real.norm_eq_abs, transition_spike c T hT] using
      hb (transitionFrequency c T) ⟨ha0, hα⟩
  have hmain : Tendsto (fun T => Real.exp (-c) + transitionFrequency c T)
      atTop (𝓝 (Real.exp (-c))) := by
    simpa only [add_zero] using ha.const_add (Real.exp (-c))
  simpa only [sub_add_cancel, zero_add] using herror.add hmain

/-- The horizontal transfer gives the same limit for the actual ordinates. -/
theorem raw_transition_limit_of_corrected_complex_estimate
    (hMT : CorrectedComplexFormFactorEstimate) (c : ℝ) :
    Tendsto (fun T => formFactor T (transitionFrequency c T)) atTop (𝓝 (Real.exp (-c))) :=
  raw_limit_of_budget _ (Real.exp_pos _).le
    (horizontalBudget_div_height_tendsto_zero_of_loglog _ (transitionFrequency_rate c))
    (sharp_transition_limit_of_corrected_complex_estimate hMT c)

private theorem eventually_transition_window_bounds (A : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      let α := transitionFrequency c T
      let u := α * Real.log T
      let r := Real.log (Real.log T) ^ 2 / Real.sqrt (Real.log T)
      0 ≤ α ∧ α ≤ r ∧ r ≤ 1 ∧ 1 / Real.sqrt (Real.log T) ≤ r ∧
        |u| ≤ horizontalTailDecay T / 4 ∧
        Real.sqrt ((1 + u ^ 2) * horizontalLogRate T) ≤ 2 * r := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (max 1 A),
    (loglog_pow_div_log_tendsto_zero 2).eventually_le_const (by norm_num : (0 : ℝ) < 1 / 32),
    (loglog_pow_div_log_tendsto_zero 4).eventually_le_const zero_lt_one]
    with T hT hL1 hℓmax hband hsmall
  let L := Real.log T
  let ℓ := Real.log L
  let r := ℓ ^ 2 / Real.sqrt L
  change max 1 A ≤ ℓ at hℓmax
  change ℓ ^ 2 / L ≤ 1 / 32 at hband
  change ℓ ^ 4 / L ≤ 1 at hsmall
  have hℓ1 := (le_max_left 1 A).trans hℓmax
  have hℓA := (le_max_right 1 A).trans hℓmax
  have hL : 0 < L := Real.log_pos hT
  have hroot := Real.sqrt_pos.2 hL
  have hroot1 : 1 ≤ Real.sqrt L := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL1
  have hrootL : Real.sqrt L ≤ L := by
    nlinarith only [Real.sq_sqrt hL.le, mul_nonneg hroot.le (sub_nonneg.mpr hroot1)]
  have hℓsq : ℓ ≤ ℓ ^ 2 := by
    nlinarith only [mul_nonneg (zero_le_one.trans hℓ1) (sub_nonneg.mpr hℓ1)]
  have hr : 0 ≤ r := div_nonneg (sq_nonneg ℓ) hroot.le
  have hr2 : r ^ 2 = ℓ ^ 4 / L := by
    dsimp only [r]
    rw [div_pow, Real.sq_sqrt hL.le]
    ring
  have hr1 : r ≤ 1 := (sq_le_sq₀ hr zero_le_one).mp (by simpa only [hr2, one_pow] using hsmall)
  have hband' : ℓ ≤ horizontalTailDecay T / 4 := by
    change ℓ ≤ L / (8 * ℓ) / 4
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4),
      le_div_iff₀ (mul_pos (by norm_num) (zero_lt_one.trans_le hℓ1))]
    nlinarith only [(div_le_iff₀ hL).mp hband]
  intro c hc
  let α := transitionFrequency c T
  let u := α * L
  have hu : u = (ℓ + c) / 2 := transitionFrequency_mul_log c T hT
  have hu0 : 0 ≤ u := by linarith only [hu, (abs_le.mp hc).1, hℓA]
  have huℓ : u ≤ ℓ := by linarith only [hu, (abs_le.mp hc).2, hℓA]
  have hα : α = u / L := (mul_div_cancel_right₀ α hL.ne').symm
  have hα0 : 0 ≤ α := (div_nonneg hu0 hL.le).trans_eq hα.symm
  refine ⟨hα0, ?_, hr1,
    div_le_div_of_nonneg_right (hℓ1.trans hℓsq) hroot.le, ?_, ?_⟩
  · calc
      α = u / L := hα
      _ ≤ ℓ ^ 2 / L := div_le_div_of_nonneg_right (huℓ.trans hℓsq) hL.le
      _ ≤ r := div_le_div_of_nonneg_left (sq_nonneg ℓ) hroot hrootL
  · change |u| ≤ horizontalTailDecay T / 4
    rw [abs_of_nonneg hu0]
    exact huℓ.trans hband'
  · have hu2 := (sq_le_sq₀ hu0 (zero_le_one.trans hℓ1)).mpr huℓ
    calc
      Real.sqrt ((1 + u ^ 2) * horizontalLogRate T) ≤ Real.sqrt ((2 * r) ^ 2) := by
        apply Real.sqrt_le_sqrt
        change (1 + u ^ 2) * (ℓ ^ 2 / L) ≤ (2 * r) ^ 2
        calc
          _ ≤ (4 * ℓ ^ 2) * (ℓ ^ 2 / L) :=
            mul_le_mul_of_nonneg_right (by linarith only [hu2, hℓsq, hℓ1])
              (div_nonneg (sq_nonneg ℓ) hL.le)
          _ = _ := by rw [mul_pow, hr2]; ring
      _ = 2 * r := Real.sqrt_sq (mul_nonneg (by norm_num) hr)

/-- Uniform raw-ordinate transition on every bounded interval of shifts, with
an explicit rate. Only the complex-zero estimate is an analytic premise. -/
theorem raw_transition_uniform_rate_of_corrected_complex_estimate
    (hMT : CorrectedComplexFormFactorEstimate) (A : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ c : ℝ, |c| ≤ A →
      |formFactor T (transitionFrequency c T) - Real.exp (-c)| ≤
        K * (Real.log (Real.log T) ^ 2 / Real.sqrt (Real.log T)) := by
  obtain ⟨C, hC, hcomplex⟩ := hMT
  obtain ⟨D, hD, hcomparison⟩ := eventually_sqrt_formFactor_difference_loglog_band
  let H := C * (Real.exp A + 1)
  let M := Real.sqrt (Real.exp A + 1 + H)
  let B := 2 * D
  have hH : 0 ≤ H := mul_nonneg hC (by positivity)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hB : 0 < B := mul_pos (by norm_num) hD
  refine ⟨B ^ 2 + 2 * M * B + H + 1, by positivity, ?_⟩
  filter_upwards [hcomplex, hcomparison, eventually_transition_window_bounds A,
    eventually_gt_atTop (1 : ℝ)] with T hb hd hw hT
  intro c hc
  let α := transitionFrequency c T
  let r := Real.log (Real.log T) ^ 2 / Real.sqrt (Real.log T)
  obtain ⟨hα0, hαr, hr1, hrad, hband, hs⟩ := hw c hc
  have hr : 0 ≤ r := hα0.trans hαr
  have hα1 := hαr.trans hr1
  have hsp : Real.exp (-c) ≤ Real.exp A := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hc).1])
  have herror : |sharpFormFactor T α - (Real.exp (-c) + α)| ≤ H * r := by
    have he := hb α ⟨hα0, hα1⟩
    dsimp only at he
    rw [transition_spike c T hT] at he
    calc
      _ ≤ C * (Real.exp (-c) + 1) / Real.sqrt (Real.log T) := he
      _ ≤ H / Real.sqrt (Real.log T) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hsp]) hC) (Real.sqrt_nonneg _)
      _ = H * (1 / Real.sqrt (Real.log T)) := by ring
      _ ≤ H * r := mul_le_mul_of_nonneg_left hrad hH
  have hsharp : Real.sqrt (sharpFormFactor T α) ≤ M := by
    apply Real.sqrt_le_sqrt
    have hh : H * r ≤ H := by simpa using mul_le_mul_of_nonneg_left hr1 hH
    linarith only [(abs_le.mp herror).2, hsp, hα1, hh]
  have hdiff : |Real.sqrt (formFactor T α) - Real.sqrt (sharpFormFactor T α)| ≤ B * r := by
    rw [abs_sub_comm]
    exact (hd α hband).trans ((mul_le_mul_of_nonneg_left hs hD.le).trans_eq (by dsimp [B]; ring))
  have hBr := mul_nonneg hB.le hr
  have hpair := WeightedSqrtTransfer.abs_sub_le_of_sqrt (formFactor_nonneg hT α)
    (MontgomeryHorizontalPairing.sharpFormFactor_nonneg hT α) (sq_nonneg (B * r))
    (by rwa [Real.sqrt_sq hBr])
  rw [Real.sqrt_sq hBr] at hpair
  have hr2 : r ^ 2 ≤ r := by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr1)]
  have hraw : |formFactor T α - sharpFormFactor T α| ≤ (B ^ 2 + 2 * M * B) * r := by
    apply hpair.trans
    rw [mul_pow]
    calc
      _ ≤ B ^ 2 * r + (2 * M) * (B * r) := add_le_add
        (mul_le_mul_of_nonneg_left hr2 (sq_nonneg B))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsharp (by norm_num)) hBr)
      _ = _ := by ring
  calc
    |formFactor T α - Real.exp (-c)| =
        |(formFactor T α - sharpFormFactor T α) +
          (sharpFormFactor T α - (Real.exp (-c) + α)) + α| := by congr 1; ring
    _ ≤ |formFactor T α - sharpFormFactor T α| +
        |sharpFormFactor T α - (Real.exp (-c) + α)| + |α| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (B ^ 2 + 2 * M * B) * r + H * r + r := by
      rw [abs_of_nonneg hα0]
      exact add_le_add (add_le_add hraw herror) hαr
    _ = _ := by ring

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
