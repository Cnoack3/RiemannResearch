import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualZeroBandCount
import RiemannResearch.Analysis.OrdinateLagPhase
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# Microscopic increments of fixed Fourier modes at actual zero occurrences

The forward shift is clipped at the height cutoff. The rational-mode input is
the unconditional actual-ordinate FMZ limit. The terminal strip estimate uses
the actual local zero count, with multiplicities. Ford, Meng and Zaharescu,
https://arxiv.org/abs/1511.06814, provide the classical one-point context.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Raw sum of the clipped forward increments of one ordinate character. -/
def clippedPhaseIncrement (T u h : ℝ) : ℂ :=
  ∑ j : Copies T, (ZeroOrdinate.phase u (min T (copyOrdinate T j + h)) -
    ZeroOrdinate.phase u (copyOrdinate T j))

private theorem phase_lipschitz (u a b : ℝ) :
    ‖ZeroOrdinate.phase u a - ZeroOrdinate.phase u b‖ ≤ |u| * |a-b| := by
  simpa only [OrdinateLagPhase.phase, ZeroOrdinate.phase, mul_comm Complex.I]
    using OrdinateLagPhase.phase_norm_sub_le u a b

/-- A finite Fourier approximation can have a nonzero microscopic increment
only if its absolute first frequency moment is sufficiently large. -/
theorem clippedFourierIncrement_norm_le {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (u : ι → ℝ) (T h : ℝ) (hh : 0 ≤ h) :
    ‖∑ k ∈ s, c k * clippedPhaseIncrement T (u k) h‖ ≤
      (Ncount 0 T : ℝ) * h * ∑ k ∈ s, ‖c k‖ * |u k| := by
  classical
  have hrow (v : ℝ) (j : Copies T) :
      ‖ZeroOrdinate.phase v (min T (copyOrdinate T j+h)) -
        ZeroOrdinate.phase v (copyOrdinate T j)‖ ≤ |v| * h := by
    apply (phase_lipschitz _ _ _).trans
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg v)
    have ht : copyOrdinate T j ≤ T := (mem_cutoff.mp j.1.property).2.2
    rw [abs_of_nonneg (sub_nonneg.mpr (le_min ht (by linarith)))]
    linarith [min_le_right T (copyOrdinate T j+h)]
  have hchar (v : ℝ) : ‖clippedPhaseIncrement T v h‖ ≤ (Ncount 0 T : ℝ) * (|v| * h) := by
    unfold clippedPhaseIncrement
    refine (_root_.norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _j : Copies T, |v| * h := Finset.sum_le_sum (fun j _ => hrow v j)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul]
  calc
    _ ≤ _ := _root_.norm_sum_le _ _
    _ ≤ ∑ k ∈ s, (Ncount 0 T : ℝ) * h * (‖c k‖ * |u k|) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      calc
        _ ≤ ‖c k‖ * ((Ncount 0 T : ℝ) * (|u k| * h)) :=
          mul_le_mul_of_nonneg_left (hchar _) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := (Finset.mul_sum ..).symm

/-- Only terminal copies contribute to the error from translating the character. -/
theorem clippedPhaseIncrement_error (T u h : ℝ) (hh : 0 ≤ h) :
    ‖clippedPhaseIncrement T u h - (ZeroOrdinate.phase u h - 1) * ordinateSum T u‖ ≤
      (Ncount (T-h) T : ℝ) * (|u| * h) := by
  classical
  have hadd (t : ℝ) : ZeroOrdinate.phase u (t+h) =
      ZeroOrdinate.phase u h * ZeroOrdinate.phase u t := by
    simp only [ZeroOrdinate.phase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have heq : clippedPhaseIncrement T u h - (ZeroOrdinate.phase u h - 1) * ordinateSum T u =
      ∑ j : Copies T, (ZeroOrdinate.phase u (min T (copyOrdinate T j + h)) -
        ZeroOrdinate.phase u (copyOrdinate T j + h)) := by
    rw [clippedPhaseIncrement, ordinateSum, sum_eq_copies, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    change _ - _ * ZeroOrdinate.phase u (copyOrdinate T j) = _
    rw [hadd]
    ring
  rw [heq]
  calc
    _ ≤ _ := _root_.norm_sum_le _ _
    _ ≤ ∑ j : Copies T, (if T-h < copyOrdinate T j then (1:ℝ) else 0) * (|u| * h) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : T-h < copyOrdinate T j
      · have ht := (mem_cutoff.mp j.1.property).2.2
        change copyOrdinate T j ≤ T at ht
        rw [if_pos hj, one_mul, min_eq_left (by linarith)]
        have hl := phase_lipschitz u T (copyOrdinate T j + h)
        rw [abs_of_nonpos (by linarith : T - (copyOrdinate T j + h) ≤ 0)] at hl
        exact hl.trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg u))
      · rw [if_neg hj, zero_mul, min_eq_right (by linarith), sub_self, norm_zero]
    _ ≤ _ := by
      rw [← Finset.sum_mul, Finset.sum_boole]
      exact mul_le_mul_of_nonneg_right (ActualZeroBandCount.copy_band_card_le T (T-h))
        (mul_nonneg (abs_nonneg _) hh)

private theorem scaled_exp_sub_one (c : ℂ) :
    Tendsto (fun T : ℝ => (Real.log T : ℂ) *
      (Complex.exp (c / (Real.log T : ℂ)) - 1)) atTop (𝓝 c) := by
  have hd : HasDerivAt (fun z : ℂ => Complex.exp (c*z)) c 0 := by
    simpa using (hasDerivAt_const_mul (x := (0 : ℂ)) c).cexp
  have hr : Tendsto (fun T : ℝ => 1 / Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hc : Tendsto (fun T : ℝ => (Real.log T : ℂ)⁻¹) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa [Function.comp_def, one_div] using (Complex.continuous_ofReal.tendsto 0).comp hr
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
      change (Real.log T : ℂ)⁻¹ ≠ 0
      exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne')
  simpa [Function.comp_def, smul_eq_mul, div_eq_mul_inv] using hd.tendsto_slope_zero.comp hc

/-- At each fixed nonnegative microscopic width b/log T, the scaled increment
of every positive rational character has its differentiated FMZ main term. -/
theorem tendsto_clippedPhaseIncrement_rational {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    {b : ℝ} (hb : 0 ≤ b) :
    let u := Real.log ((n : ℝ) / m)
    Tendsto (fun T : ℝ => (Real.log T : ℂ) / (T : ℂ) *
      clippedPhaseIncrement T u (b / Real.log T)) atTop
      (𝓝 (((u * b : ℝ) : ℂ) * Complex.I * rationalFMZMain n m)) := by
  dsimp only
  let u := Real.log ((n : ℝ) / m)
  let c : ℂ := ((u * b : ℝ) : ℂ) * Complex.I
  change Tendsto _ _ (𝓝 (c * rationalFMZMain n m))
  have hphase (T : ℝ) : ZeroOrdinate.phase u (b / Real.log T) =
      Complex.exp (c / (Real.log T : ℂ)) := by
    unfold ZeroOrdinate.phase c
    congr 1
    push_cast
    ring
  have hmain := (scaled_exp_sub_one c).mul (tendsto_centeredRationalOrdinate_div hn hm)
  have hm' : Tendsto (fun T : ℝ => (Real.log T : ℂ) / (T : ℂ) *
      ((ZeroOrdinate.phase u (b/Real.log T)-1) * ordinateSum T u)) atTop
      (𝓝 (c * rationalFMZMain n m)) := by
    apply hmain.congr
    intro T
    by_cases he : n = m
    · subst m
      simp [u, c, Nat.ne_of_gt (show 0 < n by omega), centeredRationalOrdinate,
        ZeroOrdinate.phase]
    · rw [hphase]
      simp only [centeredRationalOrdinate, if_neg he, sub_zero, u]
      ring
  have hwidth : Tendsto (fun T : ℝ => b / Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  obtain ⟨K, hK, hband⟩ := ActualZeroBandCount.exists_band_count_bound
  have herr : Tendsto (fun T : ℝ => (Real.log T : ℂ) / (T : ℂ) *
      (clippedPhaseIncrement T u (b / Real.log T) -
        (ZeroOrdinate.phase u (b / Real.log T)-1) * ordinateSum T u)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) :=
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero)
    have hc0 := h0.mul_const (2 * K * (|u| * b))
    apply squeeze_zero_norm' _ (by simpa using hc0)
    filter_upwards [eventually_ge_atTop (9:ℝ), hwidth.eventually_lt_const (by norm_num : (0:ℝ)<1)]
      with T hT hw
    have hp : 0 < T := by linarith
    have hl := Real.log_pos (show 1 < T by linarith)
    have hh : 0 ≤ b / Real.log T := div_nonneg hb hl.le
    have hc := hband T (b / Real.log T) hT hh (by linarith)
    have hs := clippedPhaseIncrement_error T u (b / Real.log T) hh
    have hh' : (Ncount (T-b/Real.log T) T : ℝ) ≤ (2*K) * Real.log T := hc.trans (by
      apply mul_le_mul_of_nonneg_right _ hl.le
      nlinarith only [mul_le_mul_of_nonneg_left hw.le hK.le])
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hl, abs_of_pos hp]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hl.le hp.le)
    calc
      _ ≤ ((2*K) * Real.log T) * (|u| * (b / Real.log T)) :=
        hs.trans (mul_le_mul_of_nonneg_right hh' (mul_nonneg (abs_nonneg _) hh))
      _ = _ := by field_simp
  have hfinal := herr.add hm'
  rw [zero_add] at hfinal
  apply hfinal.congr
  intro T
  ring

/-- info: 'RiemannResearch.Analysis.ActualZeroOrdinate.clippedFourierIncrement_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clippedFourierIncrement_norm_le

/-- info: 'RiemannResearch.Analysis.ActualZeroOrdinate.tendsto_clippedPhaseIncrement_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tendsto_clippedPhaseIncrement_rational

end RiemannResearch.Analysis.ActualZeroOrdinate
