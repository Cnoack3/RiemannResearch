import RiemannResearch.Analysis.ActualZeroSelbergDensity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Selberg slope two on a triangular Fourier window

We compare the actual ordinate trace with the Landau trace of the same
zero occurrences. The zero-density estimate at exponent two is a hypothesis.
The fourth moment of the triangular weight supplies the exact integration
constant in the resulting mean-square upper bound. The input and Fourier
normalizations are those of `ActualZeroSelbergDensity`; compare the
Ford–Meng–Zaharescu ordinate comparison in Lemma 2 of arXiv:1511.06814.
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem triangular_fourth_moment :
    (∫ x in (-1 : ℝ)..1, (1 - |x|) * x ^ 4) = 1 / 15 := by
  let f : ℝ → ℝ := fun x => (1 - |x|) * x ^ 4
  have hc : Continuous f := by dsimp [f]; fun_prop
  have he (x : ℝ) : f (-x) = f x := by
    simp only [f, abs_neg]
    ring
  have hn : (∫ x in (-1 : ℝ)..0, f x) = ∫ x in (0 : ℝ)..1, f x := by
    have h := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := 1)
    simpa only [he, neg_zero] using h.symm
  have hp : (∫ x in (0 : ℝ)..1, f x) = 1 / 30 := by
    let P : ℝ → ℝ := fun x => x ^ 5 / 5 - x ^ 6 / 6
    have hd : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt P (f x) x := by
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      have h := (((hasDerivAt_id x).pow 5).div_const 5).sub (((hasDerivAt_id x).pow 6).div_const 6)
      dsimp [P, f]
      rw [abs_of_nonneg hx.1]
      convert h using 1 <;> first | rfl | (dsimp only [id_eq]; ring) | ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)
    norm_num [P] at h
    exact h
  change (∫ x in (-1 : ℝ)..1, f x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1), hn, hp]
  norm_num

/-- Mean-square comparison on the rescaled window u = R x. Frequencies
satisfy |u| ≤ log T and the normalizer is the height T. -/
theorem selberg_two_triangular_trace_error {T R C : ℝ} (hT : 1 < T)
    (hR : 0 ≤ R) (hband : R ≤ Real.log T) (hC : 0 ≤ C)
    (hD : SelbergDensityBound T C 2) :
    (∫ x in (-1 : ℝ)..1, (1 - |x|) *
      ‖(ordinateSum T (R * x) - landauSum T (R * x)) / (T : ℂ)‖ ^ 2) ≤
      (2 * C * R ^ 2 / (3 * Real.log T)) ^ 2 / 15 := by
  let A := 2 * C * R ^ 2 / (3 * Real.log T)
  let e := fun x : ℝ => ‖(ordinateSum T (R * x) - landauSum T (R * x)) / (T : ℂ)‖
  have hlog : 0 < Real.log T := Real.log_pos hT
  have he : Continuous e := by
    dsimp [e, ordinateSum, landauSum, sum, ZeroOrdinate.phase]
    fun_prop
  have hb (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : e x ≤ A * x ^ 2 := by
    have hx' : |x| ≤ 1 := abs_le.mpr hx
    have hu : |R * x| ≤ (1 / 2 : ℝ) * (2 * Real.log T) := by
      rw [abs_mul, abs_of_nonneg hR]
      have := mul_le_mul_of_nonneg_left hx' hR
      linarith
    have h := normalized_ordinate_landau_error_of_selbergDensity_band T (R * x) C 2 (1 / 2)
      hT hC (by norm_num) (by norm_num) (by norm_num) hu hD
    calc
      e x ≤ _ := h
      _ = A * x ^ 2 := by dsimp [A]; ring
  have hlo : Continuous (fun x : ℝ => (1 - |x|) * e x ^ 2) := by fun_prop
  have hhi : Continuous (fun x : ℝ => A ^ 2 * ((1 - |x|) * x ^ 4)) := by fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (-1 : ℝ) ≤ 1)
    (hlo.intervalIntegrable (-1) 1) (hhi.intervalIntegrable (-1) 1) (fun x hx => by
      have hsq := pow_le_pow_left₀ (show 0 ≤ e x from norm_nonneg _) (hb x hx) 2
      have hw := mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr (abs_le.mpr hx))
      calc
        (1 - |x|) * e x ^ 2 ≤ _ := hw
        _ = A ^ 2 * ((1 - |x|) * x ^ 4) := by ring)
  rw [intervalIntegral.integral_const_mul, triangular_fourth_moment] at h
  change (∫ x in (-1 : ℝ)..1, (1 - |x|) * e x ^ 2) ≤ A ^ 2 / 15
  linarith only [h]

end RiemannResearch.Analysis.ActualZeroOrdinate
