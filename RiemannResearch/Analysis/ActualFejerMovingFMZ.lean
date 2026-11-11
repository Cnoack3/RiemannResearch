import RiemannResearch.Analysis.FejerSignedRemainder
import RiemannResearch.Analysis.RationalLandauMovingBand
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ActualUniformRationalLandau
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual moving FMZ tests from signed horizontal prefixes

The exact ordinate error is the horizontal comparison plus the full complex
Landau remainder. The latter is proved small uniformly for numerator
n <= T^θ, for every fixed 0 <= θ < 2/5. No Selberg or RH premise is used.

The final convergence theorem is a conditional research reduction:
the averaged signed-horizontal-prefix smallness assumption remains Open.
It does not assume the desired final Fourier remainder, an actual-zero DPP,
or Montgomery pair correlation. For geometric prime-power supports, take
n d = p^(d+1), m d = 1, and p^N <= T^θ. The complete symmetric real probe
remainder is the real part of the one-sided expression controlled here.

Source for the comparison framework: Ford--Meng--Zaharescu, Lemmas 1--2,
https://arxiv.org/html/1511.06814v2. The signed-prefix argument is elementary
summation by parts. See FMZ_Signed_Microscopic_Investigation_20261111.md
for the stronger external prime-power band and the remaining pair-square
and signed prime-correlation obligations.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open FejerSignedRemainder

def fejerHorizontalMode (T : ℝ) (n m : ℕ → ℕ) (d : ℕ) : ℂ :=
  (ordinateSum T (Real.log ((n d : ℝ) / (m d : ℝ))) -
    landauSum T (Real.log ((n d : ℝ) / (m d : ℝ)))) / (T : ℂ)

def fejerLandauMode (T : ℝ) (n m : ℕ → ℕ) (d : ℕ) : ℂ :=
  (landauSum T (Real.log ((n d : ℝ) / (m d : ℝ))) +
    ((T * rationalLandauMain (n d) (m d) : ℝ) : ℂ)) / (T : ℂ)

def fejerOrdinateMode (T : ℝ) (n m : ℕ → ℕ) (d : ℕ) : ℂ :=
  ordinateSum T (Real.log ((n d : ℝ) / (m d : ℝ))) / (T : ℂ) +
    (rationalLandauMain (n d) (m d) : ℂ)

theorem fejer_mode_exact (T : ℝ) (hT : T ≠ 0) (n m : ℕ → ℕ) :
    fejerOrdinateMode T n m = fun d => fejerHorizontalMode T n m d +
      fejerLandauMode T n m d := by
  funext d
  unfold fejerOrdinateMode fejerHorizontalMode fejerLandauMode
  have hc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
  push_cast
  field_simp
  ring

theorem fejer_remainder_exact (T : ℝ) (hT : T ≠ 0)
    (N : ℕ) (n m : ℕ → ℕ) :
    remainder N (fejerOrdinateMode T n m) =
      remainder N (fejerHorizontalMode T n m) + remainder N (fejerLandauMode T n m) := by
  rw [fejer_mode_exact T hT, remainder_add]

/-- Unconditional estimate. Only the signed horizontal prefixes remain unevaluated. -/
theorem eventually_fejer_ordinate_remainder_le (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ : θ < 2 / 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (N : ℕ) (n m : ℕ → ℕ),
      (∀ d < N, 1 ≤ m d ∧ m d < n d ∧ Real.log (n d : ℝ) ≤ θ * Real.log T) →
      ‖remainder N (fejerOrdinateMode T n m)‖ ≤
        2 / ((N : ℝ) + 1)^2 *
          ∑ k ∈ Finset.range N, ‖partialSum (fejerHorizontalMode T n m) (k+1)‖ +
        (N : ℝ) / ((N : ℝ) + 1) * (C / Real.log T) := by
  obtain ⟨C, hC, hc⟩ := eventually_rational_landau_error_power_band θ hθ0 hθ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hc, eventually_gt_atTop (1 : ℝ)] with T hc hT
  intro N n m hband
  rw [fejer_remainder_exact T (by linarith)]
  apply (norm_add_le _ _).trans
  apply add_le_add (norm_remainder_le_prefix N _)
  apply norm_remainder_le_modes
  intro d hd
  obtain ⟨hm, hmn, hn⟩ := hband d hd
  exact hc (n d) (m d) hm hmn hn

/-- A signed-prefix condition, independent of any Selberg or RH premise. -/
theorem tendsto_fejer_ordinate_of_horizontal_prefix
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : θ < 2 / 5)
    (N : ℝ → ℕ) (n m : ℝ → ℕ → ℕ)
    (hband : ∀ᶠ T : ℝ in atTop, ∀ d < N T,
      1 ≤ m T d ∧ m T d < n T d ∧ Real.log (n T d : ℝ) ≤ θ * Real.log T)
    (hsmall : Tendsto (fun T : ℝ =>
      (∑ k ∈ Finset.range (N T),
        ‖partialSum (fejerHorizontalMode T (n T) (m T)) (k+1)‖) /
        ((N T : ℝ) + 1)^2) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => remainder (N T) (fejerOrdinateMode T (n T) (m T)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hc⟩ := eventually_fejer_ordinate_remainder_le θ hθ0 hθ
  have hlog : Tendsto (fun T : ℝ => C / Real.log T) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul C
  have hl := (hsmall.const_mul 2).add hlog
  simp only [mul_zero, zero_add] at hl
  apply squeeze_zero_norm' _ hl
  filter_upwards [hc, hband, eventually_gt_atTop (1 : ℝ)] with T hc hb hT
  apply (hc (N T) (n T) (m T) hb).trans
  have hratio : (N T : ℝ) / ((N T : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N T : ℝ) + 1)).2
    linarith
  have hmain := mul_le_mul_of_nonneg_right hratio
    (show 0 ≤ C / Real.log T from div_nonneg hC.le (Real.log_pos hT).le)
  rw [one_mul] at hmain
  calc
    _ ≤ 2 / ((N T : ℝ) + 1)^2 *
        ∑ k ∈ Finset.range (N T), ‖partialSum (fejerHorizontalMode T (n T) (m T)) (k+1)‖ +
        C / Real.log T := add_le_add le_rfl hmain
    _ = _ := by ring

#print axioms eventually_fejer_ordinate_remainder_le
#print axioms tendsto_fejer_ordinate_of_horizontal_prefix
end RiemannResearch.Analysis.ActualZeroOrdinate
