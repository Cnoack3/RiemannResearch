import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import RiemannResearch.RH.CompensatedTwoCoefficientCriterion
import RiemannResearch.RH.ParetoMellinDilation
import RiemannResearch.RH.LocalizedMellinObstruction

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/- Source: user-provided continuation, 6 October 2026, Section 25
(target symbol and localized obstruction). The explicit shifted-source lift
and its arithmetic window estimate are not supplied by this module. -/

theorem mellin_doubleDilation (f : ThresholdHilbert) (s : ℂ) :
    paretoMellin (doubleDilation f) s =
      (2 : ℂ) ^ (1 - s) * paretoMellin f s := by
  simpa [doubleDilation, hilbertDilationContinuous_apply] using
    paretoMellin_dilation f 2 (by decide) s

theorem twoThreeDual_mellin (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin twoThreeDual s =
      (14 - 26 * (2 : ℂ) ^ (-s) + 12 * ((2 : ℂ) ^ (-s)) ^ 2) / s := by
  change paretoMellinContinuous s hs twoThreeDual = _
  rw [twoThreeDual, twoThreeRiesz_eq_dilation, map_add, map_sub,
    map_smul, map_smul, map_smul]
  change (14 : ℂ) * paretoMellin hilbertOne s -
      (13 : ℂ) * paretoMellin (doubleDilation hilbertOne) s +
      (3 : ℂ) * paretoMellin (doubleDilation (doubleDilation hilbertOne)) s = _
  rw [mellin_doubleDilation, mellin_doubleDilation,
    mellin_doubleDilation, paretoMellin_one s hs]
  have hp : (2 : ℂ) ^ (1 - s) = (2 : ℂ) * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0),
      Complex.cpow_one]
  rw [hp]
  ring

theorem twoThreeSymbol_ne_zero_of_norm_lt_one
    {z : ℂ} (hz : ‖z‖ < 1) :
    (14 - 26 * z + 12 * z ^ 2 : ℂ) ≠ 0 := by
  have h1 : (1 : ℂ) - z ≠ 0 := by
    intro he
    have hz1 : z = 1 := by linear_combination -he
    norm_num [hz1] at hz
  have h2 : (7 : ℂ) - 6 * z ≠ 0 := by
    intro he
    have hz7 : z = (7 / 6 : ℂ) := by linear_combination -(1 / 6 : ℂ) * he
    have hzn : ‖z‖ = (7 / 6 : ℝ) := by rw [hz7]; norm_num
    linarith
  have hfactor : (14 - 26 * z + 12 * z ^ 2 : ℂ) =
      (2 : ℂ) * (1 - z) * (7 - 6 * z) := by ring
  rw [hfactor]
  exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h2

/-- The compact target symbol never vanishes anywhere in the right half-plane. -/
theorem twoThreeSymbol_at_ne_zero_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    (14 - 26 * (2 : ℂ)^(-s) + 12 * ((2 : ℂ)^(-s))^2) ≠ 0 := by
  apply twoThreeSymbol_ne_zero_of_norm_lt_one
  have hnorm : ‖(2 : ℂ)^(-s)‖ = (2 : ℝ)^(-s.re) := by
    simpa only [Complex.ofReal_ofNat, Complex.neg_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (-s)
  rw [hnorm]
  calc
    (2 : ℝ)^(-s.re) < (2 : ℝ)^(0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    _ = 1 := by simp

theorem twoThreeDual_mellin_ne_zero (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) : paretoMellin twoThreeDual s ≠ 0 := by
  rw [twoThreeDual_mellin s hs]
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  exact div_ne_zero (twoThreeSymbol_at_ne_zero_of_re_pos s (by linarith)) hs0

/-- Compact-target analogue of the sharp constant-target obstruction.
The actual target Mellin numerator is derived above; no target-transform
provider is required. The explicit shifted-Mobius lift is not assembled here. -/
theorem twoThreeDual_exact_head_power_lower
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A)
    (n : ℕ) (hn : 1 ≤ n)
    (hhead : ∀ k, 0 < k → k < n →
      hilbertSequence f k = hilbertSequence twoThreeDual k)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (2 * s.re - 1) * ‖paretoMellin twoThreeDual s‖ ^ 2 *
      (n : ℝ) ^ (2 * s.re - 1) ≤ ‖twoThreeDual - f‖ ^ 2 := by
  have hfzero := paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz hf
  have heval : paretoMellin (twoThreeDual - f) s = paretoMellin twoThreeDual s := by
    change paretoMellinContinuous s hs (twoThreeDual - f) = _
    rw [map_sub]
    change paretoMellin twoThreeDual s - paretoMellin f s = _
    rw [hfzero, sub_zero]
  have hehead : ∀ k, 0 < k → k < n →
      hilbertSequence (twoThreeDual - f) k = 0 := by
    intro k hk hkn
    change hilbertSequenceLinear (twoThreeDual - f) k = 0
    rw [map_sub]
    change hilbertSequence twoThreeDual k - hilbertSequence f k = 0
    rw [hhead k hk hkn, sub_self]
  have h := mellin_zero_head_lower (twoThreeDual - f) n hn hehead s hs
  rwa [heval] at h

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open Filter
open scoped Topology
open RiemannResearch.Analysis.SubpolynomialWindow

/-- Conditional compact-target RH reduction. The finite certificate and its
complete norm bound are explicit arithmetic obligations. -/
theorem riemannHypothesis_of_cofinal_compact_exact_head_subpolynomial
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (f : ℕ → ThresholdHilbert) (n : ℕ → ℕ) (C : ℕ → ℝ) (K : ℝ)
    (hn : Tendsto (fun i => (n i : ℝ)) atTop atTop)
    (hf : ∀ i, f i ∈ hilbertLegalClosure A)
    (hhead : ∀ i k, 0 < k → k < n i →
      hilbertSequence (f i) k = hilbertSequence twoThreeDual k)
    (hC : ∀ i, 0 ≤ C i) (hK : 1 ≤ K)
    (hbound : ∀ i, ‖twoThreeDual - f i‖^2 ≤ C i + K)
    (hsub : Tendsto (fun i => Real.log (1+C i) / Real.log (n i : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have ha : 0 < 2*s.re-1 := by linarith
  have hc : 0 < (2*s.re-1) * ‖paretoMellin twoThreeDual s‖^2 :=
    mul_pos ha (pow_pos (norm_pos_iff.mpr (twoThreeDual_mellin_ne_zero s hs)) 2)
  have hn1 : ∀ᶠ i : ℕ in atTop, (1 : ℝ) ≤ (n i : ℝ) :=
    hn.eventually (eventually_ge_atTop 1)
  have hfloor : ∀ᶠ i : ℕ in atTop,
      ((2*s.re-1) * ‖paretoMellin twoThreeDual s‖^2) *
        (n i : ℝ)^(2*s.re-1) ≤ C i + K := by
    filter_upwards [hn1] with i hi
    exact (twoThreeDual_exact_head_power_lower A hA (hf i)
      (n i) (by exact_mod_cast hi) (hhead i) s hs hs1 hz).trans (hbound i)
  exact no_positive_power_floor (fun i => (n i : ℝ)) C K
    ((2*s.re-1) * ‖paretoMellin twoThreeDual s‖^2) (2*s.re-1)
    hn hC hK hc ha hsub hfloor

end RiemannResearch.RH.Pareto.CoefficientStabilization
