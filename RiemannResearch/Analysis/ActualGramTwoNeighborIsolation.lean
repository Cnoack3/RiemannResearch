/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualConreyTwoNeighborIsolation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Isolation with clipped Gram traces and finite prescribed gaps

See RiemannResearch/RH/ClippedGramIsolation20261119.md and RiemannResearch/RH/FixedGapIsolation20261119.md
for the paper proofs of the finite trace inequality and the actual window
budget. Larger-gap windows use plain Jensen and exact Fourier energies.
The external interaction data are Knausgård's eight-point certificate and the
verified ten-point certificate of haakonrba. The numerical obligations in
this file are replayed by RiemannResearch/RH/BoundCertificateReplays20261119.md. Each source
input is explicit at its consumer.
-/

noncomputable section
open Filter Set MeasureTheory Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Lower bound for 2−C(f), interaction reward, span charge and the window
density on its support. -/
structure IsolationGramWindow where
  energyFloor : ℝ
  reward : ℝ
  spanCharge : ℝ
  density : ℝ → ℝ

def IsolationGramWindow.mixed (W : IsolationGramWindow) (y c : ℝ) : ℝ :=
  ∫ t in (-(1 : ℝ) / 2)..(1 / 2),
    W.density t * Real.cosh (2 * Real.pi * y * t) * Real.cos (2 * Real.pi * c * t)

def IsolationGramWindow.pairLoss (W : IsolationGramWindow) (c : ℝ) : ℝ :=
  1 - W.mixed 0 c ^ 2

private def weakEigenvalue (A s off : ℝ) : ℝ :=
  (A + s - Real.sqrt ((A - s) ^ 2 + 4 * off ^ 2)) / 2

private def weakEigenPrice (t : ℝ) : ℝ := 4 * t - t ^ 2

/-- The larger of the signed effective-rank costs of one or two simple
points attached to the same reflected pair. -/
def IsolationGramWindow.signedPenalty (W : IsolationGramWindow) (b y : ℝ) : ℝ :=
  let A := 1 + W.mixed (2 * y) 0
  let J := max (W.mixed y b) 0
  let p := W.pairLoss b
  let d := W.mixed 0 (2 * b)
  let one := weakEigenPrice (weakEigenvalue A 1 (Real.sqrt 2 * J)) - 2 - 3*p
  let two := weakEigenPrice (weakEigenvalue A 2 (2 * J)) + weakEigenPrice (1-d) - 4 - 4*p
  max (min one (1-3*p)) (min two (2*(1-d^2)-4*p))

/-- Full right-side copies dominate the distinct off-line groups. -/
def IsolationGramWindow.rightCost (W : IsolationGramWindow) (b T : ℝ) : ℝ :=
  realSum T (fun z => if 1 / 2 < z.re then
      max (W.signedPenalty b ((z.re - 1 / 2) * Real.log T / (2 * Real.pi))) 0 else 0) /
    (Ncount 0 T : ℝ)

/-- The weakest possible triple frame is compared with its positive
symmetric Rayleigh vector. Two residual eigenvalues with total at most t
have aggregate price at most 4t−t²/2. -/
def IsolationGramWindow.tripleResidual (W : IsolationGramWindow) (b : ℝ) : ℝ :=
  let k := W.mixed 0 b
  let d := W.mixed 0 (2 * b)
  2 - (d + Real.sqrt (d^2 + 8*k^2))/2

structure IsolationGramWindow.admissibleGap (W : IsolationGramWindow) (b : ℝ) : Prop where
  gap_pos : 0 < b
  gap_le_one : b ≤ 1
  pair_pos : 0 < W.mixed 0 b
  double_pos : 0 < W.mixed 0 (2*b)
  double_lower : ∀ v ∈ Icc (0 : ℝ) (2*b), W.mixed 0 (2*b) ≤ W.mixed 0 v
  triple_price : 4 * W.tripleResidual b - W.tripleResidual b ^ 2 / 2 <
    2 + 3 * W.pairLoss b
  denominator_pos : 0 < 1 - W.reward - W.pairLoss b

/-- The effective-rank estimate and pair-energy asymptotic for the actual
window, with the close-pair cost charged only to the complement of the
retained isolated set. The analysis of this named premise is in the notes. -/
def IsolationGramWindow.energyInput (W : IsolationGramWindow) : Prop :=
  ∀ b : ℝ, W.admissibleGap b → ∀ c : ℝ, 0 < c → c ≤ b →
    ∀ δ : ℝ, 0 < δ → ∀ᶠ T : ℝ in atTop,
      W.energyFloor - W.spanCharge - W.rightCost b T - W.pairLoss b - δ ≤
        (1 - W.reward - W.pairLoss b) * kimIsolatedProportion T c

def IsolationGramWindow.majorant (W : IsolationGramWindow) (b a ℓ : ℝ) : Prop :=
  ∀ y : ℝ, 0 ≤ y → max (W.signedPenalty b y) 0 ≤ ℓ * max (y - a) 0

def IsolationGramWindow.curve (W : IsolationGramWindow) (b a ℓ : ℝ) : ℝ :=
  (W.energyFloor - W.spanCharge - W.pairLoss b -
    ℓ * (conreyStopLossProfile (2 * Real.pi * a) / (4 * Real.pi))) /
    (1 - W.reward - W.pairLoss b)

def IsolationGramWindow.intervalCertificate (W : IsolationGramWindow) (b a ℓ k : ℝ) : Prop :=
  W.admissibleGap b ∧ W.majorant b a ℓ ∧ k ≤ W.curve b a ℓ

theorem IsolationGramWindow.rightCost_le (W : IsolationGramWindow) {b T a ℓ : ℝ}
    (hT : 1 ≤ T) (hℓ : 0 ≤ ℓ) (h : W.majorant b a ℓ) :
    W.rightCost b T ≤ ℓ * kimRightExcess T a := by
  let f (z : ℂ) := max ((z.re - 1 / 2) * Real.log T / (2 * Real.pi) - a) 0
  have hL := Real.log_nonneg hT
  unfold rightCost kimRightExcess
  calc
    _ ≤ realSum T (fun z => f z * ℓ) / (Ncount 0 T : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply realSum_mono
      intro z _
      by_cases hz : 1 / 2 < z.re
      · rw [if_pos hz, mul_comm (f z) ℓ]
        exact h ((z.re - 1 / 2) * Real.log T / (2 * Real.pi))
          (div_nonneg (mul_nonneg (sub_nonneg.mpr hz.le) hL) (by positivity))
      · rw [if_neg hz]
        exact mul_nonneg (le_max_right _ _) hℓ
    _ = _ := by rw [realSum_mul_const]; dsimp only [f]; ring

/-- The complete continuous coefficient at any fixed admissible gap bound. -/
theorem kimIsolationLower_of_gramMajorant (W : IsolationGramWindow)
    (hC : ConreyStopLossHypothesis) (hW : W.energyInput) {a ℓ b c : ℝ}
    (hb : W.admissibleGap b) (hmaj : W.majorant b a ℓ) (ha : 0 < a) (hℓ : 0 ≤ ℓ)
    (hc : 0 < c) (hcb : c ≤ b) : KimIsolationLower c (W.curve b a ℓ) := by
  intro ε hε
  let z := 1 - W.reward - W.pairLoss b
  have hz : 0 < z := hb.denominator_pos
  let δ := z * ε / (1 + ℓ)
  have hden : 0 < 1 + ℓ := by linarith
  have hδ : 0 < δ := div_pos (mul_pos hz hε) hden
  have he : δ * (1 + ℓ) = z * ε := div_mul_cancel₀ _ hden.ne'
  have hcurve : W.curve b a ℓ * z = W.energyFloor - W.spanCharge - W.pairLoss b -
      ℓ * (conreyStopLossProfile (2 * Real.pi * a) / (4 * Real.pi)) :=
    div_mul_cancel₀ _ hz.ne'
  filter_upwards [hW b hb c hc hcb δ hδ, kimRightExcess_eventually hC ha hδ,
    eventually_ge_atTop (1 : ℝ)] with T hE hK hT
  have hcost := (W.rightCost_le hT hℓ hmaj).trans (mul_le_mul_of_nonneg_left hK hℓ)
  change W.energyFloor - W.spanCharge - W.rightCost b T - W.pairLoss b - δ ≤
    z * kimIsolatedProportion T c at hE
  apply le_of_mul_le_mul_left _ hz
  nlinarith only [hcurve, hcost, hE, he]

private def cosineCorrection (cs : List ℤ) (den t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range cs.length, (cs.getD j 0 : ℝ) *
    Real.cos (2 * Real.pi * ((j : ℝ) + 1) * t)) / den

def knausgardEightIsolationWindow : IsolationGramWindow where
  energyFloor := 2 - 1327947272845 / (10 : ℝ) ^ 12
  reward := 8722 / (10 : ℝ) ^ 6
  spanCharge := 4389 / (10 : ℝ) ^ 6
  density := fun t => 1 + cosineCorrection
    [122290, -45012, 16241, 1887, 2711, 3731, -5307, 2982, -5153, 5358] (10 ^ 6) t

def tenPointIsolationWindow : IsolationGramWindow where
  energyFloor := 67206299948881203266318003264831248651423598405947 / (10 : ℝ) ^ 50
  reward := 78629501063688385648757192860 / 8388608000000000000000000000000
  spanCharge := 39745053312603427868508160000 / 8388608000000000000000000000000
  density := fun t => (Real.cos (Real.sqrt 2 * t) + cosineCorrection
    [14540341, -17051850, 6940151, 5482678, -200220, 3939293, -5615406, 3367926,
      -4987106, 5017749, -4274153, 5029336, -4508275, 744709, 541564, -371255]
    (10 ^ 9) t) / (Real.sqrt 2 * Real.sin (Real.sqrt 2)⁻¹)

/-- A mean-zero cosine perturbation of the Montgomery–Taylor window.
Jensen supplies the isolated frame reward with x=b=0. Orthogonality and
stationarity give the exact cost of every prescribed Fourier coefficient. -/
def tunedIsolationWindow (cs : List ℤ) : IsolationGramWindow where
  energyFloor := ThmD.HD 1 - ∑ j ∈ Finset.range cs.length,
    ((cs.getD j 0 : ℝ) / 10000)^2 *
      (1/2 - 1 / (4 * Real.pi^2 * ((j : ℝ) + 1)^2))
  reward := 0
  spanCharge := 0
  density := fun t => Real.cos (Real.sqrt 2*t) /
    (Real.sqrt 2 * Real.sin (Real.sqrt 2)⁻¹) + cosineCorrection cs 10000 t

/-- Each case has its own numerical inputs and certified threshold. -/
inductive FixedGapIsolationCase
  | eightMicroscopic | tenMicroscopic | twoThirds | sixth | quarter | third | twoFifths
  | nineTwentieths | half | elevenTwentieths | threeFifths | wide
  deriving DecidableEq

structure FixedGapIsolationRow where
  window : IsolationGramWindow
  gap : ℝ
  strike : ℝ
  slope : ℝ
  lower : ℝ

def FixedGapIsolationCase.row : FixedGapIsolationCase → FixedGapIsolationRow
  | .eightMicroscopic => ⟨knausgardEightIsolationWindow, 1 / 100000, 1439 / 1000, 7358 / 10000,
      673536406 / (10 : ℝ) ^ 9⟩
  | .tenMicroscopic => ⟨tenPointIsolationWindow, 1 / 100000, 36 / 25, 7348 / 10000,
      673637381 / (10 : ℝ) ^ 9⟩
  | .twoThirds => ⟨tenPointIsolationWindow, 831944 / (10 : ℝ) ^ 7, 1455 / 1000,
      6912 / 10000, 2 / 3⟩
  | .sixth => ⟨tenPointIsolationWindow, 1 / 6 + 1 / (10 : ℝ) ^ 8, 1519 / 1000,
      5529 / 10000, 64455851 / (10 : ℝ) ^ 8⟩
  | .quarter => ⟨tenPointIsolationWindow, 1 / 4 + 1 / (10 : ℝ) ^ 8, 1148 / 1000,
      8426 / 10000, 60369938 / (10 : ℝ) ^ 8⟩
  | .third => ⟨tunedIsolationWindow [859,-189,82,-46,29,-20,15,-11], 1/3 + 1/(10:ℝ)^8,
      841/1000, 14688/10000, 53929888/(10:ℝ)^8⟩
  | .twoFifths => ⟨tunedIsolationWindow [1322,-278,120,-67,43,-29,22,-17], 2/5 + 1/(10:ℝ)^8,
      695/1000, 18296/10000, 46427262/(10:ℝ)^8⟩
  | .nineTwentieths => ⟨tunedIsolationWindow [1772,-358,153,-85,54,-38,28,-21], 9/20 + 1/(10:ℝ)^8,
      622/1000, 19507/10000, 38986860/(10:ℝ)^8⟩
  | .half => ⟨tunedIsolationWindow [2320,-446,190,-105,67,-46,34,-26], 1/2 + 1/(10:ℝ)^8,
      574/1000, 19559/10000, 29675518/(10:ℝ)^8⟩
  | .elevenTwentieths => ⟨tunedIsolationWindow [2978,-540,228,-126,80,-55,41,-31],
      11/20 + 1/(10:ℝ)^8, 546/1000, 18460/10000, 18242429/(10:ℝ)^8⟩
  | .threeFifths => ⟨tunedIsolationWindow [3776,-638,267,-147,93,-64,47,-36], 3/5 + 1/(10:ℝ)^8,
      539/1000, 16910/10000, 4520996/(10:ℝ)^8⟩
  | .wide => ⟨tunedIsolationWindow [4048,-668,279,-153,97,-67,49,-38], 61485/100000,
      540/1000, 16314/10000, 1338/(10:ℝ)^8⟩

def FixedGapIsolationCase.certificate (i : FixedGapIsolationCase) : Prop :=
  i.row.window.intervalCertificate i.row.gap i.row.strike i.row.slope i.row.lower

theorem kimIsolationLower_of_fixedGapCase (i : FixedGapIsolationCase)
    (hC : ConreyStopLossHypothesis) (hW : i.row.window.energyInput) (hI : i.certificate)
    {c : ℝ} (hc : 0 < c) (hcb : c ≤ i.row.gap) : KimIsolationLower c i.row.lower := by
  have ha : 0 < i.row.strike := by cases i <;> norm_num [FixedGapIsolationCase.row]
  have hℓ : 0 ≤ i.row.slope := by cases i <;> norm_num [FixedGapIsolationCase.row]
  have hh := kimIsolationLower_of_gramMajorant i.row.window hC hW hI.1 hI.2.1 ha hℓ hc hcb
  intro ε hε
  filter_upwards [hh ε hε] with T ht
  exact (sub_le_sub_right hI.2.2 ε).trans ht

end RiemannResearch.Analysis.ActualZeroOrdinate
