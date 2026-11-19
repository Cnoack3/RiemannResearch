/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualGramTwoNeighborIsolation

/-!
# Two-neighbor isolation without a horizontal-displacement source

The two possible weak eigenweights from two attached singleton frames can
be bounded using their own inner product. After crediting the gap allowance
both signed prices vanish under the scalar angular conditions below. The
optimal source-free window is a linear combination of two explicit cosines.
See RiemannResearch/RH/VariationalIsolation20261119.md and RiemannResearch/RH/BoundCertificateReplays20261119.md.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- The smaller eigenvalue of the sum-frame block is at most 1+k. Adding
the difference-frame price gives g(1+k)+g(1−k)=6−2k². -/
def IsolationGramWindow.zeroHorizontalPrice (W : IsolationGramWindow) (b : ℝ) : Prop :=
  1 ≤ 3 * W.pairLoss b ∧ 1 - W.mixed 0 (2*b) ^ 2 ≤ 2 * W.pairLoss b

theorem IsolationGramWindow.rightCost_eq_zero (W : IsolationGramWindow) {b : ℝ}
    (h : W.zeroHorizontalPrice b) (T : ℝ) : W.rightCost b T = 0 := by
  have hA : 1-3*W.pairLoss b ≤ 0 := by linarith only [h.1]
  have hB : 2*(1-W.mixed 0 (2*b)^2)-4*W.pairLoss b ≤ 0 := by linarith only [h.2]
  have hu (y : ℝ) : W.signedPenalty b y ≤ 0 :=
    max_le ((min_le_right _ _).trans hA) ((min_le_right _ _).trans hB)
  unfold rightCost
  have hz : (fun z : ℂ => if 1 / 2 < z.re then
      max (W.signedPenalty b ((z.re-1/2) * Real.log T / (2*Real.pi))) 0 else 0) = fun _ => 0 := by
    funext z
    rw [max_eq_right (hu _)]
    simp
  rw [hz]
  simp [realSum]

/-- The complete lower proportion when the reflected groups absorb their
own cost at every horizontal offset. -/
def IsolationGramWindow.zeroPriceCurve (W : IsolationGramWindow) (b : ℝ) : ℝ :=
  (W.energyFloor-W.spanCharge-W.pairLoss b)/(1-W.reward-W.pairLoss b)

theorem kimIsolationLower_of_zeroHorizontalPrice (W : IsolationGramWindow)
    (hW : W.energyInput) {b c : ℝ} (hb : W.admissibleGap b)
    (h : W.zeroHorizontalPrice b) (hc : 0 < c) (hcb : c ≤ b) :
    KimIsolationLower c (W.zeroPriceCurve b) := by
  intro ε hε
  let d := 1-W.reward-W.pairLoss b
  have hd : 0 < d := hb.denominator_pos
  have heq : W.zeroPriceCurve b*d = W.energyFloor-W.spanCharge-W.pairLoss b :=
    div_mul_cancel₀ _ hd.ne'
  filter_upwards [hW b hb c hc hcb (d*ε) (mul_pos hd hε)] with T hT
  rw [W.rightCost_eq_zero h T, sub_zero] at hT
  change W.energyFloor-W.spanCharge-W.pairLoss b-d*ε ≤ d*kimIsolatedProportion T c at hT
  apply le_of_mul_le_mul_left _ hd
  nlinarith only [hT, heq]

private def cyclicSinc (s : ℝ) : ℝ :=
  if s = 0 then 1 else Real.sin (Real.pi*s)/(Real.pi*s)

/-- Fourier transform of the unit-mass Montgomery–Taylor window at the
rational cutoffs in the certificate, away from its removable singularity. -/
private def mtAngularKernel (s : ℝ) : ℝ :=
  let t := Real.pi*s
  let θ := (Real.sqrt 2)⁻¹
  (Real.cos t - Real.sqrt 2*t*(Real.cos θ / Real.sin θ)*Real.sin t)/(1-2*t^2)

private def optimalCosineCoefficient (s : ℝ) : ℝ :=
  (1-ThmD.HD 1) * s^2 / (mtAngularKernel s * (s^2 - 1/(2*Real.pi^2)))

/-- The exact extremizer of K(C)²/(C(f)−1) in the unit-mass energy space.
Its price witness uses only scalar angular inequalities. -/
def variationalIsolationWindow (C : ℝ) : IsolationGramWindow :=
  let b := optimalCosineCoefficient C
  let a := 1-b*cyclicSinc C
  let k := a*mtAngularKernel C+b*((1+cyclicSinc (2*C))/2)
  { energyFloor := 1-(1-ThmD.HD 1)*k/mtAngularKernel C
    reward := 0
    spanCharge := 0
    density := fun t => a * (Real.cos (Real.sqrt 2*t) /
      (Real.sqrt 2 * Real.sin (Real.sqrt 2)⁻¹)) + b*Real.cos (2*Real.pi*C*t) }

inductive VariationalIsolationCase
  | fortyNineHundredths | half | elevenTwentieths | threeFifths | sixtyOneHundredths | limitLower
  deriving DecidableEq

def VariationalIsolationCase.gap : VariationalIsolationCase → ℝ
  | .fortyNineHundredths => 49/100 + 1/(10:ℝ)^8
  | .half => 1/2 + 1/(10:ℝ)^8
  | .elevenTwentieths => 11/20 + 1/(10:ℝ)^8
  | .threeFifths => 3/5 + 1/(10:ℝ)^8
  | .sixtyOneHundredths => 61/100 + 1/(10:ℝ)^8
  | .limitLower => 61701890/(10:ℝ)^8

def VariationalIsolationCase.lower : VariationalIsolationCase → ℝ
  | .fortyNineHundredths => 32175415/(10:ℝ)^8
  | .half => 30187816/(10:ℝ)^8
  | .elevenTwentieths => 18901531/(10:ℝ)^8
  | .threeFifths => 5214801/(10:ℝ)^8
  | .sixtyOneHundredths => 2184040/(10:ℝ)^8
  | .limitLower => 1/(10:ℝ)^8

def VariationalIsolationCase.certificate (i : VariationalIsolationCase) : Prop :=
  let W := variationalIsolationWindow i.gap
  W.admissibleGap i.gap ∧ W.zeroHorizontalPrice i.gap ∧ i.lower ≤ W.zeroPriceCurve i.gap

/-- The actual zero-array lower proportion for each certified cut, using
only the pair-energy input and the angular/numerical certificate. -/
theorem kimIsolationLower_of_variationalCase (i : VariationalIsolationCase)
    (hW : (variationalIsolationWindow i.gap).energyInput) (hI : i.certificate)
    {c : ℝ} (hc : 0 < c) (hcb : c ≤ i.gap) : KimIsolationLower c i.lower := by
  have hh := kimIsolationLower_of_zeroHorizontalPrice _ hW hI.1 hI.2.1 hc hcb
  intro ε hε
  filter_upwards [hh ε hε] with T ht
  exact (sub_le_sub_right hI.2.2 ε).trans ht

end RiemannResearch.Analysis.ActualZeroOrdinate
