/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualDistinctOrdinateProportion
import RiemannResearch.Analysis.ActualGramTwoNeighborIsolation

/-!
# Quantitative multiplicity-weighted lower bounds for distinct ordinates

All reflected pairs and all other occurrences at the same positive height
belong to one group. The denominator retains their analytic multiplicities.
See docs/DistinctOrdinateGram20261119.md for the finite rank and projection
argument and scripts/verify_distinct_ordinates.py for the angular certificate.
-/

noncomputable section
open Filter Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Analytic occurrence count at one exact positive height. -/
def ordinateMultiplicity (T γ : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun j : Copies T => copyOrdinate T j = γ).card

theorem copyOrdinate_mem_distinct (T : ℝ) (j : Copies T) :
    copyOrdinate T j ∈ distinctOrdinates T :=
  Finset.mem_image.mpr ⟨j.1.1, j.1.2, rfl⟩

theorem ordinateMultiplicity_pos {T γ : ℝ} (hγ : γ ∈ distinctOrdinates T) :
    0 < ordinateMultiplicity T γ := by
  classical
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hγ
  apply Finset.card_pos.mpr
  let j : Copies T := ⟨⟨z,hz⟩,⟨0,multiplicity_pos hz⟩⟩
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem sum_ordinateMultiplicity (T : ℝ) :
    ∑ γ ∈ distinctOrdinates T, ordinateMultiplicity T γ = Ncount 0 T := by
  classical
  calc
    _ = ∑ γ ∈ distinctOrdinates T, ∑ j : Copies T,
        if copyOrdinate T j = γ then 1 else 0 := by simp [ordinateMultiplicity]
    _ = ∑ j : Copies T, ∑ γ ∈ distinctOrdinates T,
        if copyOrdinate T j = γ then 1 else 0 := Finset.sum_comm
    _ = ∑ _ : Copies T, 1 := by
      apply Finset.sum_congr rfl
      intro j _
      simp [copyOrdinate_mem_distinct T j]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_copies,
        Nat.cast_id]

/-- The singleton count plus total multiplicity equals twice the number
of occupied heights plus the excess above multiplicity two. -/
theorem singleton_ordinate_partition (T : ℝ) :
    ((distinctOrdinates T).filter fun γ => ordinateMultiplicity T γ = 1).card + Ncount 0 T =
      2*(distinctOrdinates T).card + ∑ γ ∈ distinctOrdinates T, (ordinateMultiplicity T γ-2) := by
  classical
  have hh : ∑ γ ∈ distinctOrdinates T,
        ((if ordinateMultiplicity T γ = 1 then 1 else 0) + ordinateMultiplicity T γ) =
      ∑ γ ∈ distinctOrdinates T, (2 + (ordinateMultiplicity T γ-2)) := by
    apply Finset.sum_congr rfl
    intro γ hγ
    have h := ordinateMultiplicity_pos hγ
    split_ifs <;> omega
  simpa [Finset.sum_add_distrib, sum_ordinateMultiplicity, mul_comm] using hh

private def ordinateLaplace (W : IsolationGramWindow) (y : ℝ) : ℝ :=
  W.mixed y 0

private def positiveNorm (W : IsolationGramWindow) (y : ℝ) : ℝ :=
  1 + ordinateLaplace W (2 * y)

private def positiveCross (W : IsolationGramWindow) (x y : ℝ) : ℝ :=
  ordinateLaplace W (x+y) + ordinateLaplace W (x-y)

private def smallerEigenvalue (a b q : ℝ) : ℝ :=
  (a+b-Real.sqrt ((a-b)^2+4*q^2))/2

private def clippedPrice (t : ℝ) : ℝ := 4 - max (2-t) 0 ^ 2

private def realReferencePrice (W : IsolationGramWindow) (z : ℝ) : ℝ :=
  clippedPrice (1-2 * ordinateLaplace W z ^ 2 / positiveNorm W z)

private def projectedRightPrice (W : IsolationGramWindow) (z y : ℝ) : ℝ :=
  clippedPrice (positiveNorm W y - positiveCross W y z ^ 2 / positiveNorm W z)

private def residualCredit (W : IsolationGramWindow) (z : ℝ) : ℝ :=
  min (4/3) (1+(1-realReferencePrice W z)/2)

/-- Exact allocation of the integer excess m−2 in the projected groups,
including two reflected pairs sharing a height with a real occurrence. -/
theorem ordinate_projection_credit {r n : ℕ} {h : ℝ} (hh : h ≤ 1)
    (hr : 3 ≤ r ∨ r = 2 ∧ 1 ≤ n) :
    (r : ℝ) * min (4/3) (1+(1-h)/2) + (n : ℝ)*h ≤ 2*(r : ℝ)+n-2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases hr with hr | ⟨rfl,hr⟩
  · have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
    have hp := mul_le_mul_of_nonneg_left
      (min_le_left (4/3 : ℝ) (1+(1-h)/2)) (Nat.cast_nonneg r)
    have hq := mul_le_mul_of_nonneg_left hh hn
    nlinarith only [hp,hq,hr']
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hr
    have hp := min_le_right (4/3 : ℝ) (1+(1-h)/2)
    have hq := mul_nonneg (sub_nonneg.mpr hn') (sub_nonneg.mpr hh)
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hp,hq]

/-- The three collision configurations that need an angular price. The
remaining multiplicity groups absorb their entire weak spectral price. -/
structure DistinctOrdinateMajorant (W : IsolationGramWindow) (z a ℓ : ℝ) : Prop where
  reference : realReferencePrice W z ≤ 1
  many : ∀ y : ℝ, 0 ≤ y → projectedRightPrice W z y - residualCredit W z ≤ ℓ * max (y-a) 0
  one : ∀ y : ℝ, 0 ≤ y → ∀ n : ℕ, n ∈ Finset.Icc 1 3 →
    clippedPrice (smallerEigenvalue (positiveNorm W y) n
      (Real.sqrt (2*n) * ordinateLaplace W y)) - n ≤ ℓ * max (y-a) 0
  two : ∀ y x : ℝ, 0 ≤ x → x ≤ y →
    clippedPrice (smallerEigenvalue (positiveNorm W x) (positiveNorm W y)
      (positiveCross W x y)) - 2 ≤ ℓ * max (y-a) 0

/-- Named paper input for grouping the full signed frame by its actual
imaginary coordinates and applying the pair-energy asymptotic. -/
def DistinctOrdinateGramTransfer (W : IsolationGramWindow) : Prop :=
  ∀ z a ℓ : ℝ, 0 ≤ z → 0 < a → 0 ≤ ℓ → DistinctOrdinateMajorant W z a ℓ →
    ∀ δ : ℝ, 0 < δ → ∀ᶠ T : ℝ in atTop,
      1 + W.energyFloor - W.reward - W.spanCharge - ℓ * kimRightExcess T a - δ ≤
        (2*(1-W.reward)) * (((distinctOrdinates T).card : ℝ)/(Ncount 0 T : ℝ))

def DistinctOrdinateCurve (W : IsolationGramWindow) (a ℓ : ℝ) : ℝ :=
  (1+W.energyFloor-W.reward-W.spanCharge -
    ℓ*(conreyStopLossProfile (2*Real.pi*a)/(4*Real.pi)))/(2*(1-W.reward))

/-- A bound for the number of distinct heights, including all possible
off-line collisions, follows from a window's three verified prices. -/
private theorem cumulativeDistinctOrdinate_of_excess (W : IsolationGramWindow)
    (hG : DistinctOrdinateGramTransfer W)
    {z a ℓ q D : ℝ} (hz : 0 ≤ z) (ha : 0 < a) (hℓ : 0 ≤ ℓ)
    (hM : DistinctOrdinateMajorant W z a ℓ) (hx : W.reward < 1)
    (hD : ∀ δ : ℝ, 0 < δ → ∀ᶠ T : ℝ in atTop, kimRightExcess T a ≤ D+δ)
    (hq : q ≤ (1+W.energyFloor-W.reward-W.spanCharge-ℓ*D)/(2*(1-W.reward))) :
    CumulativeDistinctOrdinateProportion q := by
  intro ε hε
  let d := 2*(1-W.reward)
  have hd : 0 < d := mul_pos (by norm_num) (sub_pos.mpr hx)
  let δ := d*ε/(1+ℓ)
  have h1 : 0 < 1+ℓ := by linarith
  have hδ : 0 < δ := div_pos (mul_pos hd hε) h1
  have hh : δ*(1+ℓ) = d*ε := div_mul_cancel₀ _ h1.ne'
  have he : ((1+W.energyFloor-W.reward-W.spanCharge-ℓ*D)/(2*(1-W.reward)))*d =
      1+W.energyFloor-W.reward-W.spanCharge-ℓ*D := div_mul_cancel₀ _ hd.ne'
  have ev : ∀ᶠ T : ℝ in atTop, (q-ε)*(Ncount 0 T : ℝ) ≤ ((distinctOrdinates T).card : ℝ) := by
    filter_upwards [hG z a ℓ hz ha hℓ hM δ hδ, hD δ hδ,
      eventually_count_pos] with T hg hc hn
    have hn' : 0 < (Ncount 0 T : ℝ) := by exact_mod_cast hn
    change 1+W.energyFloor-W.reward-W.spanCharge-ℓ*kimRightExcess T a-δ ≤
      d*(((distinctOrdinates T).card : ℝ)/(Ncount 0 T : ℝ)) at hg
    have hu := mul_le_mul_of_nonneg_left hc hℓ
    have hq' := mul_le_mul_of_nonneg_right hq hd.le
    apply (le_div_iff₀ hn').mp
    apply le_of_mul_le_mul_left _ hd
    nlinarith only [hh, he, hg, hu, hq']
  exact eventually_atTop.mp ev

/-- Conrey's fixed-strike bound yields the quantitative ordinate proportion. -/
theorem cumulativeDistinctOrdinate_of_gram (W : IsolationGramWindow)
    (hC : ConreyStopLossHypothesis) (hG : DistinctOrdinateGramTransfer W)
    {z a ℓ q : ℝ} (hz : 0 ≤ z) (ha : 0 < a) (hℓ : 0 ≤ ℓ)
    (hM : DistinctOrdinateMajorant W z a ℓ) (hx : W.reward < 1)
    (hq : q ≤ DistinctOrdinateCurve W a ℓ) : CumulativeDistinctOrdinateProportion q :=
  cumulativeDistinctOrdinate_of_excess W hG hz ha hℓ hM hx
    (fun _ hδ => kimRightExcess_eventually hC ha hδ) hq

/-- Vanishing microscopic mean displacement absorbs the complete collision
price, including at mutually coincident off-line ordinates. -/
theorem cumulativeDistinctOrdinate_of_microscopicMean (W : IsolationGramWindow)
    (hG : DistinctOrdinateGramTransfer W)
    (hμ : Tendsto (fun T : ℝ => microscopicExcess T 0) atTop (𝓝 0))
    {z a ℓ : ℝ} (hz : 0 ≤ z) (ha : 0 < a) (hℓ : 0 ≤ ℓ)
    (hM : DistinctOrdinateMajorant W z a ℓ) (hx : W.reward < 1) :
    CumulativeDistinctOrdinateProportion
      ((1+W.energyFloor-W.reward-W.spanCharge)/(2*(1-W.reward))) := by
  apply cumulativeDistinctOrdinate_of_excess W hG hz ha hℓ hM hx (D := 0) _ (by simp)
  intro δ hδ
  have hp : 0 < 4*Real.pi := by positivity
  filter_upwards [hμ.eventually (gt_mem_nhds (mul_pos hp hδ)), eventually_ge_atTop (1 : ℝ)]
    with T hT ht
  have hh : microscopicExcess T 0 = 4*Real.pi*kimRightExcess T 0 := by
    simpa only [mul_zero] using microscopicExcess_eq_four_pi_kimRightExcess ht (le_refl (0:ℝ))
  have hbound : kimRightExcess T 0 ≤ δ := by
    rw [hh] at hT
    exact le_of_mul_le_mul_left hT.le hp
  have hmono : kimRightExcess T a ≤ kimRightExcess T 0 := by
    unfold kimRightExcess
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply realSum_mono
    intro ρ _
    exact max_le_max (sub_le_sub_left ha.le _) le_rfl
  simpa only [zero_add] using hmono.trans hbound

inductive DistinctOrdinateGramCase
  | montgomeryTaylor | tenPoint
  deriving DecidableEq

def DistinctOrdinateGramCase.window : DistinctOrdinateGramCase → IsolationGramWindow
  | .montgomeryTaylor => tunedIsolationWindow []
  | .tenPoint => tenPointIsolationWindow

def DistinctOrdinateGramCase.reference : DistinctOrdinateGramCase → ℝ
  | .montgomeryTaylor => 64/100
  | .tenPoint => 641/1000

def DistinctOrdinateGramCase.strike : DistinctOrdinateGramCase → ℝ
  | .montgomeryTaylor => 795/1000
  | .tenPoint => 797/1000

def DistinctOrdinateGramCase.slope : DistinctOrdinateGramCase → ℝ
  | .montgomeryTaylor => 1762/100
  | .tenPoint => 1769/100

def DistinctOrdinateGramCase.lower : DistinctOrdinateGramCase → ℝ
  | .montgomeryTaylor => 83392118/(10:ℝ)^8
  | .tenPoint => 83449280/(10:ℝ)^8

def DistinctOrdinateGramCase.certificate (i : DistinctOrdinateGramCase) : Prop :=
  DistinctOrdinateMajorant i.window i.reference i.strike i.slope ∧
    i.lower ≤ DistinctOrdinateCurve i.window i.strike i.slope

theorem cumulativeDistinctOrdinate_of_case (i : DistinctOrdinateGramCase)
    (hC : ConreyStopLossHypothesis) (hG : DistinctOrdinateGramTransfer i.window)
    (hI : i.certificate) : CumulativeDistinctOrdinateProportion i.lower := by
  apply cumulativeDistinctOrdinate_of_gram i.window hC hG _ _ _ hI.1 _ hI.2
  · cases i <;> norm_num [DistinctOrdinateGramCase.reference]
  · cases i <;> norm_num [DistinctOrdinateGramCase.strike]
  · cases i <;> norm_num [DistinctOrdinateGramCase.slope]
  · cases i <;>
      norm_num [DistinctOrdinateGramCase.window, tunedIsolationWindow, tenPointIsolationWindow]

/-- The ten-point limiting coefficient simplifies to one half of one
plus the ten-point critical-line fraction. -/
theorem tenPoint_distinctOrdinate_of_microscopicMean
    (hG : DistinctOrdinateGramTransfer tenPointIsolationWindow)
    (hI : DistinctOrdinateGramCase.tenPoint.certificate)
    (hμ : Tendsto (fun T : ℝ => microscopicExcess T 0) atTop (𝓝 0)) :
    CumulativeDistinctOrdinateProportion ((1+tenPointCriticalFraction)/2) := by
  have h := cumulativeDistinctOrdinate_of_microscopicMean tenPointIsolationWindow hG hμ
    (z := DistinctOrdinateGramCase.tenPoint.reference)
    (a := DistinctOrdinateGramCase.tenPoint.strike)
    (ℓ := DistinctOrdinateGramCase.tenPoint.slope)
    (by norm_num [DistinctOrdinateGramCase.reference])
    (by norm_num [DistinctOrdinateGramCase.strike])
    (by norm_num [DistinctOrdinateGramCase.slope]) hI.1 (by norm_num [tenPointIsolationWindow])
  convert h using 1
  norm_num [tenPointIsolationWindow, tenPointCriticalFraction]

end RiemannResearch.Analysis.ActualZeroOrdinate
