import RiemannResearch.Analysis.CesaroHilbertAdjoint
import RiemannResearch.Analysis.FirstMomentTails
import RiemannResearch.RH.ParetoGroupedSignedTails
import RiemannResearch.RH.CRTDelayedProjection

set_option autoImplicit false

/-!
# Actual conditional pulse pairings and their second tails

Source: user-provided three-generator strict-improvement argument.
The conditional Hilbert adjoint and the existing grouped signed-tail theorem
give the exact pulse correlation formula, with its summability requirements
discharged by actual Hilbert-space membership.
-/
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.RH.Pareto RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.Analysis.Cesaro RiemannResearch.Probability.ConditionalIID

def cesaroDual (g : ThresholdHilbert) : ℕ → ℝ :=
  hilbertSequence (cesaroOperator.adjoint g)

def cesaroDualTail (g : ThresholdHilbert) : ℕ → ℝ :=
  anchoredSignedTail (cesaroDual g)

def conditionalPulsePair (g : ThresholdHilbert) (d : ℕ) : ℝ :=
  ∑' k : ℕ, mixtureWeight (k + 1) *
    (conditionalSequence g (k + 1) * cesaro (meanPulse d) (k + 1))

theorem cesaroDual_square_summable (g : ThresholdHilbert) :
    Summable (fun n => positiveWeight n * cesaroDual g n ^ 2) :=
  hilbertSequence_square_summable _

@[simp] theorem cesaroDualTail_zero (g : ThresholdHilbert) :
    cesaroDualTail g 0 = 0 := anchoredSignedTail_zero _

theorem cesaroDual_positive (g : ThresholdHilbert) (n : ℕ) (hn : 0 < n) :
    cesaroDual g n = adjointSequence (conditionalSequence g) n :=
  cesaroOperator_adjoint_coordinate g n hn

/-- The first tail is the actual conditional adjoint tail, not an assumed transform. -/
theorem cesaroDual_signedCoefficient (g : ThresholdHilbert) (n : ℕ) (hn : 0 < n) :
    signedCoefficient (cesaroDual g) n =
      ∑' k : ℕ, mixtureWeight (n + k) / ((n + k : ℕ) : ℝ) *
        conditionalSequence g (n + k) := by
  unfold signedCoefficient
  rw [cesaroDual_positive g n hn]
  change weight n * adjointSequence (conditionalSequence g) n = _
  unfold adjointSequence
  exact mul_div_cancel₀ _ (by unfold weight; positivity)

/-- Two differences of the second tail recover the actual conditional coordinate. -/
theorem cesaroDualTail_second_difference (g : ThresholdHilbert) (n : ℕ) (hn : 0 < n) :
    cesaroDualTail g n - 2 * cesaroDualTail g (n + 1) + cesaroDualTail g (n + 2) =
      mixtureWeight n / (n : ℝ) * conditionalSequence g n := by
  have h₁ := anchoredSignedTail_difference (cesaroDual_square_summable g) hn
  have h₂ := anchoredSignedTail_difference (cesaroDual_square_summable g)
    (show 0 < n + 1 by omega)
  have h₃ := adjointSequence_recover (conditionalSequence g) (conditionalSequence_mem g) n hn
  have he (m : ℕ) (hm : 0 < m) :
      signedCoefficient (cesaroDual g) m = weight m * adjointSequence (conditionalSequence g) m := by
    unfold signedCoefficient
    rw [cesaroDual_positive g m hm]
    rfl
  rw [he n hn] at h₁
  rw [he (n + 1) (by omega)] at h₂
  change cesaroDualTail g n - cesaroDualTail g (n + 1) = _ at h₁
  change cesaroDualTail g (n + 1) - cesaroDualTail g (n + 1 + 1) = _ at h₂
  have hn₂ : n + 1 + 1 = n + 2 := by omega
  rw [hn₂] at h₂
  linarith

theorem meanPulse_eq_div_mod (d n : ℕ) (hd : 0 < d) :
    meanPulse d n = ((n / d % 2 : ℕ) : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := by positivity
  unfold meanPulse residueFraction
  rw [Nat.mul_comm 2 d, Nat.mod_mul]
  push_cast
  field_simp
  ring

theorem dilation_binary_eq_meanPulse (d : ℕ) (hd : 0 < d) :
    dilation d (residue 2) = fun n => (d : ℝ) * meanPulse d n := by
  funext n
  rw [meanPulse_eq_div_mod d n hd]
  rfl

/-- The full actual conditional pairing equals the physical adjoint pairing. -/
theorem conditionalPulsePair_eq_paretoInner (g : ThresholdHilbert) (d : ℕ) (hd : 0 < d) :
    conditionalPulsePair g d = paretoInner (cesaroDual g) (meanPulse d) := by
  obtain ⟨p, hp, hseq⟩ := legalSeedSpan_exists_hilbert (Set.Ici 1)
    (by intro a ha; exact ha) (meanPulse_legal d hd)
  have he : conditionalPulsePair g d = inner ℝ g (cesaroOperator p) := by
    rw [conditional_inner_weighted]
    unfold conditionalPulsePair
    apply tsum_congr
    intro k
    rw [conditionalSequence_cesaroOperator, hseq]
  rw [he, real_inner_comm]
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm, hilbert_inner_weighted, hseq]
  rfl

theorem cesaroDualTail_binary_summable (g : ThresholdHilbert) (d : ℕ) (hd : 0 < d) :
    Summable (fun j => cesaroDualTail g (d * (2 * j + 1)) -
      cesaroDualTail g (d * (2 * (j + 1)))) := by
  simpa only [cesaroDualTail, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
    binary_grouped_signedTail_summable (cesaroDual_square_summable g) hd

/-- Exact grouped correlation formula for the actual conditional pulse. -/
theorem conditionalPulsePair_eq_grouped (g : ThresholdHilbert) (d : ℕ) (hd : 0 < d) :
    conditionalPulsePair g d =
      ∑' j, (cesaroDualTail g (d * (2 * j + 1)) -
        cesaroDualTail g (d * (2 * (j + 1)))) := by
  rw [conditionalPulsePair_eq_paretoInner g d hd]
  have he := dyadic_pairing_eq_grouped_signedTail (cesaroDual_square_summable g) hd
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hx : paretoInner (cesaroDual g) (dilation d (residue 2)) =
      (d : ℝ) * paretoInner (cesaroDual g) (meanPulse d) := by
    rw [dilation_binary_eq_meanPulse d hd]
    unfold paretoInner
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  rw [hx] at he
  apply (mul_left_cancel₀ hdR)
  convert he using 1
  simp only [cesaroDualTail, Nat.mul_add, Nat.mul_one]

theorem conditionalPulsePair_cesaroOperator (f : ThresholdHilbert) (d : ℕ) :
    conditionalPulsePair (cesaroOperator f) d =
      conditionalMeanInner (hilbertSequence f) (meanPulse d) := by
  unfold conditionalPulsePair conditionalMeanInner
  apply tsum_congr
  intro k
  rw [conditionalSequence_cesaroOperator]
  change mixtureWeight (k + 1) *
      (cesaro (hilbertSequence f) (k + 1) * cesaro (meanPulse d) (k + 1)) =
    mixtureWeight (k + 1) * cesaro (hilbertSequence f) (k + 1) *
      cesaro (meanPulse d) (k + 1)
  ring

/-- The transform is attached to the exact physical sequence appearing in the energy. -/
theorem conditionalMeanInner_meanPulse_eq_grouped (F : ℕ → ℝ)
    (hF : Summable (fun n => positiveWeight n * F n ^ 2)) (hF0 : F 0 = 0)
    (d : ℕ) (hd : 0 < d) :
    conditionalMeanInner F (meanPulse d) =
      ∑' j, (cesaroDualTail (cesaroOperator (sequenceHilbert F hF)) (d * (2 * j + 1)) -
        cesaroDualTail (cesaroOperator (sequenceHilbert F hF)) (d * (2 * (j + 1)))) := by
  have h := conditionalPulsePair_eq_grouped (cesaroOperator (sequenceHilbert F hF)) d hd
  rw [conditionalPulsePair_cesaroOperator, hilbertSequence_sequenceHilbert F hF hF0] at h
  exact h

end RiemannResearch.RH.CRTBlock

open Filter
open scoped BigOperators Topology
noncomputable section

namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.RH.Pareto RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.Analysis RiemannResearch.Analysis.Cesaro
open RiemannResearch.Probability.ConditionalIID

/-- Decay of the conditional means gives a quantitative first-tail bound.
The exact uniform-mixture marginal performs the complete infinite tail sum. -/
theorem cesaroDual_signedCoefficient_abs_le
    (g : ThresholdHilbert) (B : ℝ) (hB : 0 ≤ B)
    (hG : ∀ t : ℕ, 0 < t → |conditionalSequence g t| ≤ B / (t : ℝ))
    (n : ℕ) (hn : 0 < n) :
    |signedCoefficient (cesaroDual g) n| ≤ weight n * (B / (n : ℝ)) := by
  have hs := adjointTail_summable (conditionalSequence g) (conditionalSequence_mem g) n hn
  have hm := hasSum_uniform_mixture_marginal n hn
  rw [cesaroDual_signedCoefficient g n hn]
  calc
    _ ≤ ∑' k : ℕ, |mixtureWeight (n+k) / ((n+k : ℕ) : ℝ) *
        conditionalSequence g (n+k)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k : ℕ, (mixtureWeight (n+k) / ((n+k : ℕ) : ℝ)) * (B / (n : ℝ)) := by
      apply hs.abs.tsum_le_tsum _ (hm.summable.mul_right (B / (n : ℝ)))
      intro k
      have hq : 0 ≤ mixtureWeight (n+k) / ((n+k : ℕ) : ℝ) :=
        div_nonneg (mixtureWeight_nonneg _) (Nat.cast_nonneg _)
      rw [abs_mul, abs_of_nonneg hq]
      apply mul_le_mul_of_nonneg_left _ hq
      exact (hG (n+k) (by omega)).trans
        (div_le_div_of_nonneg_left hB (by positivity) (by exact_mod_cast Nat.le_add_right n k))
    _ = _ := by rw [tsum_mul_right, hm.tsum_eq]

/-- The conditional adjoint has a finite first absolute moment whenever
the physical conditional means are bounded by B/t. -/
theorem cesaroDual_firstMoment_of_decay
    (g : ThresholdHilbert) (B : ℝ) (hB : 0 ≤ B)
    (hG : ∀ t : ℕ, 0 < t → |conditionalSequence g t| ≤ B / (t : ℝ)) :
    Summable (fun n : ℕ => (n : ℝ) * |signedCoefficient (cesaroDual g) n|) := by
  apply (positiveWeight_summable.mul_left B).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))]
  by_cases hn : n = 0
  · simp [hn, positiveWeight]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnreal : (n : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ (n : ℝ) * (weight n * (B / (n : ℝ))) :=
      mul_le_mul_of_nonneg_left (cesaroDual_signedCoefficient_abs_le g B hB hG n hnpos)
        (Nat.cast_nonneg _)
    _ = B * positiveWeight n := by
      change (n : ℝ) * (weight n * (B / (n : ℝ))) = B * weight n
      field_simp [hnreal]

/-- Periodic mean-zero witnesses provide the required decay from their
actual, finite cumulative period defect. No uniform bound on this defect
is assumed or concluded. -/
theorem cesaroOperator_firstMoment_of_zeroMean
    (f : ThresholdHilbert) (F : ℕ → ℝ) (hseq : hilbertSequence f = F)
    (Q : ℕ) (hQ : 0 < Q) (hper : ∀ n, F (n+Q) = F n)
    (hm : periodMean F Q = 0) :
    Summable (fun n : ℕ => (n : ℝ) *
      |signedCoefficient (cesaroDual (cesaroOperator f)) n|) := by
  obtain ⟨B, hB, hb⟩ := periodDefect_exists_bound F Q hQ hper
  apply cesaroDual_firstMoment_of_decay (cesaroOperator f) B hB
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [conditionalSequence_cesaroOperator, hseq, cesaro_from_defect F Q (k+1) (by omega),
    hm, zero_add, abs_div,
    abs_of_nonneg (show (0 : ℝ) ≤ ((k+1 : ℕ) : ℝ) from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (hb (k+1)) (Nat.cast_nonneg _)

/-- First-moment control yields absolute summability of the second tail. -/
theorem cesaroDualTail_summable_of_firstMoment
    (g : ThresholdHilbert)
    (hm : Summable (fun n : ℕ => (n : ℝ) * |signedCoefficient (cesaroDual g) n|)) :
    Summable (cesaroDualTail g) := by
  have hs := rawTail_summable_of_firstMoment (signedCoefficient (cesaroDual g))
    (signedCoefficient_summable (cesaroDual_square_summable g)) hm
  apply hs.norm.of_norm_bounded
  intro n
  change ‖if n = 0 then 0 else signedTail (cesaroDual g) n‖ ≤
    ‖∑' j : ℕ, signedCoefficient (cesaroDual g) (j+n)‖
  split_ifs <;> simp [signedTail]

/-- The decay needed by summable-multiples inversion follows from the same
first absolute moment, using the already established tail theorem. -/
theorem cesaroDualTail_weighted_tendsto_of_firstMoment
    (g : ThresholdHilbert)
    (hm : Summable (fun n : ℕ => (n : ℝ) * |signedCoefficient (cesaroDual g) n|)) :
    Tendsto (fun n : ℕ => (n : ℝ) * cesaroDualTail g n) atTop (𝓝 0) := by
  have ht := weighted_rawTail_tendsto_zero_of_firstMoment (signedCoefficient (cesaroDual g))
    (signedCoefficient_summable (cesaroDual_square_summable g)) hm
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [cesaroDualTail, anchoredSignedTail, if_neg (by omega : n ≠ 0), signedTail]

/-- Full analytic regularity needed by the qualitative pulse inversion. -/
theorem cesaroDualTail_regular_of_decay
    (g : ThresholdHilbert) (B : ℝ) (hB : 0 ≤ B)
    (hdecay : ∀ n : ℕ, 0 < n → |conditionalSequence g n| ≤ B / (n : ℝ)) :
    Summable (cesaroDualTail g) ∧
      Tendsto (fun n : ℕ => (n : ℝ) * cesaroDualTail g n) atTop (𝓝 0) := by
  have hm := cesaroDual_firstMoment_of_decay g B hB hdecay
  exact ⟨cesaroDualTail_summable_of_firstMoment g hm,
    cesaroDualTail_weighted_tendsto_of_firstMoment g hm⟩

end RiemannResearch.RH.CRTBlock

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.RH.Pareto

theorem conditionalMeanInner_meanPulse_tendsto_zero (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) :
    Tendsto (fun d => conditionalMeanInner F (meanPulse d)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * conditionalMeanSquare F / ε^2)
  refine ⟨N + 1, ?_⟩
  intro d hd
  have hdpos : 0 < d := by omega
  have hE := conditionalMeanSquare_nonneg F
  have he := conditionalMeanInner_sq_le F (meanPulse d) hF
    (meanPulse_legal d hdpos) (meanPulse_energy_pos d hdpos)
  have hb := meanPulse_energy_le d hdpos
  have hNd : (N : ℝ) < (d : ℝ) + 1 := by exact_mod_cast (show N < d+1 by omega)
  have heps : 0 < ε^2 := sq_pos_of_pos hε
  have hden : 0 < (d : ℝ)+1 := by positivity
  have hlt : 2 * conditionalMeanSquare F / ((d : ℝ)+1) < ε^2 := by
    apply (div_lt_iff₀ hden).2
    have hh := (div_lt_iff₀ heps).1 (hN.trans hNd)
    nlinarith
  have hs : (conditionalMeanInner F (meanPulse d))^2 < ε^2 := by
    calc
      _ ≤ conditionalMeanSquare F * conditionalMeanSquare (meanPulse d) := he
      _ ≤ conditionalMeanSquare F * (2 / ((d : ℝ)+1)) := mul_le_mul_of_nonneg_left hb hE
      _ = 2 * conditionalMeanSquare F / ((d : ℝ)+1) := by ring
      _ < ε^2 := hlt
  rw [Real.dist_eq, sub_zero]
  have habs := sq_abs (conditionalMeanInner F (meanPulse d))
  nlinarith [abs_nonneg (conditionalMeanInner F (meanPulse d))]

end RiemannResearch.RH.CRTBlock
