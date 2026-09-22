/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusPNT
import RiemannResearch.RH.ParetoFiniteHeadDilation

/-!
# Heavy tails of arithmetic annihilators with nonzero constant pairing

Source: the user-provided Pareto direct approximation handoff, Sections 3--4
and 14, for the sublinear exact-head argument and infinite normal problem.
This extends the residual-tail obstruction to every actual annihilator whose
pairing with the constant sequence is nonzero. It keeps the complete infinite
tail and uses the established unconditional canonical sublinear-energy theorem.
Integer dilations remove the nonzero-mean restriction in the final theorem.
No nonzero annihilator, tail upper bound, or proof of RH is asserted.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The complete tail of any annihilator controls its constant pairing. -/
theorem annihilator_tail_product_lower (z : ThresholdHilbert)
    (hz : z ∈ closedSpaceᗮ) (N : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ closedSpace)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    (inner ℝ z hilbertOne)^2 ≤
      ‖hilbertTailShift z N‖^2 * ‖hilbertOne - f‖^2 := by
  have ho : inner ℝ z f = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp hz _ hf
  have he : ∀ n < N, (hilbertOne - f) n = 0 := by
    intro n hn
    have hs := hhead (n + 1) (by omega) (by omega)
    have hone : hilbertSequence hilbertOne (n + 1) = 1 := by
      rw [hilbertOne_sequence]
      simp [zeroAnchor]
    have hsame : hilbertSequence hilbertOne (n + 1) =
        hilbertSequence f (n + 1) := hone.trans hs.symm
    have hw : Real.sqrt (paretoWeight n) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (paretoWeight_pos n))
    have hc : hilbertOne n = f n := (div_left_inj' hw).mp hsame
    change hilbertOne n - f n = 0
    exact sub_eq_zero.mpr hc
  simpa only [inner_sub_right, ho, sub_zero] using
    hilbertTailShift_inner_sq_le z (hilbertOne - f) N he

/-- Any arithmetic annihilator with nonzero constant pairing must have
normalized complete tail energy tending to infinity. -/
theorem annihilator_normalized_tail_tendsto_atTop (z : ThresholdHilbert)
    (hz : z ∈ closedSpaceᗮ) (hmean : inner ℝ z hilbertOne ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℝ) * ‖hilbertTailShift z N‖^2)
      atTop atTop := by
  have hsub := error_energy_div_tendsto_zero_of_energy
    canonicalMobiusHilbert canonicalMobiusHilbert_sublinear
  refine RiemannResearch.Analysis.tendsto_atTop_of_pos_le_mul_tendsto_zero
    (sq_pos_of_ne_zero hmean) ?_ hsub ?_
  · exact Eventually.of_forall
      (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hne : (N : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : N ≠ 0)
    have heq : ((N : ℝ) * ‖hilbertTailShift z N‖^2) *
        (‖hilbertOne - canonicalMobiusHilbert N‖^2 / (N : ℝ)) =
        ‖hilbertTailShift z N‖^2 *
          ‖hilbertOne - canonicalMobiusHilbert N‖^2 := by
      field_simp [hne]
    rw [heq]
    exact annihilator_tail_product_lower z hz N
      (canonicalMobiusHilbert_mem_closedSpace N)
      (canonicalMobiusHilbert_exact N)

/-- A bounded cofinal normalized tail forces zero constant pairing; it
need not force an arbitrary annihilator itself to be zero. -/
theorem annihilator_inner_one_eq_zero_of_frequently_bounded_tail
    (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ) (C : ℝ)
    (hbounded : ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * ‖hilbertTailShift z N‖^2 ≤ C) :
    inner ℝ z hilbertOne = 0 := by
  by_contra hn
  have ht := annihilator_normalized_tail_tendsto_atTop z hz hn
  obtain ⟨N, hN, hN'⟩ :=
    (hbounded.and_eventually (ht.eventually_gt_atTop C)).exists
  linarith

/-- The Hilbert tail norm is precisely the complete physical Pareto tail. -/
theorem hilbertTailShift_energy_eq_weighted (z : ThresholdHilbert) (N : ℕ) :
    ‖hilbertTailShift z N‖^2 = ∑' n : ℕ,
      positiveWeight (n + N + 1) * hilbertSequence z (n + N + 1)^2 := by
  rw [hilbert_norm_sq]
  change (∑' n : ℕ, (z (n + N))^2) = _
  apply tsum_congr
  intro n
  exact (hilbertSequence_weighted_square z (n + N)).symm

/-- The all-integer threshold family separates every actual Hilbert vector. -/
theorem eq_zero_of_inner_dilation_one_eq_zero (z : ThresholdHilbert)
    (hz : ∀ B : ℕ, ∀ hB : 0 < B,
      inner ℝ z (hilbertDilation B hB hilbertOne) = 0) : z = 0 := by
  have hmean : inner ℝ z hilbertOne = 0 := by
    simpa only [hilbertDilation_one] using hz 1 Nat.zero_lt_one
  have hhead (N : ℕ) : inner ℝ z (finiteHeadIndicator N) = 0 := by
    rw [finiteHeadIndicator_eq_dilation_difference,
      inner_sub_right, inner_smul_right, hmean, hz (N + 1) (by omega)]
    ring
  have hpoint (n : ℕ) : inner ℝ z (paretoPointHilbert n) = 0 := by
    have hs : finiteHeadIndicator (n + 1) =
        finiteHeadIndicator n + paretoPointHilbert n := by
      simp only [finiteHeadIndicator, Finset.sum_range_succ]
    have hh := hhead (n + 1)
    rwa [hs, inner_add_right, hhead n, zero_add] at hh
  apply hilbertSequence_injective
  funext k
  cases k with
  | zero => simp only [hilbertSequence_zero]
  | succ n =>
    have hp := hpoint n
    rw [inner_paretoPoint, hilbertGibbsPhysical_eq] at hp
    have hh : hilbertSequence z (n + 1) = 0 :=
      (mul_eq_zero.mp hp).resolve_left (ne_of_gt (paretoWeight_pos n))
    change hilbertSequence z (n + 1) = (0 : ℝ) / Real.sqrt (paretoWeight n)
    rw [hh, zero_div]

/-- Any one nonzero threshold pairing forces divergent normalized tails. -/
theorem annihilator_normalized_tail_tendsto_atTop_of_dilation_pairing
    (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ)
    (B : ℕ) (hB : 0 < B)
    (hpair : inner ℝ z (hilbertDilation B hB hilbertOne) ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℝ) * ‖hilbertTailShift z N‖^2)
      atTop atTop := by
  let E : ℕ → ThresholdHilbert := fun N =>
    hilbertDilation B hB (hilbertOne - canonicalMobiusHilbert N)
  have hzero (N : ℕ) : ∀ n < N, E N n = 0 := by
    intro n hn
    have hphysical : hilbertSequence (E N) (n + 1) = 0 := by
      change hilbertSequence (hilbertDilation B hB
        (hilbertOne - canonicalMobiusHilbert N)) (n + 1) = 0
      rw [hilbertDilation_sequence]
      change (B : ℝ) *
        hilbertSequence (hilbertOne - canonicalMobiusHilbert N) ((n + 1) / B) = 0
      by_cases hq : (n + 1) / B = 0
      · rw [hq, hilbertSequence_zero, mul_zero]
      · have hqpos : 0 < (n + 1) / B := Nat.pos_of_ne_zero hq
        have hqN : (n + 1) / B ≤ N := (Nat.div_le_self _ _).trans (by omega)
        have hu := canonicalMobiusHilbert_exact N ((n + 1) / B) hqpos hqN
        have hone : hilbertSequence hilbertOne ((n + 1) / B) = 1 := by
          rw [hilbertOne_sequence]
          simp only [zeroAnchor, hq, ↓reduceIte]
        change (B : ℝ) *
          hilbertSequenceLinear (hilbertOne - canonicalMobiusHilbert N)
            ((n + 1) / B) = 0
        rw [map_sub]
        change (B : ℝ) * (hilbertSequence hilbertOne ((n + 1) / B) -
          hilbertSequence (canonicalMobiusHilbert N) ((n + 1) / B)) = 0
        rw [hone, hu, sub_self, mul_zero]
    change E N n / Real.sqrt (paretoWeight n) = 0 at hphysical
    exact (div_eq_zero_iff.mp hphysical).resolve_right
      (ne_of_gt (Real.sqrt_pos.mpr (paretoWeight_pos n)))
  have hinner (N : ℕ) : inner ℝ z (E N) =
      inner ℝ z (hilbertDilation B hB hilbertOne) := by
    have ho : inner ℝ z
        (hilbertDilation B hB (canonicalMobiusHilbert N)) = 0 := by
      rw [real_inner_comm]
      exact (closedSpace.mem_orthogonal _).mp hz _
        (closedSpace_dilation (canonicalMobiusHilbert_mem_closedSpace N) B hB)
    change inner ℝ z ((hilbertDilationContinuous B hB)
      (hilbertOne - canonicalMobiusHilbert N)) = _
    rw [map_sub, inner_sub_right]
    change inner ℝ z (hilbertDilation B hB hilbertOne) -
      inner ℝ z (hilbertDilation B hB (canonicalMobiusHilbert N)) = _
    rw [ho, sub_zero]
  have hsub : Tendsto (fun N : ℕ => ‖E N‖^2 / (N : ℝ)) atTop (𝓝 0) := by
    have hu := (error_energy_div_tendsto_zero_of_energy
      canonicalMobiusHilbert canonicalMobiusHilbert_sublinear).const_mul (B : ℝ)
    convert hu using 1
    · funext N
      dsimp [E]
      rw [hilbertDilation_norm_sq]
      ring
    · simp only [mul_zero]
  refine RiemannResearch.Analysis.tendsto_atTop_of_pos_le_mul_tendsto_zero
    (sq_pos_of_ne_zero hpair) ?_ hsub ?_
  · exact Eventually.of_forall
      (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have heq : ((N : ℝ) * ‖hilbertTailShift z N‖^2) *
        (‖E N‖^2 / (N : ℝ)) = ‖hilbertTailShift z N‖^2 * ‖E N‖^2 := by
      field_simp [hne]
    rw [heq]
    simpa only [hinner N] using hilbertTailShift_inner_sq_le z (E N) N (hzero N)

/-- Every nonzero arithmetic annihilator has heavy tails, including those
whose constant pairing happens to vanish. -/
theorem every_nonzero_annihilator_normalized_tail_tendsto_atTop
    (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ) (hne : z ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℝ) * ‖hilbertTailShift z N‖^2)
      atTop atTop := by
  have hex : ∃ B : ℕ, ∃ hB : 0 < B,
      inner ℝ z (hilbertDilation B hB hilbertOne) ≠ 0 := by
    by_contra hnot
    apply hne
    apply eq_zero_of_inner_dilation_one_eq_zero z
    intro B hB
    by_contra hp
    exact hnot ⟨B, hB, hp⟩
  obtain ⟨B, hB, hp⟩ := hex
  exact annihilator_normalized_tail_tendsto_atTop_of_dilation_pairing z hz B hB hp

/-- In the actual arithmetic annihilator, a bounded cofinal normalized
tail already forces the vector to vanish. -/
theorem annihilator_eq_zero_of_frequently_bounded_normalized_tail
    (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ) (C : ℝ)
    (hbounded : ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * ‖hilbertTailShift z N‖^2 ≤ C) : z = 0 := by
  by_contra hn
  have ht := every_nonzero_annihilator_normalized_tail_tendsto_atTop z hz hn
  obtain ⟨N, hN, hN'⟩ :=
    (hbounded.and_eventually (ht.eventually_gt_atTop C)).exists
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization
