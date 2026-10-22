/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoCRTReciprocalEnergy
import RiemannResearch.RH.ParetoExactHeadClosure
import RiemannResearch.RH.ParetoBeurlingMellinObstruction
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import RiemannResearch.RH.ParetoLegalApproximationClosure
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Cofinal exact heads with bounded finite CRT energy imply RH

Source: user-provided formulation and proof, 13 October 2026.
The Nyman--Beurling terminology and discrete residue criterion are discussed in
B. Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
of the Riemann hypothesis", https://arxiv.org/abs/math/0607733, Theorem 1 and
Remark 8. The source supports the interpretation; the actual forward Mellin
obstruction is an already proved repository dependency.

These are conditional research reductions. The existence of a cofinal family
with the displayed uniform finite energy bound remains Open. The final result
concludes Mathlib's actual RiemannHypothesis proposition, without assuming
a closure-to-RH bridge. All finite divisor sets are permitted; squarefree
periods and their divisors are an immediate special case.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

open Filter
open scoped Topology
open RiemannResearch.RH.ParetoBeurlingMellinObstruction

theorem hilbertOne_mem_normalizedClosure_of_cofinal_reciprocal_bound
    (f : ℕ → ThresholdHilbert) (M L : ℕ → ℕ)
    (hM : Tendsto M atTop atTop)
    (hf : ∀ j, f j ∈ normalizedResidueSpan)
    (hL : ∀ j, 0 < L j)
    (hbounded : ∀ j, ∃ C : ℝ, ∀ n, |hilbertSequence (f j) n| ≤ C)
    (hp : ∀ j n, hilbertSequence (f j) (n + L j) = hilbertSequence (f j) n)
    (hhead : ∀ j n, 0 < n → n ≤ M j → hilbertSequence (f j) n = 1)
    {C : ℝ}
    (henergy : ∀ j,
      crtReciprocalEnergy (L j) (fun n => 1 - hilbertSequence (f j) n) ≤ C) :
    hilbertOne ∈ normalizedResidueClosure := by
  have hC : 0 ≤ C := (crtReciprocalEnergy_nonneg _ _).trans (henergy 0)
  have hn (j : ℕ) : ‖hilbertOne - f j‖ ^ 2 ≤ 2 * C := by
    obtain ⟨D, hD⟩ := hbounded j
    rw [hilbertOne_sub_norm_sq_eq_paretoError]
    exact (periodic_paretoError_le_crtReciprocalEnergy
      (L j) (hL j) _ hD (hp j)).trans
      (mul_le_mul_of_nonneg_left (henergy j) (by norm_num))
  have hnorm (j : ℕ) : ‖f j‖ ≤ 2 * C + 2 := by
    have ht := norm_sub_le hilbertOne (hilbertOne - f j)
    have he : hilbertOne - (hilbertOne - f j) = f j := by abel
    rw [he] at ht
    have ho := hilbertOne_norm_sq
    have hone : ‖hilbertOne‖ ≤ 1 := by nlinarith [norm_nonneg hilbertOne]
    have herr : ‖hilbertOne - f j‖ ≤ 2 * C + 1 := by
      nlinarith [hn j, sq_nonneg (‖hilbertOne - f j‖ - 1)]
    linarith
  have hex : ∀ N : ℕ, ∃ j : ℕ, N ≤ M j := by
    intro N
    exact (Filter.tendsto_atTop.mp hM N).exists
  choose j hj using hex
  exact hilbertOne_mem_closure_of_bounded_exact_heads normalizedResidueSpan
    (fun N => f (j N)) (fun N => hf (j N))
    (fun N n hn hnN => hhead (j N) n hn (hnN.trans (hj N)))
    (fun N => hnorm (j N))

theorem riemannHypothesis_of_cofinal_reciprocal_bound
    (f : ℕ → ThresholdHilbert) (M L : ℕ → ℕ)
    (hM : Tendsto M atTop atTop)
    (hf : ∀ j, f j ∈ normalizedResidueSpan)
    (hL : ∀ j, 0 < L j)
    (hbounded : ∀ j, ∃ C : ℝ, ∀ n, |hilbertSequence (f j) n| ≤ C)
    (hp : ∀ j n, hilbertSequence (f j) (n + L j) = hilbertSequence (f j) n)
    (hhead : ∀ j n, 0 < n → n ≤ M j → hilbertSequence (f j) n = 1)
    {C : ℝ}
    (henergy : ∀ j,
      crtReciprocalEnergy (L j) (fun n => 1 - hilbertSequence (f j) n) ≤ C) :
    RiemannHypothesis := by
  have hmem := hilbertOne_mem_normalizedClosure_of_cofinal_reciprocal_bound
    f M L hM hf hL hbounded hp hhead henergy
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt
  exact zeta_ne_zero_of_hilbertOne_mem_normalizedResidueClosure hmem s hs
    (by intro he; norm_num [he] at hslt)


open ArithmeticCumulative

def crtResidueCombination (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) : ThresholdHilbert :=
  ∑ d : s, c d • normalizedResidueHilbert d (by have := hs d d.property; omega)

theorem crtResidueCombination_sequence (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) (n : ℕ) :
    hilbertSequence (crtResidueCombination s c hs) n =
      ∑ d : s, c d * residueFraction d n := by
  change hilbertSequenceLinear (∑ d : s,
    c d • normalizedResidueHilbert d (by have := hs d d.property; omega)) n = _
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [show hilbertSequenceLinear
    (normalizedResidueHilbert d (by have := hs d d.property; omega)) =
      residueFraction d from normalizedResidueHilbert_sequence _ _]

theorem crtResidueCombination_mem (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) :
    crtResidueCombination s c hs ∈ normalizedResidueSpan := by
  apply Submodule.sum_mem
  intro d _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨d, hs d d.property⟩, rfl⟩

theorem crtResidueCombination_bounded (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) (n : ℕ) :
    |hilbertSequence (crtResidueCombination s c hs) n| ≤ ∑ d : s, |c d| := by
  rw [crtResidueCombination_sequence]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d _
  have hd : 0 < (d.val : ℝ) := by exact_mod_cast (show 0 < d.val by have := hs d d.property; omega)
  have hm : ((n % d.val : ℕ) : ℝ) ≤ d.val := by
    exact_mod_cast (Nat.mod_lt n (by have := hs d d.property; omega)).le
  have hr : |residueFraction d n| ≤ 1 := by
    unfold residueFraction
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ hd).mpr
    simpa using hm
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left hr (abs_nonneg _)).trans_eq (mul_one _)

theorem crtResidueCombination_period (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) (L : ℕ) (hdiv : ∀ d ∈ s, d ∣ L) (n : ℕ) :
    hilbertSequence (crtResidueCombination s c hs) (n + L) =
      hilbertSequence (crtResidueCombination s c hs) n := by
  rw [crtResidueCombination_sequence, crtResidueCombination_sequence]
  apply Finset.sum_congr rfl
  intro d _
  simp [residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd (hdiv d d.property)]

/-- Conditional research reduction for literal finite divisor-supported residue sums.
Squarefree periods are allowed but not required for this sufficient implication. -/
theorem riemannHypothesis_of_cofinal_divisor_reciprocal_bound
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (M L : ℕ → ℕ)
    (hs : ∀ j d, d ∈ s j → 2 ≤ d)
    (hdiv : ∀ j d, d ∈ s j → d ∣ L j)
    (hM : Tendsto M atTop atTop) (hL : ∀ j, 0 < L j)
    (hhead : ∀ j n, 0 < n → n ≤ M j →
      (∑ d : s j, c j d * residueFraction d n) = 1)
    {C : ℝ}
    (henergy : ∀ j, crtReciprocalEnergy (L j)
      (fun n => 1 - ∑ d : s j, c j d * residueFraction d n) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_reciprocal_bound
    (fun j => crtResidueCombination (s j) (c j) (hs j)) M L hM
    (fun j => crtResidueCombination_mem (s j) (c j) (hs j)) hL
    (fun j => ⟨_, crtResidueCombination_bounded (s j) (c j) (hs j)⟩)
    (fun j => crtResidueCombination_period (s j) (c j) (hs j) (L j) (hdiv j))
  · intro j n hn hnM
    rw [crtResidueCombination_sequence]
    exact hhead j n hn hnM
  · simpa only [crtResidueCombination_sequence] using henergy

end
end RiemannResearch.RH.Pareto
