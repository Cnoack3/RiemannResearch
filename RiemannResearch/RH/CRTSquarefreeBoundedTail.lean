/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTReciprocalExactHeadRH
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The literal squarefree divisor-span bounded-tail RH criterion

Source: user-provided sufficient goal, 13 October 2026.
Span membership is algebraic and finite; boundedness and periodicity are
proved from it. The displayed finite Icc tail need only be uniformly bounded.
The conclusion is Mathlib's actual RiemannHypothesis proposition, via the
proved Mellin obstruction. Constructing a family with the assumed bound
remains the substantive Open arithmetic provider.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative ParetoBeurlingMellinObstruction

def divisorResidueSpan (L : ℕ) : Submodule ℝ (ℕ → ℝ) :=
  Submodule.span ℝ {F | ∃ d : ℕ, 2 ≤ d ∧ d ∣ L ∧ F = residueFraction d}

theorem divisorResidueSpan_lift {L : ℕ} {F : ℕ → ℝ}
    (hF : F ∈ divisorResidueSpan L) :
    ∃ f : ThresholdHilbert, f ∈ normalizedResidueSpan ∧
      hilbertSequence f = F ∧ (∃ C : ℝ, ∀ n, |F n| ≤ C) ∧
      (∀ n, F (n + L) = F n) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨d, hd, hdiv, rfl⟩ := hF
    refine ⟨normalizedResidueHilbert d (by omega),
      Submodule.subset_span ⟨⟨d, hd⟩, rfl⟩,
      normalizedResidueHilbert_sequence _ _, ⟨1, ?_⟩, ?_⟩
    · intro n
      have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have hm : ((n % d : ℕ) : ℝ) ≤ d := by
        exact_mod_cast (Nat.mod_lt n (by omega)).le
      unfold residueFraction
      rw [abs_of_nonneg (by positivity)]
      exact (div_le_iff₀ hdR).mpr (by simpa using hm)
    · intro n
      simp [residueFraction, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv]
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_, ⟨0, by simp⟩, by simp⟩
    exact hilbertSequenceLinear.map_zero
  | add F G hF hG ihF ihG =>
    obtain ⟨f, hf, hsf, ⟨C, hC⟩, hpF⟩ := ihF
    obtain ⟨g, hg, hsg, ⟨D, hD⟩, hpG⟩ := ihG
    refine ⟨f + g, Submodule.add_mem _ hf hg, ?_, ⟨C + D, ?_⟩, ?_⟩
    · change hilbertSequenceLinear (f + g) = _
      rw [map_add]
      exact congrArg₂ (· + ·) hsf hsg
    · intro n
      exact (abs_add_le (F n) (G n)).trans (add_le_add (hC n) (hD n))
    · intro n
      simp only [Pi.add_apply, hpF, hpG]
  | smul c F hF ih =>
    obtain ⟨f, hf, hsf, ⟨C, hC⟩, hp⟩ := ih
    refine ⟨c • f, Submodule.smul_mem _ c hf, ?_, ⟨|c| * C, ?_⟩, ?_⟩
    · change hilbertSequenceLinear (c • f) = _
      rw [map_smul]
      exact congrArg (c • ·) hsf
    · intro n
      simpa only [Pi.smul_apply, smul_eq_mul, abs_mul] using
        mul_le_mul_of_nonneg_left (hC n) (abs_nonneg c)
    · intro n
      simp only [Pi.smul_apply, smul_eq_mul, hp]

theorem crtReciprocalEnergy_eq_Icc (L : ℕ) (R : ℕ → ℝ) :
    crtReciprocalEnergy L R = ∑ a ∈ Finset.Icc 1 L, R a ^ 2 / (a : ℝ) ^ 2 := by
  classical
  unfold crtReciprocalEnergy
  apply Finset.sum_bij (fun a _ => a.val + 1)
  · intro a _
    exact Finset.mem_Icc.mpr ⟨by omega, a.isLt⟩
  · intro a _ b _ hab
    apply Fin.ext
    omega
  · intro b hb
    have hb' := Finset.mem_Icc.mp hb
    refine ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  · intro a _
    rfl

theorem crtReciprocalEnergy_eq_Icc_tail (M L : ℕ) (R : ℕ → ℝ)
    (hhead : ∀ n, 0 < n → n ≤ M → R n = 0) :
    crtReciprocalEnergy L R =
      ∑ a ∈ Finset.Icc (M + 1) L, |R a| ^ 2 / (a : ℝ) ^ 2 := by
  classical
  rw [crtReciprocalEnergy_eq_Icc]
  simp only [sq_abs]
  symm
  apply Finset.sum_subset
  · intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩
  · intro n hn hnot
    have hn' := Finset.mem_Icc.mp hn
    have hnM : n ≤ M := by
      by_contra hh
      exact hnot (Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩)
    rw [hhead n (by omega) hnM]
    simp

/-- The literal finite tail condition implies actual RH. No decay is assumed. -/
theorem riemannHypothesis_of_squarefree_span_bounded_tail
    (M L : ℕ → ℕ) (F : ℕ → ℕ → ℝ)
    (hM : Tendsto M atTop atTop)
    (hL : ∀ j, Squarefree (L j))
    (hF : ∀ j, F j ∈ divisorResidueSpan (L j))
    (hhead : ∀ j n, 0 < n → n ≤ M j → F j n = 1)
    (htail : BddAbove (Set.range (fun j =>
      ∑ a ∈ Finset.Icc (M j + 1) (L j), |1 - F j a| ^ 2 / (a : ℝ) ^ 2))) :
    RiemannHypothesis := by
  choose f hf hseq hbound hp using fun j => divisorResidueSpan_lift (hF j)
  obtain ⟨C, hC⟩ := htail
  apply riemannHypothesis_of_cofinal_reciprocal_bound f M L hM hf
    (fun j => Nat.pos_of_ne_zero (hL j).ne_zero)
  · intro j
    simpa only [hseq j] using hbound j
  · intro j n
    simpa only [hseq j] using hp j n
  · intro j n hn hnM
    simpa only [hseq j] using hhead j n hn hnM
  · intro j
    rw [hseq j, crtReciprocalEnergy_eq_Icc_tail (M j) (L j) _
      (by intro n hn hnM; rw [hhead j n hn hnM]; ring)]
    exact hC ⟨j, rfl⟩

end RiemannResearch.RH.Pareto
