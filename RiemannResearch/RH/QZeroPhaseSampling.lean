/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import RiemannResearch.Analysis.FiniteWeightedSampling
import Mathlib.Tactic.Positivity
import RiemannResearch.Analysis.FiniteCellSampling

/-!
# Complete Q inner products through periodic physical representatives

Source: user-directed zero-ordinate/CRT discussion, 21 October 2026.
The empirical convergence hypothesis is explicit. This bridge permits a
nonzero physical value at zero. The value at zero is ignored by the Q law,
so constants and periodic approximation errors are covered.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace RiemannResearch.RH.QZeroPhaseSampling

open ZetaTwoHilbert ZetaTwoProbability

theorem qInner_eq_periodic_weights
    (L : ℕ) (hL : 0 < L) (f g : QHilbert)
    (F G : ℕ → ℝ) {C D : ℝ}
    (hF : ∀ k, |F k| ≤ C) (hG : ∀ k, |G k| ≤ D)
    (hpF : ∀ k, F (k + L) = F k)
    (hpG : ∀ k, G (k + L) = G k)
    (hf : ∀ k, qSequence f (k + 1) = F (k + 1))
    (hg : ∀ k, qSequence g (k + 1) = G (k + 1)) :
    inner ℝ f g =
      ∑ a : Fin L, residuePowerWeight 0 L (a.val + 1) *
        (F (a.val + 1) * G (a.val + 1)) := by
  rw [qInner_eq_inversePowerMean]
  have he :
      inversePowerMean 0 (fun k => qSequence f k * qSequence g k) =
        inversePowerMean 0 (fun k => F k * G k) := by
    unfold inversePowerMean
    apply tsum_congr
    intro k
    dsimp only
    rw [hf k, hg k]
  rw [he]
  exact periodic_inversePowerMean_mul 0 L hL F G hF hG hpF hpG


open RiemannResearch.Analysis.FiniteCellSampling

/-- The exact finite-sample discrepancy remains visible. -/
theorem weighted_inner_sample_exact {κ : Type*}
    (L : ℕ) (s : Finset κ) (A : κ → Fin L) (F G : ℕ → ℝ) :
    sampleMean s A (fun a =>
      ((L : ℝ) * residuePowerWeight 0 L (a.val + 1)) *
        (F (a.val + 1) * G (a.val + 1))) =
      ∑ a : Fin L, residuePowerWeight 0 L (a.val + 1) *
        ((L : ℝ) * cellFrequency s A a) *
        (F (a.val + 1) * G (a.val + 1)) := by
  exact weighted_sampleMean_eq s A L
    (fun a => residuePowerWeight 0 L (a.val + 1))
    (fun a => F (a.val + 1) * G (a.val + 1))

/-- Uniform coded-cell frequencies recover the complete Q inner product.
The empirical hypothesis is explicit; it is not proved for zeta zeros here. -/
theorem weighted_inner_sample_tendsto {κ : Type*}
    (L : ℕ) (hL : 0 < L) (s : ℕ → Finset κ) (A : κ → Fin L)
    (f g : QHilbert) (F G : ℕ → ℝ) {C D : ℝ}
    (hF : ∀ k, |F k| ≤ C) (hG : ∀ k, |G k| ≤ D)
    (hpF : ∀ k, F (k + L) = F k)
    (hpG : ∀ k, G (k + L) = G k)
    (hf : ∀ k, qSequence f (k + 1) = F (k + 1))
    (hg : ∀ k, qSequence g (k + 1) = G (k + 1))
    (hfreq : ∀ a, Tendsto (fun n => cellFrequency (s n) A a)
      atTop (𝓝 (1 / (L : ℝ)))) :
    Tendsto (fun n => sampleMean (s n) A (fun a =>
      ((L : ℝ) * residuePowerWeight 0 L (a.val + 1)) *
        (F (a.val + 1) * G (a.val + 1))))
      atTop (𝓝 (inner ℝ f g)) := by
  rw [qInner_eq_periodic_weights L hL f g F G hF hG hpF hpG hf hg]
  exact weighted_sampleMean_tendsto s A L
    (by exact_mod_cast ne_of_gt hL)
    (fun a => residuePowerWeight 0 L (a.val + 1))
    (fun a => F (a.val + 1) * G (a.val + 1)) hfreq

end RiemannResearch.RH.QZeroPhaseSampling



noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QZeroPhaseSampling

open ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis.FiniteCellSampling
open RiemannResearch.Analysis.FiniteWeightedSampling

/-- The complete Q norm is exactly the positive finite residue-weight energy. -/
theorem qNorm_sq_eq_periodic_energy
    (L : ℕ) (hL : 0 < L) (f : QHilbert) (F : ℕ → ℝ) {C : ℝ}
    (hF : ∀ k, |F k| ≤ C) (hpF : ∀ k, F (k + L) = F k)
    (hf : ∀ k, qSequence f (k + 1) = F (k + 1)) :
    ‖f‖ ^ 2 = energy Finset.univ
      (fun a : Fin L => residuePowerWeight 0 L (a.val + 1))
      (fun a => F (a.val + 1)) := by
  simpa only [real_inner_self_eq_norm_sq, energy, pow_two] using
    (qInner_eq_periodic_weights L hL f f F F hF hF hpF hpF hf hf)

/-- The empirical norm is precisely the finite energy with multiplicatively
perturbed weights. Empty samples are permitted by the algebraic identity. -/
theorem weighted_norm_sample_eq_energy {κ : Type*}
    (L : ℕ) (s : Finset κ) (A : κ → Fin L) (F : ℕ → ℝ) :
    sampleMean s A (fun a =>
      ((L : ℝ) * residuePowerWeight 0 L (a.val + 1)) *
        F (a.val + 1) ^ 2) =
      energy Finset.univ
        (fun a : Fin L => residuePowerWeight 0 L (a.val + 1) *
          ((L : ℝ) * cellFrequency s A a))
        (fun a => F (a.val + 1)) := by
  simpa only [energy] using
    (weighted_sampleMean_eq s A (L : ℝ)
      (fun a => residuePowerWeight 0 L (a.val + 1))
      (fun a => F (a.val + 1) ^ 2))

/-- A relative coded-cell discrepancy bounds the sampled Q norm uniformly over
the whole space of L-periodic physical representatives. The same hypothesis
works for every f; it does not depend on its norm or on its coefficients. -/
theorem weighted_norm_sample_comparison {κ : Type*}
    (L : ℕ) (hL : 0 < L) (s : Finset κ) (A : κ → Fin L)
    (f : QHilbert) (F : ℕ → ℝ) {C : ℝ}
    (hF : ∀ k, |F k| ≤ C) (hpF : ∀ k, F (k + L) = F k)
    (hf : ∀ k, qSequence f (k + 1) = F (k + 1))
    (δ : ℝ)
    (hfreq : ∀ a : Fin L, |(L : ℝ) * cellFrequency s A a - 1| ≤ δ) :
    (1 - δ) * ‖f‖ ^ 2 ≤
        sampleMean s A (fun a =>
          ((L : ℝ) * residuePowerWeight 0 L (a.val + 1)) *
            F (a.val + 1) ^ 2) ∧
      sampleMean s A (fun a =>
          ((L : ℝ) * residuePowerWeight 0 L (a.val + 1)) *
            F (a.val + 1) ^ 2) ≤ (1 + δ) * ‖f‖ ^ 2 := by
  rw [qNorm_sq_eq_periodic_energy L hL f F hF hpF hf,
    weighted_norm_sample_eq_energy]
  apply sampled_energy_comparison
  · intro a ha
    exact (residuePowerWeight_pos 0 (by exact_mod_cast hL) (by positivity)).le
  · intro a ha
    exact hfreq a

end RiemannResearch.RH.QZeroPhaseSampling
