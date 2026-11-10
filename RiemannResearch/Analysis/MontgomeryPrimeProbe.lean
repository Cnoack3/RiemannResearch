/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryFormFactor


/-! # Finite shifted probes of the raw pair sum

Source: Section 5 of the user-provided Montgomery handoff. The identity is
proved for arbitrary finite real frequencies and real weights; logarithms
of primes and log(p)/p are specializations. This is exact finite algebra,
not an identification of the zeros with a determinantal process and not
an estimate of the form factor above Fourier support one.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.MontgomeryFormFactor
open MontgomeryPoisson ZeroOrdinate
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def probeKernel (q b : κ → ℝ) (d : ℝ) : ℂ :=
  ∑ p, (b p : ℂ) * phase (q p) d

theorem phase_mul_conj_frequency (u v d : ℝ) :
    phase u d * conj (phase v d) = phase (u-v) d := by
  simp only [phase, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp
  <;> ring

theorem probe_energy_expansion (q b : κ → ℝ) (d : ℝ) :
    ((‖probeKernel q b d‖^2 : ℝ) : ℂ) =
      ∑ p, ∑ r, ((b p*b r : ℝ) : ℂ) * phase (q p-q r) d := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [probeKernel, map_sum, map_mul, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro r hr
  rw [← phase_mul_conj_frequency, Complex.ofReal_mul]
  ring

/-- Exact finite probe identity before any normalization or asymptotic limit. -/
theorem shifted_probe (t : ι → ℝ) (q b : κ → ℝ) (u : ℝ) :
    (∑ i, ∑ j, (cauchyWeight (t i-t j) : ℂ) * phase u (t i-t j) *
      ((‖probeKernel q b (t i-t j)‖^2 : ℝ) : ℂ)) =
    ∑ p, ∑ r, ((b p*b r : ℝ) : ℂ) * pairSum t (u+q p-q r) := by
  simp_rw [probe_energy_expansion, Finset.mul_sum]
  let f := fun (i j : ι) (p r : κ) =>
    (cauchyWeight (t i-t j) : ℂ) * phase u (t i-t j) *
      (((b p*b r : ℝ) : ℂ) * phase (q p-q r) (t i-t j))
  change (∑ i, ∑ j, ∑ p, ∑ r, f i j p r) = _
  have hs : (∑ i, ∑ j, ∑ p, ∑ r, f i j p r) =
      ∑ p, ∑ r, ∑ i, ∑ j, f i j p r := by
    calc
      _ = ∑ i, ∑ p, ∑ r, ∑ j, f i j p r := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.sum_comm]
  rw [hs]
  unfold pairSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show u+q p-q r = u+(q p-q r) by ring, phase_add]
  dsimp [f]
  ring

end RiemannResearch.Analysis.MontgomeryFormFactor
