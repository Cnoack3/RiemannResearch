/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryComplexGram
import RiemannResearch.Analysis.WeightedSqrtTransfer
import RiemannResearch.Analysis.MontgomeryLocalMass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-! # Signed perturbation identities for the finite Cauchy Gram form

The exact mixed term is retained before the reverse-triangle estimate is taken.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.CauchyWeightPerturbation
open MontgomeryPoisson MontgomeryComplexGram
variable {ι : Type*} [Fintype ι]

def crossKernel (t : ι → ℝ) (a b : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, a i * conj (b j) * (cauchyWeight (t i - t j) : ℂ)

theorem crossKernel_conj (t : ι → ℝ) (a b : ι → ℂ) :
    conj (crossKernel t a b) = crossKernel t b a := by
  unfold crossKernel
  simp only [map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hk : cauchyWeight (t j - t i) = cauchyWeight (t i - t j) := by
    unfold cauchyWeight
    congr 2
    ring
  rw [hk]
  ring

theorem kernel_add_exact (t : ι → ℝ) (a b : ι → ℂ) :
    kernelQuadratic t (a+b) =
      kernelQuadratic t a + crossKernel t a b +
        crossKernel t b a + kernelQuadratic t b := by
  simp only [kernelQuadratic, crossKernel, Pi.add_apply, map_add,
    add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem kernel_sub_exact (t : ι → ℝ) (a b : ι → ℂ) :
    (kernelQuadratic t a).re - (kernelQuadratic t b).re =
      2*(crossKernel t b (a-b)).re + (kernelQuadratic t (a-b)).re := by
  have he : a = b+(a-b) := by ext i; simp
  have h := kernel_add_exact t b (a-b)
  rw [← he, ← crossKernel_conj t b (a-b)] at h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.conj_re] at hr
  linarith

theorem complexSignal_imaginary (t : ι → ℝ) (c : ι → ℂ) (s : ℝ) :
    complexSignal (fun i => (t i : ℂ)*Complex.I) c s = signal t c s := by
  unfold complexSignal signal ZeroOrdinate.phase
  simp only [Complex.ofReal_mul, mul_assoc]

theorem sqrt_kernel_difference (t : ι → ℝ) (a b : ι → ℂ) :
    |Real.sqrt (kernelQuadratic t a).re - Real.sqrt (kernelQuadratic t b).re| ≤
      Real.sqrt (kernelQuadratic t (a-b)).re := by
  let z : ι → ℂ := fun i => (t i : ℂ)*Complex.I
  have hz : ∀ i, |(z i).re| < 1 := by intro i; simp [z]
  have h := sqrt_energy_reverse_triangle (weightedSignal_memLp z a hz)
    (weightedSignal_memLp z b hz)
  have he (s : ℝ) : weightedSignal z a s - weightedSignal z b s =
      weightedSignal z (a-b) s := by
    simp only [weightedSignal, complexSignal, Pi.sub_apply, sub_mul,
      Finset.sum_sub_distrib, mul_sub]
  simp only [he, weightedSignal_sq] at h
  simp only [z, complexSignal_imaginary, finite_gram] at h
  exact h

end RiemannResearch.Analysis.CauchyWeightPerturbation
