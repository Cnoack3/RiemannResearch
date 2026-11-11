/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualPrimeTorusHorizontalEndpoint
import RiemannResearch.Analysis.WeightedFourierStrengthenedClasses
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

/-!
# Finite arithmetic-height sublevels on a fixed finite prime torus

Source: Section 7 of `FRZ_Strengthening_2026-11-10.pdf`. Strictly positive
prime logarithms make arithmetic-height sublevels finite in the integer
character lattice. This discharges the compact-tail premise in the stronger
weighted-ball theorem, including multipliers diverging arbitrarily slowly.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Fourier

theorem finite_weightedIntegerHeight_sublevel {κ : Type*} [Fintype κ]
    (v : κ → ℝ) (hv : ∀ p, 0 < v p) (B : ℝ) :
    Set.Finite {k : κ → ℤ | ∑ p, |(k p : ℝ)| * v p ≤ B} := by
  classical
  let t : κ → Set ℤ := fun p => Set.Icc (-⌈B / v p⌉) ⌈B / v p⌉
  have ht : ∀ p, (t p).Finite := fun p => Set.finite_Icc _ _
  apply (Set.Finite.pi ht).subset
  intro k hk p hp
  have hcoord : |(k p : ℝ)| * v p ≤ B := by
    exact (Finset.single_le_sum (fun q _ => mul_nonneg (abs_nonneg (k q : ℝ)) (hv q).le)
      (Finset.mem_univ p)).trans hk
  have ha : |(k p : ℝ)| ≤ (⌈B / v p⌉ : ℝ) :=
    ((le_div_iff₀ (hv p)).2 hcoord).trans (Int.le_ceil _)
  have hab := abs_le.mp ha
  change -⌈B / v p⌉ ≤ k p ∧ k p ≤ ⌈B / v p⌉
  constructor
  · exact_mod_cast hab.1
  · exact_mod_cast hab.2

end RiemannResearch.Fourier

namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar

/-- The canonical extension of a finite prime character to all natural indices. -/
def extendPrimeMode (P : Finset ℕ) (k : P → ℤ) (p : ℕ) : ℤ :=
  if hp : p ∈ P then k ⟨p, hp⟩ else 0

/-- Intrinsic arithmetic height of a character of the finite prime torus. -/
def finitePrimeModeWeight (P : Finset ℕ) (k : P → ℤ) : ℝ :=
  1 + ∑ p : P, |(k p : ℝ)| * Real.log p

theorem primeModeWeight_extend (P : Finset ℕ) (k : P → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    primeModeWeight P (extendPrimeMode P k) = finitePrimeModeWeight P k := by
  rw [primeModeWeight_eq P _ hP, finitePrimeModeWeight]
  congr 1
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro p hp
  simp [extendPrimeMode, p.property]

theorem one_le_finitePrimeModeWeight (P : Finset ℕ) (k : P → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    1 ≤ finitePrimeModeWeight P k := by
  rw [← primeModeWeight_extend P k hP]
  exact one_le_primeModeWeight P _

theorem finite_finitePrimeModeWeight_sublevel (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (B : ℝ) :
    Set.Finite {k : P → ℤ | finitePrimeModeWeight P k ≤ B} := by
  have hv : ∀ p : P, 0 < Real.log (p : ℕ) := by
    intro p
    apply Real.log_pos
    exact_mod_cast (hP p p.property).one_lt
  apply (Fourier.finite_weightedIntegerHeight_sublevel (fun p : P => Real.log (p : ℕ))
    hv (B - 1)).subset
  intro k hk
  dsimp [finitePrimeModeWeight] at hk ⊢
  linarith

/-- Full fixed finite-prime application of the arbitrarily slow multiplier
class: no finite-sublevel or tight-tail premise remains. -/
theorem eventually_uniform_prime_multiplierBall
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Φ : ℝ → ℝ) (hΦpos : ∀ x, 1 ≤ x → 0 < Φ x)
    (hΦ : Tendsto Φ atTop atTop) (hD : UniformSelbergDensity (1 / 4))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ c : (P → ℤ) → ℂ,
      Summable (fun k => ‖c k‖ *
        (finitePrimeModeWeight P k ^ 2 * Φ (finitePrimeModeWeight P k))) →
      Fourier.weightedFourierMass c
        (fun k => finitePrimeModeWeight P k ^ 2 * Φ (finitePrimeModeWeight P k)) ≤ 1 →
      ‖(Real.log T : ℂ) * ∑' k, c k * correctedRationalRemainder T
        (primeNumerator P (extendPrimeMode P k))
        (primeDenominator P (extendPrimeMode P k))‖ ≤ ε := by
  have hw : ∀ k : P → ℤ, 0 < finitePrimeModeWeight P k ^ 2 := by
    intro k
    have := one_le_finitePrimeModeWeight P k hP
    positivity
  have ht := Fourier.tight_weight_of_diverging_multiplier
    (finitePrimeModeWeight P) (fun k => finitePrimeModeWeight P k ^ 2) Φ
    (fun k => (hw k).le) (finite_finitePrimeModeWeight_sublevel P hP) hΦ
  have htail : ∀ η : ℝ, 0 < η → ∃ F : Finset (P → ℤ), ∀ k ∉ F,
      primeModeWeight P (extendPrimeMode P k) ^ 2 ≤ η *
        (finitePrimeModeWeight P k ^ 2 * Φ (finitePrimeModeWeight P k)) := by
    simpa only [primeModeWeight_extend P _ hP] using ht
  exact eventually_uniform_prime_correctedFourier P (extendPrimeMode P)
    (fun k => finitePrimeModeWeight P k ^ 2 * Φ (finitePrimeModeWeight P k)) hP
    (fun k => mul_pos (hw k) (hΦpos _ (one_le_finitePrimeModeWeight P k hP)))
    htail hD ε hε

end RiemannResearch.Analysis.ActualPrimeTorusFMZ
