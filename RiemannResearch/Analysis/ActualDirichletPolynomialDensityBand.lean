/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualDirichletPolynomialGram
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import Mathlib.Tactic.Ring

/-!
# Actual quadratic density-band comparison

The scalar density-band theorem is assembled into the actual sampled
Dirichlet-polynomial quadratic form. The normalizer is T, every analytic
multiplicity is retained, and the bound has only the coefficient-weighted
frequency spread: there is no constant entrywise remainder.

Source for the analytic input: Ford--Zaharescu, "On the distribution of
imaginary parts of zeros of the Riemann zeta function", Lemma 2,
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .
The finite assembly below is a deduction from the imported scalar theorem.

`SelbergDensityBound` is a visible hypothesis, not a proved provider.
This module does not formalize Selberg's density estimate for zeta.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.Analysis.ActualDirichletPolynomialGram
open ActualZeroOrdinate RiemannResearch.Fourier

/-- Actual phase-versus-Landau comparison in every fractional Selberg band.
The complete quadratic form, not its finite head, is the object on the left. -/
theorem sampledSquare_landau_error_of_selbergDensity_band
    (T C δ θ : ℝ) (s : Finset ℕ) (a : ℕ → ℂ)
    (hT : 1 < T) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hband : ∀ n ∈ s, ∀ m ∈ s,
      |Real.log m - Real.log n| ≤ θ * (δ * Real.log T))
    (hD : SelbergDensityBound T C δ) :
    ‖(sampledSquare T s a -
      finiteGramErrorPairing s a (fun n m =>
        landauSum T (Real.log m - Real.log n))) / (T : ℂ)‖ ≤
      (2 * C / (δ ^ 2 * (1 - θ ^ 2))) *
        (weightedFrequencySpread s (fun n => ‖a n‖)
          (fun n => Real.log n) / Real.log T) := by
  have he : (sampledSquare T s a -
      finiteGramErrorPairing s a (fun n m =>
        landauSum T (Real.log m - Real.log n))) / (T : ℂ) =
      finiteGramErrorPairing s a (fun n m =>
        (gramEntry T n m - landauSum T (Real.log m - Real.log n)) / (T : ℂ)) := by
    rw [sampledSquare_eq_gram]
    simp only [finiteGramErrorPairing, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [he]
  let κ : ℝ := (2 * C / (δ ^ 2 * (1 - θ ^ 2))) / Real.log T
  have hb := finiteGramErrorPairing_norm_le_frequencySpread s a
    (fun n m => (gramEntry T n m -
      landauSum T (Real.log m - Real.log n)) / (T : ℂ))
    (fun n => Real.log n) 0 κ
  have hentry : ∀ n ∈ s, ∀ m ∈ s,
      ‖(gramEntry T n m - landauSum T (Real.log m - Real.log n)) / (T : ℂ)‖ ≤
        0 + κ * (Real.log n - Real.log m) ^ 2 := by
    intro n hn m hm
    calc
      _ ≤ (2 * C / (δ ^ 2 * (1 - θ ^ 2))) *
          (Real.log m - Real.log n) ^ 2 / Real.log T :=
        normalized_ordinate_landau_error_of_selbergDensity_band
          T (Real.log m - Real.log n) C δ θ hT hC hδ hθ₀ hθ₁
          (hband n hn m hm) hD
      _ = _ := by dsimp [κ]; ring
  have h := hb hentry
  simp only [zero_mul, zero_add] at h
  calc
    _ ≤ κ * weightedFrequencySpread s (fun n => ‖a n‖)
        (fun n => Real.log n) := h
    _ = _ := by dsimp [κ]; ring

/-- Concrete one-eighth-log frequency band from the classical one-quarter
Selberg exponent; still explicitly conditional on its density provider. -/
theorem sampledSquare_landau_error_of_classical_selberg
    (T C : ℝ) (s : Finset ℕ) (a : ℕ → ℂ)
    (hT : 1 < T) (hC : 0 ≤ C)
    (hband : ∀ n ∈ s, ∀ m ∈ s,
      |Real.log m - Real.log n| ≤ Real.log T / 8)
    (hD : SelbergDensityBound T C (1 / 4)) :
    ‖(sampledSquare T s a -
      finiteGramErrorPairing s a (fun n m =>
        landauSum T (Real.log m - Real.log n))) / (T : ℂ)‖ ≤
      (128 * C / 3) *
        (weightedFrequencySpread s (fun n => ‖a n‖)
          (fun n => Real.log n) / Real.log T) := by
  have hb : ∀ n ∈ s, ∀ m ∈ s,
      |Real.log m - Real.log n| ≤ (1 / 2 : ℝ) * ((1 / 4 : ℝ) * Real.log T) := by
    intro n hn m hm
    calc
      _ ≤ Real.log T / 8 := hband n hn m hm
      _ = _ := by ring
  have h := sampledSquare_landau_error_of_selbergDensity_band
    T C (1 / 4) (1 / 2) s a hT hC (by norm_num) (by norm_num)
    (by norm_num) hb hD
  convert h using 1 <;> ring

/-- Moving supports and coefficients are permitted when their actual spread
budget vanishes and every stage satisfies the stated density and band inputs. -/
theorem sampledSquare_landau_error_tendsto_zero_of_selbergDensity_band
    (T : ℕ → ℝ) (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℂ)
    (C δ θ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hT : ∀ᶠ j in atTop, 1 < T j)
    (hD : ∀ᶠ j in atTop, SelbergDensityBound (T j) C δ)
    (hband : ∀ᶠ j in atTop, ∀ n ∈ s j, ∀ m ∈ s j,
      |Real.log m - Real.log n| ≤ θ * (δ * Real.log (T j)))
    (hbudget : Tendsto (fun j =>
      weightedFrequencySpread (s j) (fun n => ‖a j n‖)
        (fun n => Real.log n) / Real.log (T j)) atTop (𝓝 0)) :
    Tendsto (fun j =>
      (sampledSquare (T j) (s j) (a j) -
        finiteGramErrorPairing (s j) (a j) (fun n m =>
          landauSum (T j) (Real.log m - Real.log n))) / (T j : ℂ))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' _
    (show Tendsto (fun j => (2 * C / (δ ^ 2 * (1 - θ ^ 2))) *
      (weightedFrequencySpread (s j) (fun n => ‖a j n‖)
        (fun n => Real.log n) / Real.log (T j))) atTop (𝓝 0) from
      by simpa using tendsto_const_nhds.mul hbudget)
  filter_upwards [hT, hD, hband] with j hjT hjD hjband
  exact sampledSquare_landau_error_of_selbergDensity_band
    (T j) C δ θ (s j) (a j) hjT hC hδ hθ₀ hθ₁ hjband hjD

#print axioms sampledSquare_landau_error_of_selbergDensity_band
#print axioms sampledSquare_landau_error_of_classical_selberg
#print axioms sampledSquare_landau_error_tendsto_zero_of_selbergDensity_band
end RiemannResearch.Analysis.ActualDirichletPolynomialGram
