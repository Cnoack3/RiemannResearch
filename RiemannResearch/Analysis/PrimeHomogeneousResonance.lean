/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeBandlimitedWeil
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Lean.Elab.Tactic.Omega

/-! # Homogeneous cancellation in the band-limited Weil identity

Source: user-provided Montgomery_Pair_Correlation_Lean_Handoff.md, Section 3.
The analytic baseline is the checked Guinand--Weil specialization in
PrimeBandlimitedWeil. Equal total prime-factor degree kills the arithmetic
correction exactly. This does not remove the pole or gamma terms, estimate
the gamma remainder, or prove a raw-ordinate asymptotic.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ArithmeticFunction ArithmeticFunction.Omega
namespace RiemannResearch.Analysis.PrimeBandlimitedWeil

theorem eq_of_dvd_of_cardFactors_eq {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (hd : m ∣ n) (hdeg : Ω n = Ω m) : n = m := by
  obtain ⟨k, rfl⟩ := hd
  have hk : k ≠ 0 := by intro h; simp [h] at hn
  rw [ArithmeticFunction.cardFactors_mul hm hk] at hdeg
  have hz : Ω k = 0 := by omega
  have hk1 : k = 1 :=
    (ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp hz).resolve_left hk
  simp [hk1]

theorem resonance_eq_zero_of_cardFactors_eq {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hdeg : Ω n = Ω m) : resonance n m = 0 := by
  by_cases h : n = m
  · subst n; exact resonance_self m hm
  · have hnm : ¬m ∣ n := fun hd =>
      h (eq_of_dvd_of_cardFactors_eq hn.ne' hm.ne' hd hdeg)
    have hmn : ¬n ∣ m := fun hd =>
      h (eq_of_dvd_of_cardFactors_eq hm.ne' hn.ne' hd hdeg.symm).symm
    simp [resonance, directionalResonance, hnm, hmn]

theorem homogeneous_resonance_quadratic_zero {ι : Type*} (s : Finset ι)
    (n : ι → ℕ) (c : ι → ℂ) (d : ℕ)
    (hn : ∀ i ∈ s, 0 < n i) (hd : ∀ i ∈ s, Ω (n i) = d) :
    ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j) * (resonance (n i) (n j) : ℂ) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [resonance_eq_zero_of_cardFactors_eq (hn i hi) (hn j hj) ((hd i hi).trans (hd j hj).symm)]
  simp

/-- The full zero sum on an equal-Omega block: poles and gamma integral remain. -/
theorem actual_zero_sum_homogeneous {F : ℝ → ℂ} (hFd : ContDiff ℝ 2 F)
    (hF : Function.support F ⊆ Set.Icc (-1 : ℝ) 1) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hdeg : Ω n = Ω m) {T : ℝ}
    (hTn : (n : ℝ) + 1 < T) (hTm : (m : ℝ) + 1 < T) :
    let k := frequencyTest F T (logRatio n m)
    Summable (fun ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier =>
      ((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) *
        Zeta23.paperFT k (Zeta23.gammaOf ρ)) ∧
    (∑' ρ : (Zeta23.zetaZeros Zeta23.zetaSeam).carrier,
      ((Zeta23.zetaZeros Zeta23.zetaSeam).mult ρ : ℂ) *
        Zeta23.paperFT k (Zeta23.gammaOf ρ)) =
      Zeta23.paperFT k (Complex.I / 2) + Zeta23.paperFT k (-Complex.I / 2) +
        (1 / (2 * Real.pi) : ℂ) *
          ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ) := by
  simpa only [resonance_eq_zero_of_cardFactors_eq hn hm hdeg, Complex.ofReal_zero,
    mul_zero, sub_zero] using actual_zero_sum_eq_resonance hFd hF hn hm hTn hTm

end RiemannResearch.Analysis.PrimeBandlimitedWeil
