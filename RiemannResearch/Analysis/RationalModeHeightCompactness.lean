/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalHorizontalEndpoint
import RiemannResearch.Analysis.WeightedFourierStrengthenedClasses
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Compact arithmetic-height tails across all rational modes

The mode envelope is independent of the prime set. Rational arithmetic-height
sublevels are finite even when all positive numerator/denominator pairs are
admitted. Therefore an arbitrarily slowly diverging stronger weight gives
uniform corrected Fourier convergence across the whole rational mode family,
not only on one fixed finite prime torus. This strengthens the finite-prime
Fourier-uniformity discussion in Section 7 of
`FRZ_Strengthening_2026-11-10.pdf`. The only analytic premise remains the
explicit Selberg density provider.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem nat_log_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  cases n with
  | zero => simp
  | succ n => exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

theorem finite_rationalModeWeight_sublevel (B : ℝ) :
    Set.Finite {i : ℕ × ℕ | rationalModeWeight i.1 i.2 ≤ B} := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp B)
  apply ((Set.finite_Iio N).prod (Set.finite_Iio N)).subset
  intro i hi
  have hb : Real.log (i.1 : ℝ) + Real.log (i.2 : ℝ) ≤ B := by
    dsimp [rationalModeWeight] at hi
    rw [abs_of_nonneg (add_nonneg (nat_log_nonneg i.1) (nat_log_nonneg i.2))] at hi
    linarith
  have hbound (n : ℕ) (hn : Real.log (n : ℝ) ≤ B) : n < N := by
    have hcast : (n : ℝ) ≤ Real.exp B := by
      by_cases hn0 : n = 0
      · subst n
        simp only [Nat.cast_zero]
        exact (Real.exp_pos B).le
      · have hp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
        rw [← Real.exp_log hp]
        exact Real.exp_le_exp.mpr hn
    exact_mod_cast hcast.trans_lt hN
  exact ⟨hbound i.1 (by linarith [nat_log_nonneg i.2]),
    hbound i.2 (by linarith [nat_log_nonneg i.1])⟩

theorem finite_positiveRationalModeWeight_sublevel (B : ℝ) :
    Set.Finite {i : ℕ+ × ℕ+ | rationalModeWeight i.1 i.2 ≤ B} := by
  let f : ℕ+ × ℕ+ → ℕ × ℕ := fun i => (i.1, i.2)
  have hinj : Function.Injective f := by
    intro i j hij
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hij
    · apply Subtype.ext
      exact congrArg Prod.snd hij
  exact Set.Finite.preimage hinj.injOn (finite_rationalModeWeight_sublevel B)

/-- A stronger weighted unit ball can vary over every positive rational mode
at once. In particular the prime support need not remain in a fixed set. -/
theorem eventually_uniform_allRational_multiplierBall
    (Φ : ℝ → ℝ) (hΦpos : ∀ x, 1 ≤ x → 0 < Φ x)
    (hΦ : Tendsto Φ atTop atTop) (hD : UniformSelbergDensity (1 / 4))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ c : (ℕ+ × ℕ+) → ℂ,
      Summable (fun i => ‖c i‖ *
        (rationalModeWeight i.1 i.2 ^ 2 * Φ (rationalModeWeight i.1 i.2))) →
      Fourier.weightedFourierMass c
        (fun i => rationalModeWeight i.1 i.2 ^ 2 * Φ (rationalModeWeight i.1 i.2)) ≤ 1 →
      ‖(Real.log T : ℂ) * ∑' i, c i * correctedRationalRemainder T i.1 i.2‖ ≤ ε := by
  obtain ⟨K, hK, hb⟩ := eventually_log_mul_correctedRationalRemainder_le hD
  let w : ℕ+ × ℕ+ → ℝ := fun i => rationalModeWeight i.1 i.2
  have hw1 : ∀ i, 1 ≤ w i := by
    intro i
    dsimp [w, rationalModeWeight]
    linarith [abs_nonneg (Real.log (i.1 : ℝ) + Real.log (i.2 : ℝ))]
  have hw : ∀ i, 0 < w i ^ 2 := by intro i; have := hw1 i; positivity
  have h := Fourier.eventually_uniform_weightedFourier_multiplierBall
    (fun T i => (Real.log T : ℂ) * correctedRationalRemainder T i.1 i.2)
    w (fun i => w i ^ 2) Φ K hK hw (fun i => hΦpos _ (hw1 i))
    finite_positiveRationalModeWeight_sublevel hΦ
    (fun i => tendsto_log_mul_correctedRationalRemainder i.1.pos i.2.pos
      (1 / 4) (by norm_num) hD)
    (hb.mono (fun T hT i => hT _ _ i.1.pos i.2.pos)) ε hε
  filter_upwards [h] with T hT
  intro c hc hmass
  have hh := hT c hc hmass
  convert hh using 1
  congr 1
  rw [Fourier.weightedFourierPairing, ← tsum_mul_left]
  apply tsum_congr
  intro i
  ring

end RiemannResearch.Analysis.ActualZeroOrdinate
