/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ResidueOscillation
import RiemannResearch.RH.QFullCofinalHarmonic
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QDisplacementTranslationCarry
import RiemannResearch.RH.QSievePrimeJump
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# D5: full-conductor CRT oscillation of the actual displacement

Source: user-provided Full_Conductor_RH_Projection_Machinery.pdf, task D5,
Sections 6.2 and 10.1 (6 November 2026). The source supplies the research
question and bounded-displacement strategy. The proofs below strengthen
the requested modulus criterion: a finite bound at one fixed positive
modulus suffices.

Every application uses QFullDisplacement.displacement. The squarefree
annihilator theorem is used only after the checked inclusion of the
squarefree legal space in the full legal space. The displacement is never
replaced by its squarefree analogue. The carry identity retains every
conductor not dividing L, including higher prime powers.

Conditional research reduction: a finite global residue-oscillation
bound for the actual displacement remains Open. Finite-stage periodicity
and complete-Q norm convergence do not establish that bound.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QFullCRTDisplacement
open ZetaTwoHilbert QFullDisplacement QShiftedReciprocal
open RiemannResearch.Analysis.ResidueOscillation

/-- Transfer the bounded-annihilator argument to the actual full displacement. -/
theorem residual_zero_of_physically_bounded
    (C : ℝ) (hb : ∀ n : ℕ, |qSequence displacement n| ≤ C) :
    qResidual = 0 := by
  obtain ⟨D, hD⟩ := B_physical_bounded pResidual
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb 0)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hw : ∀ n : ℕ, |qSequence witness n| ≤ D + C := by
    intro n
    have he : qSequence witness n =
        qSequence (B pResidual) n - qSequence displacement n := by
      change qSequenceLinear (B pResidual - displacement) n = _
      rw [map_sub]
      rfl
    rw [he]
    have ht := abs_sub_le (qSequence (B pResidual) n) 0 (qSequence displacement n)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    exact ht.trans (add_le_add (hD n) (hb n))
  exact qResidual_eq_zero_of_witness_mean_zero
    (QSquarefreeResidualTail.bounded_annihilator_mean_eq_zero witness
      (annihilator_mem_squarefree_orthogonal witness witness_mem_orthogonal)
      (D + C) (add_nonneg hD0 hC0) hw)

/-- At any fixed positive modulus, finite oscillation is equivalent to zero residual. -/
theorem residual_zero_iff_finite_residue_oscillation (L : ℕ) (hL : 0 < L) :
    qResidual = 0 ↔ ∃ C : ℝ, Bound (qSequence displacement) L C := by
  constructor
  · intro hr
    refine ⟨0, ?_⟩
    intro n m _ _ _
    rw [displacement_eq_zero_of_qResidual_eq_zero hr]
    simp [show qSequence (0 : QHilbert) = 0 from map_zero qSequenceLinear]
  · rintro ⟨C, hC⟩
    obtain ⟨D, _, hD⟩ := exists_uniform_bound _ L hL C hC
    exact residual_zero_of_physically_bounded D hD

/-- Conditional research reduction: the global oscillation bound is the open premise. -/
theorem riemannHypothesis_of_finite_residue_oscillation (L : ℕ) (hL : 0 < L)
    (C : ℝ) (hC : Bound (qSequence displacement) L C) : RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (qResidual_eq_zero_iff.mp
      ((residual_zero_iff_finite_residue_oscillation L hL).mpr ⟨C, hC⟩))

/-- If RH fails, no positive modulus has finite global oscillation. -/
theorem unbounded_oscillation_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) (L : ℕ) (hL : 0 < L) (C : ℝ) :
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ n % L = m % L ∧
      C < |qSequence displacement n - qSequence displacement m| := by
  by_contra! h
  apply hRH
  apply riemannHypothesis_of_finite_residue_oscillation L hL C
  intro n m hn hm he
  exact h n m hn hm he

/-- Exact signed translation, retaining the endpoint and every escaping conductor. -/
theorem full_carry_translation (f : ℕ → ℝ) (hf : f 0 = 0) (L t k : ℕ) :
    f (k * L + t) - f t =
      f (k * L) +
        ∑ q ∈ Finset.Icc 1 (k * L + t),
          if ¬ q ∣ L ∧ q ≤ (k * L) % q + t % q
          then Pareto.mobiusDifference q f else 0 := by
  classical
  have ht := QDisplacementTranslationCarry.finite_translation_identity f hf (k * L) t
  have hs :
      (∑ q ∈ Finset.Icc 1 (k * L + t),
        if q ≤ (k * L) % q + t % q then Pareto.mobiusDifference q f else 0) =
      ∑ q ∈ Finset.Icc 1 (k * L + t),
        if ¬ q ∣ L ∧ q ≤ (k * L) % q + t % q
        then Pareto.mobiusDifference q f else 0 := by
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hd : q ∣ L
    · have hd' : q ∣ k * L := dvd_mul_of_dvd_right hd k
      have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
      have hc : ¬ q ≤ (k * L) % q + t % q := by
        rw [Nat.mod_eq_zero_of_dvd hd', zero_add]
        exact not_le_of_gt (Nat.mod_lt t hqpos)
      simp [hd, hc]
    · simp [hd]
  rw [hs] at ht
  linarith


/-- Pointwise convergence can pass a common oscillation bound, with a fixed modulus. -/
theorem riemannHypothesis_of_stage_oscillation (F : ℕ → ℕ → ℝ)
    (L : ℕ) (hL : 0 < L) (C : ℝ)
    (hlim : ∀ n, Tendsto (fun j => F j n) atTop (𝓝 (qSequence displacement n)))
    (hb : ∀ᶠ j : ℕ in atTop, Bound (F j) L C) : RiemannHypothesis :=
  riemannHypothesis_of_finite_residue_oscillation L hL C
    (bound_of_pointwise_limit F _ L C hlim hb)

/-- Complete-Q convergence controls each physical pair, with a growing site factor. -/
theorem pair_difference_le_norm_tail (f g : QHilbert) (n m : ℕ)
    (hg : qSequence g n = qSequence g m) :
    |qSequence f n - qSequence f m| ≤
      Real.sqrt ZetaTwoProbability.zetaTwo * ((n : ℝ) + m) * ‖f - g‖ := by
  have he (k : ℕ) : qSequence (f - g) k = qSequence f k - qSequence g k := by
    change qSequenceLinear (f - g) k = _
    rw [map_sub]
    rfl
  have hr : qSequence f n - qSequence f m =
      qSequence (f - g) n - qSequence (f - g) m := by rw [he, he, hg]; ring
  rw [hr]
  calc
    _ ≤ |qSequence (f - g) n| + |qSequence (f - g) m| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (qSequence (f - g) n) 0 (qSequence (f - g) m)
    _ ≤ Real.sqrt ZetaTwoProbability.zetaTwo * (n : ℝ) * ‖f - g‖ +
        Real.sqrt ZetaTwoProbability.zetaTwo * (m : ℝ) * ‖f - g‖ :=
      add_le_add (QPrimePowerSieve.qSequence_abs_le (f - g) n)
        (QPrimePowerSieve.qSequence_abs_le (f - g) m)
    _ = _ := by ring

/-- Specialization keeps the actual full-conductor displacement and its anchor. -/
theorem displacement_carry_translation (L t k : ℕ) :
    qSequence displacement (k * L + t) - qSequence displacement t =
      qSequence displacement (k * L) +
        ∑ q ∈ Finset.Icc 1 (k * L + t),
          if ¬ q ∣ L ∧ q ≤ (k * L) % q + t % q
          then Pareto.mobiusDifference q (qSequence displacement) else 0 :=
  full_carry_translation _ (qSequence_zero _) L t k

end RiemannResearch.RH.QFullCRTDisplacement
