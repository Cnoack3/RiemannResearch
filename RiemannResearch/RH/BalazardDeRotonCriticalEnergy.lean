/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoBoundedMellin
import RiemannResearch.RH.DampedMobiusHardyBridge
import RiemannResearch.RH.DampedMobiusSquarefreeClosure
import RiemannResearch.RH.ArithmeticFloorHilbertSeries
import RiemannResearch.RH.DampedMobiusSeed
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.HardyMobiusFamily
import RiemannResearch.RH.ParetoMellinHardyNorm
import RiemannResearch.RH.ParetoMellinFunctional
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Balazard--de Roton error splitting with the discrete charge retained

Source: Michel Balazard and Anne de Roton, "Sur un critère de Báez-Duarte
pour l'hypothèse de Riemann", https://arxiv.org/abs/0812.1689,
Section 2, Proposition 1, for the two-error splitting strategy.
The actual Pareto cutoff requires its reciprocal-charge correction.
All finite Mellin and norm identities below are unconditional.
Small signed energy is an explicit open hypothesis in the RH consumer;
neither the paper's RH-conditional estimates nor RH are asserted here.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.BalazardDeRoton

def polynomial (ε : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range N,
    (dampedMobiusWeight ε (m + 1) : ℂ) * ((m + 1 : ℕ) : ℂ) ^ (-s)

def charge (ε : ℝ) (N : ℕ) : ℂ :=
  ∑ m ∈ Finset.range N,
    (dampedMobiusWeight ε (m + 1) : ℂ) / ((m + 1 : ℕ) : ℂ)

def bias (ε : ℝ) (s : ℂ) : ℂ :=
  (1 - riemannZeta s / riemannZeta (s + ε)) / s

def correctedTail (ε : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s / s *
    ((riemannZeta (s + ε))⁻¹ - polynomial ε N s + charge ε N)

/-- Pure finite algebra; even a zero denominator is not divided out in this proof. -/
theorem residual_split (ε : ℝ) (N : ℕ) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    1 / s - dampedHardyMobiusSum ε N s = bias ε s + correctedTail ε N s := by
  rw [dampedHardyMobiusSum_eq_zeta ε N s hs hs1]
  unfold bias correctedTail polynomial charge
  simp only [div_eq_mul_inv]
  ring

private theorem mellin_neg (f : ThresholdHilbert) (s : ℂ) :
    paretoMellin (-f) s = -paretoMellin f s := by
  simpa using paretoMellin_smul (-1) f s

/-- The finite family admits its literal Mellin formula on Re(s)>0,
including the critical line. -/
theorem partial_mellin_of_pos (ε : ℝ) (N : ℕ) (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) s =
      dampedHardyMobiusSum ε N s := by
  have hb (m : ℕ) (_ : m ∈ Finset.range N) (n : ℕ) :
      |hilbertSequence (arithmeticResidueTerm (dampedMobiusWeight ε) m) n| ≤
        |dampedMobiusWeight ε (m + 1)| := by
    rw [arithmeticResidueTerm_eq_normalized]
    have he := congrFun (hilbertSequenceLinear.map_smul
      (dampedMobiusWeight ε (m + 1))
      (normalizedResidueHilbert (m + 1) (Nat.succ_pos m))) n
    change hilbertSequence (_ • _) n = _ at he
    rw [he]
    change |dampedMobiusWeight ε (m + 1) *
      hilbertSequence (normalizedResidueHilbert (m + 1) (Nat.succ_pos m)) n| ≤ _
    rw [normalizedResidueHilbert_sequence]
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (residueFraction_abs_le_one (m + 1) n (Nat.succ_pos m))
      (abs_nonneg (dampedMobiusWeight ε (m + 1)))
  rw [arithmeticFloorHilbertPartial, mellin_neg,
    paretoMellin_finset_sum_of_bounded (Finset.range N)
      (arithmeticResidueTerm (dampedMobiusWeight ε))
      (fun m => |dampedMobiusWeight ε (m + 1)|) hb s hs]
  simp_rw [arithmeticResidueTerm_eq_normalized, paretoMellin_smul,
    normalizedResidue_mellin_eq_neg_hardyMobiusGenerator _ _ s hs]
  simp only [Complex.real_smul, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rfl

theorem residual_mellin_of_pos (ε : ℝ) (N : ℕ) (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (hilbertOne -
      arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) s =
      1 / s - dampedHardyMobiusSum ε N s := by
  have h1 (n : ℕ) : |hilbertSequence hilbertOne n| ≤ (1 : ℝ) := by
    rw [hilbertOne_sequence]
    by_cases hn : n = 0 <;> simp [zeroAnchor, hn]
  have hF (n : ℕ) :
      |hilbertSequence (-arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) n| ≤
        ∑ m ∈ Finset.range N, |dampedMobiusWeight ε (m + 1)| := by
    have he := congrFun (hilbertSequenceLinear.map_neg
      (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N)) n
    change hilbertSequence (-_) n = _ at he
    rw [he]
    change |-hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) n| ≤ _
    rw [abs_neg]
    exact dampedMobius_partial_abs_le ε N n
  rw [sub_eq_add_neg,
    paretoMellin_add_of_bounded _ _ 1 _ h1 hF s hs,
    paretoMellin_one_of_pos s hs, mellin_neg, partial_mellin_of_pos ε N s hs,
    sub_eq_add_neg]

def criticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

theorem criticalPoint_re (t : ℝ) : (criticalPoint t).re = 1 / 2 := by
  simp [criticalPoint]

theorem critical_residual_split (ε : ℝ) (N : ℕ) (t : ℝ) :
    paretoMellin (hilbertOne -
      arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) (criticalPoint t) =
      bias ε (criticalPoint t) + correctedTail ε N (criticalPoint t) := by
  have hs : 0 < (criticalPoint t).re := by rw [criticalPoint_re]; norm_num
  have hs1 : criticalPoint t ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [criticalPoint_re] at this
    norm_num at this
  rw [residual_mellin_of_pos ε N _ hs, residual_split ε N _ hs hs1]

/-- Full infinite physical energy, not a truncated physical sum. -/
theorem critical_energy (ε : ℝ) (N : ℕ) :
    ‖hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N‖ ^ 2 =
      (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖bias ε (criticalPoint t) + correctedTail ε N (criticalPoint t)‖ ^ 2 := by
  rw [← dampedMobius_residual_critical_line_norm ε N]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [show (1 / 2 : ℂ) + (t : ℂ) * Complex.I = criticalPoint t from rfl,
    critical_residual_split]

/-- A single actual critical-line budget suffices. This is a proposition,
not an assertion that the required small errors exist. -/
def CriticalApproximation : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
    (1 / (2 * Real.pi)) * (∫ t : ℝ,
      ‖bias ε (criticalPoint t) + correctedTail ε N (criticalPoint t)‖ ^ 2) ≤ δ

theorem criticalApproximation_iff_hardy :
    CriticalApproximation ↔ DampedHardyApproximation := by
  constructor
  · intro h δ hδ
    obtain ⟨ε, hε, N, hN⟩ := h δ hδ
    refine ⟨ε, hε, N, (dampedMobius_residual_norm_sq_le_iff ε N δ).mp ?_⟩
    rwa [critical_energy ε N]
  · intro h δ hδ
    obtain ⟨ε, hε, N, hN⟩ := h δ hδ
    refine ⟨ε, hε, N, ?_⟩
    rw [← critical_energy ε N]
    exact (dampedMobius_residual_norm_sq_le_iff ε N δ).mpr hN

/-- Conditional research reduction; the critical energy budget remains open. -/
theorem riemannHypothesis_of_criticalApproximation (h : CriticalApproximation) :
    RiemannHypothesis :=
  riemannHypothesis_of_dampedHardyApproximation
    (criticalApproximation_iff_hardy.mp h)

/-- The same open budget yields the actual squarefree Q closure. -/
theorem qSquarefreeClosure_of_criticalApproximation (h : CriticalApproximation) :
    ZetaTwoHilbert.qOne ∈ ZetaTwoProbability.qSquarefreeCRTSpan.topologicalClosure :=
  qSquarefreeClosure_of_dampedHardyApproximation
    (criticalApproximation_iff_hardy.mp h)

end RiemannResearch.RH.Pareto.BalazardDeRoton

namespace RiemannResearch.RH.Pareto.BalazardDeRoton

def lineEnergy (f : ℝ → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖f t‖ ^ 2

def mixedEnergy (f g : ℝ → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ, inner ℝ (f t) (g t)

/-- Exact signed error, under genuine L2 assumptions on the two components.
These assumptions are not inferred from cancellation in their sum. -/
theorem signed_energy (ε : ℝ) (N : ℕ)
    (hb : MemLp (fun t : ℝ => bias ε (criticalPoint t)) 2)
    (ht : MemLp (fun t : ℝ => correctedTail ε N (criticalPoint t)) 2) :
    ‖hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N‖ ^ 2 =
      lineEnergy (fun t => bias ε (criticalPoint t)) +
      lineEnergy (fun t => correctedTail ε N (criticalPoint t)) +
      2 * mixedEnergy (fun t => bias ε (criticalPoint t))
        (fun t => correctedTail ε N (criticalPoint t)) := by
  let B : ℝ → ℂ := fun t => bias ε (criticalPoint t)
  let T : ℝ → ℂ := fun t => correctedTail ε N (criticalPoint t)
  have hb2 : Integrable (fun t : ℝ => ‖B t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hb.1).mp hb
  have ht2 : Integrable (fun t : ℝ => ‖T t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm ht.1).mp ht
  have hsum : Integrable (fun t : ℝ => ‖B t + T t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (hb.add ht).1).mp (hb.add ht)
  have hi (t : ℝ) :
      inner ℝ (B t) (T t) =
        (‖B t + T t‖ ^ 2 - (‖B t‖ ^ 2 + ‖T t‖ ^ 2)) / 2 := by
    nlinarith [norm_add_sq_real (B t) (T t)]
  have hc : Integrable (fun t : ℝ => inner ℝ (B t) (T t)) := by
    apply ((hsum.sub (hb2.add ht2)).div_const 2).congr
    filter_upwards [] with t
    exact (hi t).symm
  have he :
      (∫ t : ℝ, ‖B t + T t‖ ^ 2) =
        (∫ t : ℝ, ‖B t‖ ^ 2) + (∫ t : ℝ, ‖T t‖ ^ 2) +
          2 * ∫ t : ℝ, inner ℝ (B t) (T t) := by
    calc
      _ = ∫ t : ℝ, (‖B t‖ ^ 2 + ‖T t‖ ^ 2) +
          2 * inner ℝ (B t) (T t) := by
        apply integral_congr_ae
        filter_upwards [] with t
        nlinarith [norm_add_sq_real (B t) (T t)]
      _ = _ := by
        have hab : Integrable (fun t : ℝ => ‖B t‖ ^ 2 + ‖T t‖ ^ 2) := hb2.add ht2
        rw [integral_add hab (hc.const_mul 2),
          integral_add hb2 ht2, integral_const_mul]
  rw [critical_energy]
  change (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖B t + T t‖ ^ 2) = _
  rw [he]
  unfold lineEnergy mixedEnergy
  dsimp [B, T]
  ring

/-- The complete nonnegative remainder discarded by the factor-two bound. -/
theorem factor_two_exact_gap (ε : ℝ) (N : ℕ)
    (hb : MemLp (fun t : ℝ => bias ε (criticalPoint t)) 2)
    (ht : MemLp (fun t : ℝ => correctedTail ε N (criticalPoint t)) 2) :
    2 * (lineEnergy (fun t => bias ε (criticalPoint t)) +
      lineEnergy (fun t => correctedTail ε N (criticalPoint t))) -
      ‖hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N‖ ^ 2 =
      lineEnergy (fun t => bias ε (criticalPoint t) -
        correctedTail ε N (criticalPoint t)) := by
  let B : ℝ → ℂ := fun t => bias ε (criticalPoint t)
  let T : ℝ → ℂ := fun t => correctedTail ε N (criticalPoint t)
  have hb2 : Integrable (fun t : ℝ => ‖B t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hb.1).mp hb
  have ht2 : Integrable (fun t : ℝ => ‖T t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm ht.1).mp ht
  have hsum : Integrable (fun t : ℝ => ‖B t + T t‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (hb.add ht).1).mp (hb.add ht)
  have he :
      (∫ t : ℝ, ‖B t - T t‖ ^ 2) =
        2 * ((∫ t : ℝ, ‖B t‖ ^ 2) + (∫ t : ℝ, ‖T t‖ ^ 2)) -
          ∫ t : ℝ, ‖B t + T t‖ ^ 2 := by
    calc
      _ = ∫ t : ℝ, 2 * (‖B t‖ ^ 2 + ‖T t‖ ^ 2) -
          ‖B t + T t‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [] with t
        nlinarith [norm_add_sq_real (B t) (T t), norm_sub_sq_real (B t) (T t)]
      _ = _ := by
        have hab : Integrable (fun t : ℝ => ‖B t‖ ^ 2 + ‖T t‖ ^ 2) := hb2.add ht2
        rw [integral_sub (hab.const_mul 2) hsum,
          integral_const_mul, integral_add hb2 ht2]
  rw [critical_energy]
  unfold lineEnergy
  change 2 * ((1 / (2 * Real.pi)) * (∫ t : ℝ, ‖B t‖ ^ 2) +
    (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖T t‖ ^ 2)) -
    (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖B t + T t‖ ^ 2) =
    (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖B t - T t‖ ^ 2)
  rw [he]
  ring

/-- Conditional research reduction preserving cancellation. Neither component
energy is required to tend to zero separately. The stated budget is open. -/
theorem riemannHypothesis_of_signed_budget
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      MemLp (fun t : ℝ => bias ε (criticalPoint t)) 2 ∧
      MemLp (fun t : ℝ => correctedTail ε N (criticalPoint t)) 2 ∧
      lineEnergy (fun t => bias ε (criticalPoint t)) +
        lineEnergy (fun t => correctedTail ε N (criticalPoint t)) +
        2 * mixedEnergy (fun t => bias ε (criticalPoint t))
          (fun t => correctedTail ε N (criticalPoint t)) ≤ δ) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_criticalApproximation
  intro δ hδ
  obtain ⟨ε, hε, N, hb, ht, hN⟩ := h δ hδ
  refine ⟨ε, hε, N, ?_⟩
  rw [← critical_energy, signed_energy ε N hb ht]
  exact hN

end RiemannResearch.RH.Pareto.BalazardDeRoton
