/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.MellinCesaroHilbert
import RiemannResearch.RH.ParetoResidueMellinContinuation
import RiemannResearch.RH.ParetoNormalizedResidueHilbert

/-!
# Normalized residue Mellin identities with the removable value retained

Source: user-provided
Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md, Section 5;
mathematical details recorded in NormalizedResidueMellinProof.md.

The arithmetic residue is n mod d, whereas the handoff generator is
(n mod d)/d. The scalar normalization below identifies the actual Hilbert
vector and both convergent discrete pairings with the already proved entire
conductor function. The value at one is obtained from that continuation,
not by substituting into an unregularized product with the zeta pole.

-/
noncomputable section
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro ArithmeticCumulative

/-- The normalized analytic Mellin transform equals the actual entire conductor. -/
theorem normalizedResidue_mellin_conductor (d : ℕ) [NeZero d] (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) :
    s * paretoMellin (normalizedResidueHilbert d hd) s =
      nymanConductorLFunction d s := by
  have hi := paretoMellin_residue_conductor d s hs
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  unfold normalizedResidueHilbert
  rw [paretoMellin_smul]
  change s * (((1 / (d : ℝ) : ℝ) : ℂ) * paretoMellin (digitHilbert d 1 hd (by omega)) s) = _
  push_cast
  calc
    _ = (1 / (d : ℂ)) * (s * paretoMellin (digitHilbert d 1 hd (by omega)) s) := by ring
    _ = _ := by rw [hi]; field_simp [hdC]

/-- The exact g_d normalization, with no omitted 1/s or factor d. -/
theorem normalizedResidue_mellin_zeta (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    s * paretoMellin (normalizedResidueHilbert d hd) s =
      (1 / (d : ℂ) - (d : ℂ) ^ (-s)) * riemannZeta s := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  rw [normalizedResidue_mellin_conductor d hd s hs,
    nymanConductorLFunction_eq_conductorZeta,
    ZetaConductorRegularization.conductorZeta_of_ne_one d hs1,
    conductorSymbol_eq_cpow d hd s]
  ring

/-- The actual normalized transform evaluates to log(d)/d at the removable point. -/
theorem normalizedResidue_mellin_one (d : ℕ) (hd : 0 < d) :
    paretoMellin (normalizedResidueHilbert d hd) 1 = (Real.log d : ℂ) / d := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  have h := normalizedResidue_mellin_conductor d hd 1 (by norm_num)
  simpa only [one_mul, nymanConductorLFunction_one] using h

/-- Actual summation of the normalized first-difference series on the full positive half-plane. -/
theorem residueFraction_first_hasSum_conductor (d : ℕ) [NeZero d] (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun k : ℕ => mellinFirst s (k + 1) *
      (residueFraction d (k + 1) : ℂ)) (nymanConductorLFunction d s) := by
  have hB : ∀ n, |hilbertSequence (normalizedResidueHilbert d hd) n| ≤ (1 : ℝ) := by
    intro n
    rw [normalizedResidueHilbert_sequence]
    have hnonneg : 0 ≤ residueFraction d n := by unfold residueFraction; positivity
    rw [abs_of_nonneg hnonneg]
    unfold residueFraction
    apply (div_le_one (by exact_mod_cast hd : (0 : ℝ) < d)).2
    exact_mod_cast (Nat.le_of_lt (Nat.mod_lt n hd))
  have h := hasSum_first_mellin_pairing_of_bounded
    (normalizedResidueHilbert d hd) 1 hB s hs
  rw [normalizedResidueHilbert_sequence,
    normalizedResidue_mellin_conductor d hd s hs] at h
  exact h

/-- The first signed series equals the zeta product with exactly the handoff normalization. -/
theorem residueFraction_first_hasSum_zeta (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    HasSum (fun k : ℕ => mellinFirst s (k + 1) *
      (residueFraction d (k + 1) : ℂ))
      ((1 / (d : ℂ) - (d : ℂ) ^ (-s)) * riemannZeta s) := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  have h := residueFraction_first_hasSum_conductor d hd s hs
  rw [nymanConductorLFunction_eq_conductorZeta,
    ZetaConductorRegularization.conductorZeta_of_ne_one d hs1,
    conductorSymbol_eq_cpow d hd s] at h
  simpa only [mul_comm] using h

/-- This is a value of the convergent first series, not a pole convention for zeta. -/
theorem residueFraction_first_hasSum_one (d : ℕ) (hd : 0 < d) :
    HasSum (fun k : ℕ => mellinFirst 1 (k + 1) *
      (residueFraction d (k + 1) : ℂ)) ((Real.log d : ℂ) / d) := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  simpa only [nymanConductorLFunction_one] using
    residueFraction_first_hasSum_conductor d hd 1 (by norm_num)

/-- The actual normalized second pairing is summable before its value is used. -/
theorem residueFraction_second_pairing_summable (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    Summable (fun k : ℕ => mellinSecond s (k + 1) *
      mean (fun n => (residueFraction d n : ℂ)) (k + 1)) := by
  simpa only [normalizedResidueHilbert_sequence] using
    hilbert_second_pairing_summable (normalizedResidueHilbert d hd) s hs

/-- Exact normalized second-difference Mellin pairing, including the removable point. -/
theorem residueFraction_second_pairing_conductor (d : ℕ) [NeZero d] (hd : 0 < d)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (∑' k : ℕ, mellinSecond s (k + 1) *
      mean (fun n => (residueFraction d n : ℂ)) (k + 1)) =
        nymanConductorLFunction d s := by
  have h := cesaro_mellin_pairing_hilbert (normalizedResidueHilbert d hd) s hs
  rw [normalizedResidueHilbert_sequence,
    normalizedResidue_mellin_conductor d hd s (by linarith)] at h
  exact h

/-- The exact handoff formula for the smoothed generator. -/
theorem residueFraction_second_pairing_zeta (d : ℕ) (hd : 0 < d)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    (∑' k : ℕ, mellinSecond s (k + 1) *
      mean (fun n => (residueFraction d n : ℂ)) (k + 1)) =
        (1 / (d : ℂ) - (d : ℂ) ^ (-s)) * riemannZeta s := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  rw [residueFraction_second_pairing_conductor d hd s hs,
    nymanConductorLFunction_eq_conductorZeta,
    ZetaConductorRegularization.conductorZeta_of_ne_one d hs1,
    conductorSymbol_eq_cpow d hd s]
  ring

/-- The smoothed actual series has the same removable value log(d)/d. -/
theorem residueFraction_second_pairing_one (d : ℕ) (hd : 0 < d) :
    (∑' k : ℕ, mellinSecond 1 (k + 1) *
      mean (fun n => (residueFraction d n : ℂ)) (k + 1)) =
        (Real.log d : ℂ) / d := by
  letI : NeZero d := ⟨ne_of_gt hd⟩
  rw [residueFraction_second_pairing_conductor d hd 1 (by norm_num),
    nymanConductorLFunction_one]

end RiemannResearch.RH.Pareto
