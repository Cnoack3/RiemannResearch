/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.WeightedSharedFamilyEnergy
import RiemannResearch.NumberTheory.RadicalFiberSeparation
import RiemannResearch.RH.QSquarefreeConstraintEnergy
import RiemannResearch.RH.SquarefreeParetoConstraintEnergy
import RiemannResearch.RH.QSquarefreeFiniteDualClosure
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete Q and Pareto energy from finite radical-fiber families

Source: user-provided two-fiber certificates and requested generalization,
29 October 2026. All physical support disjointness, radical constraints,
summability, omitted coordinates, and completed squares are supplied here.
These are lower-energy certificates, not an upper-energy provider for RH.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.SquarefreeMultiFiberEnergy
open UniqueFactorizationMonoid ZetaTwoHilbert ZetaTwoProbability
open QSquarefreeFiniteDualClosure QSquarefreeConstraintEnergy
open SquarefreeParetoConstraintEnergy ZetaTwoParetoTransfer Pareto
open RiemannResearch.Analysis.WeightedSharedFamilyEnergy

theorem radical_family_separated {d : ℕ} {T : Finset ℕ}
    (hd : 2 ≤ d) (ht : ∀ m ∈ T, d + 1 < m)
    (hr : ∀ m ∈ T, radical m = d) : Separated T := by
  intro m hm n hn hmn
  exact Nat.radical_fiber_pairs_disjoint hd (by have := ht m hm; omega)
    (by have := ht n hn; omega) (hr m hm) (hr n hn) hmn

theorem radical_family_relations (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d : ℕ} {T : Finset ℕ} (hd : 2 ≤ d) (ht : ∀ m ∈ T, d + 1 < m)
    (hr : ∀ m ∈ T, radical m = d) (hh : qSequence F (d - 1) = 1) :
    ∀ m ∈ T, qSequence F d + qSequence F (m - 1) - qSequence F m = 1 := by
  intro m hm
  exact constrained_radical_fiber_relation F hF (by have := ht m hm; omega)
    (hr m hm) hh

theorem radical_family_q_completion (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d : ℕ} {T : Finset ℕ} (hd : 2 ≤ d) (ht : ∀ m ∈ T, d + 1 < m)
    (hr : ∀ m ∈ T, radical m = d)
    (hh : ∀ n, 0 < n → n < d → qSequence F n = 1) :
    ‖F‖ ^ 2 =
      (qHeadEnergy d +
        familyConductance inverseSquareDenominator T /
          (1 + (d : ℝ) ^ 2 * familyConductance inverseSquareDenominator T) +
        familyRemainder inverseSquareDenominator (qSequence F) d T +
        familyOmittedEnergy inverseSquareDenominator (qSequence F) d T) / zetaTwo := by
  have h := complete_family_completion inverseSquareDenominator (qSequence F)
    ht (radical_family_separated hd ht hr) (raw_Q_summable F) hh
    (fun n => sq_nonneg (n : ℝ)) (by unfold inverseSquareDenominator; positivity)
    (by
      intro m hm
      have hm0 : 0 < m := by have := ht m hm; omega
      have hm1 : 0 < m - 1 := by have := ht m hm; omega
      constructor <;> unfold inverseSquareDenominator <;> positivity)
    (radical_family_relations F hF hd ht hr (hh (d - 1) (by omega) (by omega)))
  rw [raw_Q_energy] at h
  apply (eq_div_iff zetaTwo_pos.ne').mpr
  simpa only [qHeadEnergy, inverseSquareDenominator, mul_comm] using h

theorem radical_family_q_lower_bound (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d : ℕ} {T : Finset ℕ} (hd : 2 ≤ d) (ht : ∀ m ∈ T, d + 1 < m)
    (hr : ∀ m ∈ T, radical m = d)
    (hh : ∀ n, 0 < n → n < d → qSequence F n = 1) :
    (qHeadEnergy d + familyConductance inverseSquareDenominator T /
      (1 + (d : ℝ) ^ 2 * familyConductance inverseSquareDenominator T)) / zetaTwo ≤
      ‖F‖ ^ 2 := by
  rw [radical_family_q_completion F hF hd ht hr hh]
  apply (div_le_div_iff_of_pos_right zetaTwo_pos).mpr
  have hR := familyRemainder_nonneg inverseSquareDenominator (qSequence F) d T
    (fun n => sq_nonneg (n : ℝ))
  have hO := familyOmittedEnergy_nonneg inverseSquareDenominator (qSequence F) d T
    (fun n => sq_nonneg (n : ℝ))
  linarith

theorem radical_family_pareto_completion (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d : ℕ} {T : Finset ℕ} (hd : 2 ≤ d) (ht : ∀ m ∈ T, d + 1 < m)
    (hr : ∀ m ∈ T, radical m = d)
    (hh : ∀ n, 0 < n → n < d → qSequence F n = 1) :
    ‖toPareto F‖ ^ 2 = ((d : ℝ) - 1) / d +
      familyConductance paretoDenominator T /
        (1 + (d : ℝ) * ((d : ℝ) + 1) * familyConductance paretoDenominator T) +
      familyRemainder paretoDenominator (qSequence F) d T +
      familyOmittedEnergy paretoDenominator (qSequence F) d T := by
  have h := complete_family_completion paretoDenominator (qSequence F)
    ht (radical_family_separated hd ht hr) (raw_P_summable F) hh
    paretoDenominator_nonneg (paretoDenominator_pos (by omega))
    (by
      intro m hm
      have := ht m hm
      exact ⟨paretoDenominator_pos (by omega), paretoDenominator_pos (by omega)⟩)
    (radical_family_relations F hF hd ht hr (hh (d - 1) (by omega) (by omega)))
  rw [raw_P_energy, pareto_head_energy hd] at h
  exact h

theorem radical_family_pareto_lower_bound (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d : ℕ} {T : Finset ℕ} (hd : 2 ≤ d) (ht : ∀ m ∈ T, d + 1 < m)
    (hr : ∀ m ∈ T, radical m = d)
    (hh : ∀ n, 0 < n → n < d → qSequence F n = 1) :
    ((d : ℝ) - 1) / d + familyConductance paretoDenominator T /
      (1 + (d : ℝ) * ((d : ℝ) + 1) * familyConductance paretoDenominator T) ≤
      ‖toPareto F‖ ^ 2 := by
  rw [radical_family_pareto_completion F hF hd ht hr hh]
  have hR := familyRemainder_nonneg paretoDenominator (qSequence F) d T
    paretoDenominator_nonneg
  have hO := familyOmittedEnergy_nonneg paretoDenominator (qSequence F) d T
    paretoDenominator_nonneg
  linarith

/-- Native Pareto statement: compatibility is an explicit physical-coordinate
condition; no Q/P projection identification is assumed. -/
theorem native_pareto_family_lower_bound (F : ThresholdHilbert)
    (hF : ∀ m, 2 ≤ m →
      hilbertSequence F m - hilbertSequence F (m - 1) =
        hilbertSequence F (radical m) - hilbertSequence F (radical m - 1))
    {d : ℕ} {T : Finset ℕ} (hd : 2 ≤ d) (ht : ∀ m ∈ T, d + 1 < m)
    (hr : ∀ m ∈ T, radical m = d)
    (hh : ∀ n, 0 < n → n < d → hilbertSequence F n = 1) :
    ((d : ℝ) - 1) / d + familyConductance paretoDenominator T /
      (1 + (d : ℝ) * ((d : ℝ) + 1) * familyConductance paretoDenominator T) ≤
      ‖F‖ ^ 2 := by
  have hq : QParetoEquivalence.toQ F ∈ radicalCompatible := by
    intro m hm
    simpa only [SquarefreeRadicalDifference.qDifference,
      QParetoEquivalence.toQ_sequence] using hF m hm
  have h := radical_family_pareto_lower_bound (QParetoEquivalence.toQ F)
    hq hd ht hr (by simpa only [QParetoEquivalence.toQ_sequence] using hh)
  simpa only [QParetoEquivalence.toPareto_toQ] using h

/-- Radical constraints alone cannot give a lower certificate above unit
energy: the actual unit sequence is compatible in both Hilbert metrics.
This does not assert that the unit sequence belongs to the closed legal span. -/
theorem radical_family_certificates_le_one {d : ℕ} {T : Finset ℕ}
    (hd : 2 ≤ d) (ht : ∀ m ∈ T, d + 1 < m)
    (hr : ∀ m ∈ T, radical m = d) :
    (qHeadEnergy d + familyConductance inverseSquareDenominator T /
      (1 + (d : ℝ) ^ 2 * familyConductance inverseSquareDenominator T)) / zetaTwo ≤ 1 ∧
    ((d : ℝ) - 1) / d + familyConductance paretoDenominator T /
      (1 + (d : ℝ) * ((d : ℝ) + 1) * familyConductance paretoDenominator T) ≤ 1 := by
  have hh : ∀ n, 0 < n → n < d → qSequence qOne n = 1 := by
    intro n hn _
    simp only [qSequence_qOne, qOneSequence, if_neg (Nat.ne_of_gt hn)]
  constructor
  · simpa only [qOne_norm_sq] using
      radical_family_q_lower_bound qOne qOne_mem_radicalCompatible hd ht hr hh
  · simpa only [toPareto_qOne, hilbertOne_norm_sq] using
      radical_family_pareto_lower_bound qOne qOne_mem_radicalCompatible hd ht hr hh

def qPowerConductance (d : ℕ) (K : Finset ℕ) : ℝ :=
  ∑ k ∈ K, 1 / ((((d ^ k - 1 : ℕ) : ℝ) ^ 2) + ((d : ℝ) ^ k) ^ 2)

def pPowerConductance (d : ℕ) (K : Finset ℕ) : ℝ :=
  ∑ k ∈ K, 1 / (2 * ((d : ℝ) ^ k) ^ 2)

theorem power_family_data {d : ℕ} {K : Finset ℕ}
    (hd : 2 ≤ d) (hs : Squarefree d) (hk : ∀ k ∈ K, 2 ≤ k) :
    (∀ m ∈ K.image (fun k => d ^ k), d + 1 < m) ∧
    (∀ m ∈ K.image (fun k => d ^ k), radical m = d) := by
  constructor <;> intro m hm <;> obtain ⟨k, hkK, rfl⟩ := Finset.mem_image.mp hm
  · exact Nat.power_fiber_beyond_head hd (hk k hkK)
  · exact Nat.radical_pow_eq_of_squarefree hd hs (by have := hk k hkK; omega)

theorem q_power_conductance_eq {d : ℕ} (hd : 2 ≤ d) (K : Finset ℕ) :
    familyConductance inverseSquareDenominator (K.image (fun k => d ^ k)) =
      qPowerConductance d K := by
  have hinj : Function.Injective (fun k : ℕ => d ^ k) :=
    (show StrictMono (fun k : ℕ => d ^ k) from
      fun _ _ h => Nat.pow_lt_pow_right (by omega) h).injective
  unfold familyConductance qPowerConductance
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
  simp only [inverseSquareDenominator, Nat.cast_pow]

theorem pareto_pair_denominator {m : ℕ} (hm : 0 < m) :
    paretoDenominator (m - 1) + paretoDenominator m = 2 * (m : ℝ) ^ 2 := by
  unfold paretoDenominator
  rw [Nat.cast_sub (by omega : 1 ≤ m)]
  push_cast
  ring

theorem p_power_conductance_eq {d : ℕ} (hd : 2 ≤ d) (K : Finset ℕ) :
    familyConductance paretoDenominator (K.image (fun k => d ^ k)) =
      pPowerConductance d K := by
  have hinj : Function.Injective (fun k : ℕ => d ^ k) :=
    (show StrictMono (fun k : ℕ => d ^ k) from
      fun _ _ h => Nat.pow_lt_pow_right (by omega) h).injective
  unfold familyConductance pPowerConductance
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
  apply Finset.sum_congr rfl
  intro k _
  rw [pareto_pair_denominator (pow_pos (by omega : 0 < d) k), Nat.cast_pow]

theorem power_family_q_lower_bound (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d : ℕ} {K : Finset ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hk : ∀ k ∈ K, 2 ≤ k)
    (hh : ∀ n, 0 < n → n < d → qSequence F n = 1) :
    (qHeadEnergy d + qPowerConductance d K /
      (1 + (d : ℝ) ^ 2 * qPowerConductance d K)) / zetaTwo ≤ ‖F‖ ^ 2 := by
  obtain ⟨ht, hr⟩ := power_family_data hd hs hk
  simpa only [q_power_conductance_eq hd] using
    radical_family_q_lower_bound F hF hd ht hr hh

theorem power_family_pareto_lower_bound (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d : ℕ} {K : Finset ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hk : ∀ k ∈ K, 2 ≤ k)
    (hh : ∀ n, 0 < n → n < d → qSequence F n = 1) :
    ((d : ℝ) - 1) / d + pPowerConductance d K /
      (1 + (d : ℝ) * ((d : ℝ) + 1) * pPowerConductance d K) ≤ ‖toPareto F‖ ^ 2 := by
  obtain ⟨ht, hr⟩ := power_family_data hd hs hk
  simpa only [p_power_conductance_eq hd] using
    radical_family_pareto_lower_bound F hF hd ht hr hh

/-- Both actual Hilbert metrics for every closed-legal exact-head vector. -/
theorem closed_legal_power_family_bounds (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure)
    {d : ℕ} {K : Finset ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hk : ∀ k ∈ K, 2 ≤ k)
    (hh : ∀ n, 0 < n → n < d → qSequence F n = 1) :
    (qHeadEnergy d + qPowerConductance d K /
      (1 + (d : ℝ) ^ 2 * qPowerConductance d K)) / zetaTwo ≤ ‖F‖ ^ 2 ∧
    ((d : ℝ) - 1) / d + pPowerConductance d K /
      (1 + (d : ℝ) * ((d : ℝ) + 1) * pPowerConductance d K) ≤ ‖toPareto F‖ ^ 2 :=
  ⟨power_family_q_lower_bound F (legalClosure_le_radicalCompatible hF) hd hs hk hh,
   power_family_pareto_lower_bound F (legalClosure_le_radicalCompatible hF) hd hs hk hh⟩

theorem five_two_fiber_constants :
    qPowerConductance 5 {2, 3} / (1 + 25 * qPowerConductance 5 {2, 3}) =
      32202 / 38037251 ∧
    (32202 / 38037251 : ℝ) - 1 / 1226 = 1442401 / 46633669726 ∧
    (0 : ℝ) < 1442401 / 46633669726 ∧
    pPowerConductance 5 {2, 3} / (1 + 30 * pPowerConductance 5 {2, 3}) =
      13 / 16015 ∧
    (13 / 16015 : ℝ) - 1 / 1280 = 25 / 819968 ∧
    (0 : ℝ) < 25 / 819968 := by
  norm_num [qPowerConductance, pPowerConductance]

theorem head_four_two_fiber_q_bound (F : QHilbert) (hF : F ∈ radicalCompatible)
    (hh : ∀ n, 0 < n → n ≤ 4 → qSequence F n = 1) :
    (205 / 144 + 32202 / 38037251) / zetaTwo ≤ ‖F‖ ^ 2 := by
  have h := power_family_q_lower_bound F hF (d := 5) (K := {2, 3})
    (by norm_num) (by norm_num : Nat.Prime 5).squarefree
    (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega)
    (by intro n hn hn5; exact hh n hn (by omega))
  rw [head_five_certificate_constants.1] at h
  norm_num [qPowerConductance] at h ⊢
  exact h

theorem head_four_two_fiber_pareto_bound (F : QHilbert) (hF : F ∈ radicalCompatible)
    (hh : ∀ n, 0 < n → n ≤ 4 → qSequence F n = 1) :
    4 / 5 + 13 / 16015 ≤ ‖toPareto F‖ ^ 2 := by
  have h := power_family_pareto_lower_bound F hF (d := 5) (K := {2, 3})
    (by norm_num) (by norm_num : Nat.Prime 5).squarefree
    (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk; omega)
    (by intro n hn hn5; exact hh n hn (by omega))
  norm_num [pPowerConductance] at h ⊢
  exact h

end RiemannResearch.RH.SquarefreeMultiFiberEnergy
