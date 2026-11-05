/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.SquarefreeHarmonicPulse
import RiemannResearch.RH.QResolventHarmonicPrefix
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Prefix obstruction and the residual block equations

The four-atom pulse, in the squarefree dictionary of Bagchi (2006, Remark 8),
both tests the size of harmonic prefixes and gives an explicit family of
exact balance equations for the actual orthogonal residual and witness.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.SquarefreeHarmonicPulse
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QSquarefreeDisplacementRigidity

theorem pulse_value_mod_six {p : ℕ} (hp : 0 < p) (n : ℕ) :
    qSequence (pulse p) n =
      (if n / p % 6 = 1 then (1 : ℝ) else 0) -
      (if n / p % 6 = 4 then (1 : ℝ) else 0) := by
  rw [pulse_value hp]
  have h₁ : n / p % 2 = (n / p % 6) % 2 := by omega
  have h₂ : n / p / 3 % 2 = (n / p % 6) / 3 := by omega
  rw [h₁, h₂]
  have h : n / p % 6 = 0 ∨ n / p % 6 = 1 ∨ n / p % 6 = 2 ∨
      n / p % 6 = 3 ∨ n / p % 6 = 4 ∨ n / p % 6 = 5 := by omega
  rcases h with h|h|h|h|h|h <;> rw [h] <;> norm_num

theorem minimumHarmonicPrefix_pulse_lower {p : ℕ} (hp : 0 < p) :
    1 / 5 ≤ minimumHarmonicPrefixOf (pulse p) (5 * p) := by
  have block (a : ℕ) (ha : 1 ≤ a) (hb : a + p ≤ 5 * p) (ε : ℝ)
      (he : ∀ n ∈ Finset.Ico a (a + p), ε * qSequence (pulse p) n = 1) :
      1 / 5 ≤ harmonicSideOf (pulse p) ε (5 * p) := by
    let I := Finset.Ico a (a + p)
    have hcard : I.card = p := by simp [I]
    have hsub : I ⊆ Finset.range (5 * p + 1) := by
      intro n hn
      have hhi := (Finset.mem_Ico.mp hn).2
      exact Finset.mem_range.mpr (by omega)
    calc
      (1 : ℝ) / 5 = ∑ n ∈ I, 1 / (5 * (p : ℝ)) := by
        simp only [Finset.sum_const, hcard, nsmul_eq_mul]
        field_simp [Nat.cast_ne_zero.mpr hp.ne']
      _ ≤ ∑ n ∈ I, max (ε * qSequence (pulse p) n) 0 / (n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        rw [he n hn, max_eq_left zero_le_one]
        have hlo := (Finset.mem_Ico.mp hn).1
        have hhi := (Finset.mem_Ico.mp hn).2
        apply one_div_le_one_div_of_le
        · exact_mod_cast (show 0 < n by omega)
        · exact_mod_cast (show n ≤ 5 * p by omega)
      _ ≤ harmonicSideOf (pulse p) ε (5 * p) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg n))
  apply le_min
  · apply block p (by omega) (by omega) 1
    intro n hn
    obtain ⟨hl, hh⟩ := Finset.mem_Ico.mp hn
    simp [pulse_positive_block hl (by omega)]
  · apply block (4 * p) (by omega) (by omega) (-1)
    intro n hn
    obtain ⟨hl, hh⟩ := Finset.mem_Ico.mp hn
    simp [pulse_negative_block hl (by omega)]

/-- Weighted restriction to one of the six intervals in each period of length 6p. -/
def blockMean (f : QHilbert) (p r : ℕ) : ℝ :=
  ∑' n : ℕ, if n / p % 6 = r then positiveQWeight n * qSequence f n else 0

theorem inner_pulse_eq_blockMean_sub (f : QHilbert) {p : ℕ} (hp : 0 < p) :
    inner ℝ f (pulse p) = blockMean f p 1 - blockMean f p 4 := by
  classical
  let F (n : ℕ) := positiveQWeight n * qSequence f n
  have hF : Summable F := by
    apply (qSequence_product_summable f qOne).congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [F]
    · simp [F, qSequence_qOne, qOneSequence, hn]
  have hside (r : ℕ) : Summable (fun n => if n / p % 6 = r then F n else 0) := by
    apply (hF.indicator {n | n / p % 6 = r}).congr
    intro n
    by_cases h : n / p % 6 = r <;> simp [Set.indicator, h]
  rw [qInner_weighted]
  change _ = (∑' n, (if n / p % 6 = 1 then F n else 0)) -
    (∑' n, (if n / p % 6 = 4 then F n else 0))
  rw [← (hside 1).tsum_sub (hside 4)]
  apply tsum_congr
  intro n
  rw [pulse_value_mod_six hp]
  by_cases h₁ : n / p % 6 = 1 <;> by_cases h₄ : n / p % 6 = 4 <;> simp [F, h₁, h₄]

theorem blockMean_eq_of_orthogonal {f : QHilbert} (hf : f ∈ closureᗮ)
    {p : ℕ} (hp : p.Prime) (hlarge : 6 < p) :
    blockMean f p 1 = blockMean f p 4 := by
  have hm : pulse p ∈ closure := by
    rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
    exact qSquarefreeCRTSpan.le_topologicalClosure (pulse_mem_squarefree_span hp hlarge)
  have h := Submodule.inner_right_of_mem_orthogonal hm hf
  rw [real_inner_comm, inner_pulse_eq_blockMean_sub f hp.pos] at h
  exact sub_eq_zero.mp h

theorem witness_blockMean_eq {p : ℕ} (hp : p.Prime) (hs : 6 < p) :
    blockMean witness p 1 = blockMean witness p 4 :=
  blockMean_eq_of_orthogonal witness_mem_orthogonal hp hs

theorem limitingResidual_blockMean_eq {p : ℕ} (hp : p.Prime) (hs : 6 < p) :
    blockMean limitingResidual p 1 = blockMean limitingResidual p 4 :=
  blockMean_eq_of_orthogonal (Submodule.sub_starProjection_mem_orthogonal qOne) hp hs

/-- The Lipschitz factor has square-root scale even on legal four-atom trials.
This squared form avoids rounding and any choice of reciprocal norm. -/
theorem pulse_prefix_condition_number {p : ℕ} (hp : 2 ≤ p) :
    zetaTwo * ((p : ℝ) - 1) * ‖pulse p‖ ^ 2 ≤
      25 * minimumHarmonicPrefixOf (pulse p) (5 * p) ^ 2 := by
  have hpos : 0 < (p : ℝ) - 1 := by
    apply sub_pos.mpr
    exact_mod_cast (show 1 < p by omega)
  have hnorm := (le_div_iff₀ hpos).mp (pulse_norm_sq_le hp)
  have hmass := minimumHarmonicPrefix_pulse_lower (by omega : 0 < p)
  have hmass2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 5) hmass 2
  nlinarith

end RiemannResearch.RH.SquarefreeHarmonicPulse
