/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoReciprocalBound
import RiemannResearch.Analysis.ArithmeticProgressionSquareTail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Opposite-sign intervals inside the squarefree residue span

Bagchi, *On Nyman, Beurling and Báez-Duarte's Hilbert space reformulation of the
Riemann hypothesis*, Remark 8 (https://arxiv.org/abs/math/0607733), motivates the
squarefree dictionary. The four-atom pulse and its block calculations below
are elementary residue calculations for testing the scope of bounds on this span.
-/

noncomputable section
namespace RiemannResearch.RH.SquarefreeHarmonicPulse

open ArithmeticCumulative ZetaTwoHilbert ZetaTwoProbability

def parityBlock (m : ℕ) : QHilbert :=
  (2 : ℝ) • qResidue (m * 2) - qResidue m

def pulse (p : ℕ) : QHilbert := parityBlock p - parityBlock (p * 3)

private theorem physical_sub (f g : QHilbert) (n : ℕ) :
    qSequence (f - g) n = qSequence f n - qSequence g n :=
  congrFun (qSequenceLinear.map_sub f g) n

private theorem physical_smul (a : ℝ) (f : QHilbert) (n : ℕ) :
    qSequence (a • f) n = a * qSequence f n :=
  congrFun (qSequenceLinear.map_smul a f) n

theorem parityBlock_value {m : ℕ} (hm : 0 < m) (n : ℕ) :
    qSequence (parityBlock m) n = ((n / m % 2 : ℕ) : ℝ) := by
  simp only [parityBlock, physical_sub, physical_smul, qSequence_qResidue, residueFraction]
  rw [Nat.mod_mul (a := m) (b := 2) (x := n)]
  push_cast
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp [hm']
  ring

theorem pulse_value {p : ℕ} (hp : 0 < p) (n : ℕ) :
    qSequence (pulse p) n =
      ((n / p % 2 : ℕ) : ℝ) - ((n / p / 3 % 2 : ℕ) : ℝ) := by
  rw [pulse, physical_sub, parityBlock_value hp, parityBlock_value (by omega : 0 < p * 3),
    Nat.div_div_eq_div_mul]

theorem pulse_zero_before {p n : ℕ} (hn : n < p) :
    qSequence (pulse p) n = 0 := by
  rw [pulse_value (by omega), Nat.div_eq_of_lt hn]
  norm_num

theorem pulse_positive_block {p n : ℕ} (hlo : p ≤ n) (hhi : n < 2 * p) :
    qSequence (pulse p) n = 1 := by
  have hq : n / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [pulse_value (by omega), hq]
  norm_num

theorem pulse_negative_block {p n : ℕ} (hlo : 4 * p ≤ n) (hhi : n < 5 * p) :
    qSequence (pulse p) n = -1 := by
  have hq : n / p = 4 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [pulse_value (by omega), hq]
  norm_num

theorem pulse_abs_le_one {p : ℕ} (hp : 0 < p) (n : ℕ) :
    |qSequence (pulse p) n| ≤ 1 := by
  have h₁ : n / p % 2 = 0 ∨ n / p % 2 = 1 := by omega
  have h₂ : n / p / 3 % 2 = 0 ∨ n / p / 3 % 2 = 1 := by omega
  rw [pulse_value hp]
  rcases h₁ with h|h <;> rcases h₂ with k|k <;> rw [h, k] <;> norm_num

private theorem legal_residue {m : ℕ} (hm : 2 ≤ m) (hs : Squarefree m) :
    qResidue m ∈ qSquarefreeCRTSpan :=
  Submodule.subset_span ⟨⟨m, hm, hs⟩, rfl⟩

theorem pulse_mem_squarefree_span {p : ℕ} (hp : p.Prime) (hs : 6 < p) :
    pulse p ∈ qSquarefreeCRTSpan := by
  have hprod {k : ℕ} (hk : 0 < k) (hk' : k < p) (hsk : Squarefree k) :
      Squarefree (p * k) :=
    (Nat.squarefree_mul (Nat.coprime_of_lt_prime hk.ne' hk' hp)).2 ⟨hp.squarefree, hsk⟩
  have h₂ := legal_residue (show 2 ≤ p * 2 by omega)
    (hprod (k := 2) (by decide) (by omega) Nat.prime_two.squarefree)
  have h₃ := legal_residue (show 2 ≤ p * 3 by omega)
    (hprod (k := 3) (by decide) (by omega) Nat.prime_three.squarefree)
  have h₆ := legal_residue (show 2 ≤ p * 6 by omega)
    (hprod (k := 6) (by decide) (by omega)
      ((Nat.squarefree_mul (show Nat.Coprime 2 3 by decide)).2
        ⟨Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩))
  unfold pulse parityBlock
  rw [Nat.mul_assoc p 3 2]
  exact qSquarefreeCRTSpan.sub_mem
    (qSquarefreeCRTSpan.sub_mem (qSquarefreeCRTSpan.smul_mem _ h₂)
      (legal_residue (by omega) hp.squarefree))
    (qSquarefreeCRTSpan.sub_mem (qSquarefreeCRTSpan.smul_mem _ h₆) h₃)

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoReciprocalBound
open RiemannResearch.Analysis.ArithmeticProgressionSquareTail

theorem pulse_norm_sq_le {p : ℕ} (hp : 2 ≤ p) :
    zetaTwo * ‖pulse p‖ ^ 2 ≤ 1 / ((p : ℝ) - 1) := by
  have hhead : ∑ k ∈ Finset.range p, rawSquare (pulse p) k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [rawSquare, pulse_zero_before (Finset.mem_range.mp hk)]
  have hcut := (rawSquare_summable (pulse p)).sum_add_tsum_nat_add p
  rw [hhead, zero_add] at hcut
  rw [← rawSquare_tsum, ← hcut]
  have hs : Summable (fun k : ℕ => rawSquare (pulse p) (k + p)) :=
    (summable_nat_add_iff p).mpr (rawSquare_summable (pulse p))
  apply le_of_tendsto hs.hasSum.tendsto_sum_nat
  apply Filter.Eventually.of_forall
  intro M
  have ha : 0 < (p : ℝ) - 1 := by
    apply sub_pos.mpr
    exact_mod_cast (show 1 < p by omega)
  calc
    _ ≤ ∑ k ∈ Finset.range M, 1 / (((p : ℝ) - 1) + ((k + 1 : ℕ) : ℝ) * 1)^2 := by
      apply Finset.sum_le_sum
      intro k _
      have hden : ((p : ℝ) - 1) + ((k + 1 : ℕ) : ℝ) * 1 = ((k + p : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hden, rawSquare]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have h := pulse_abs_le_one (by omega : 0 < p) (k + p)
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) h 2
    _ ≤ _ := by simpa only [one_mul] using finite_tail_bound _ 1 ha zero_lt_one M

end RiemannResearch.RH.SquarefreeHarmonicPulse
