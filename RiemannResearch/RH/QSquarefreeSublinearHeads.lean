/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.CanonicalMobiusPNT
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.ParetoSublinearResidualTail
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Squarefree exact heads with unconditionally sublinear complete Q error

Source: the user's sparse power-cost research request, 17 October 2026.
The proof combines the established PNT-based canonical Mobius energy theorem
with the complete Q/P norm comparison. Choosing a prime anchor makes every
nonzero conductor squarefree. No RH assumption or uniform primitive bound is used.

The result supplies arbitrarily cheap exponent-one heads. It does not supply
the positive exponents below one required by the open sparse power-cost provider.
Bhaskar Bagchi, "On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation
of the Riemann hypothesis", Remark 8, https://arxiv.org/abs/math/0607733,
supports the external RH relevance of squarefree constant closure.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeSublinearHeads
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer Pareto

theorem exactHead_mem_squarefreeSpan (N : ℕ) (hsf : Squarefree (N + 1)) :
    QMobiusExactHead.exactHead N ∈ qSquarefreeCRTSpan := by
  have hres (d : ℕ) (hd : 0 < d) (hs : Squarefree d) :
      qResidue d ∈ qSquarefreeCRTSpan := by
    by_cases h1 : d = 1
    · rw [h1, qResidue_one]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨d, by omega, hs⟩, rfl⟩
  unfold QMobiusExactHead.exactHead
  apply Submodule.add_mem
  · apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro d hd
    by_cases hs : Squarefree d
    · exact Submodule.smul_mem _ _ (hres d (Finset.mem_Icc.mp hd).1 hs)
    · have hm : ArithmeticFunction.moebius d = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
      simp only [hm, Int.cast_zero, zero_smul]
      exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (hres (N + 1) (by omega) hsf)

theorem toPareto_exactHead (N : ℕ) :
    toPareto (QMobiusExactHead.exactHead N) = canonicalMobiusHilbert N := by
  apply hilbertSequence_injective
  rw [toPareto_sequence, QMobiusExactHead.exactHead_sequence,
    canonicalMobiusHilbert_sequence]

theorem exactHead_sublinear :
    Tendsto (fun N => ‖QMobiusExactHead.exactHead N‖ ^ 2 / (N : ℝ))
      atTop (𝓝 0) := by
  have hupper := canonicalMobiusHilbert_sublinear.const_mul (2 / zetaTwo)
  have heq : (2 / zetaTwo) * (0 : ℝ) = 0 := mul_zero _
  rw [heq] at hupper
  apply squeeze_zero (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) ?_ hupper
  intro N
  have he := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (QMobiusExactHead.exactHead N)
  rw [toPareto_exactHead] at he
  have hle : ‖QMobiusExactHead.exactHead N‖ ^ 2 ≤
      (2 / zetaTwo) * ‖canonicalMobiusHilbert N‖ ^ 2 := by
    calc
      _ ≤ (2 * ‖canonicalMobiusHilbert N‖ ^ 2) / zetaTwo :=
        (le_div_iff₀ zetaTwo_pos).mpr (by nlinarith)
      _ = _ := by ring
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hle (Nat.cast_nonneg N)

theorem exactHead_error_sublinear :
    Tendsto (fun N => ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 / (N : ℝ))
      atTop (𝓝 0) := by
  have hupper := (error_energy_div_tendsto_zero_of_energy
    canonicalMobiusHilbert canonicalMobiusHilbert_sublinear).const_mul (2 / zetaTwo)
  simp only [mul_zero] at hupper
  apply squeeze_zero (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) ?_ hupper
  intro N
  have he := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
    (qOne - QMobiusExactHead.exactHead N)
  have hmap : toPareto (qOne - QMobiusExactHead.exactHead N) =
      hilbertOne - canonicalMobiusHilbert N := by
    change toParetoLinear (qOne - QMobiusExactHead.exactHead N) = _
    rw [map_sub]
    change toPareto qOne - toPareto (QMobiusExactHead.exactHead N) = _
    rw [toPareto_qOne, toPareto_exactHead]
  rw [hmap] at he
  have hle : ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 ≤
      (2 / zetaTwo) * ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 := by
    calc
      _ ≤ (2 * ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2) / zetaTwo :=
        (le_div_iff₀ zetaTwo_pos).mpr (by nlinarith)
      _ = _ := by ring
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hle (Nat.cast_nonneg N)

/-- Unconditional exponent-one case of the sparse power-cost assertion. -/
theorem arbitrarily_small_linear_cost (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∃ (p : ℕ) (F : QHilbert), Nat.Prime p ∧ 1 ≤ p ∧ N ≤ p ∧
      F ∈ qSquarefreeCRTSpan ∧
      (∀ k, 0 < k → k < p → qSequence F k = 1) ∧
        ‖qOne - F‖ ^ 2 < c * (p : ℝ) := by
  have hev : ∀ᶠ m : ℕ in atTop,
      ‖qOne - QMobiusExactHead.exactHead m‖ ^ 2 / (m : ℝ) < c :=
    exactHead_error_sublinear.eventually (gt_mem_nhds hc)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  obtain ⟨p, hpbound, hp⟩ := Nat.exists_infinite_primes (max K N + 2)
  have hp1 : 1 ≤ p := by omega
  have he : (p - 1) + 1 = p := by omega
  have hsf : Squarefree ((p - 1) + 1) := by
    rw [he]
    exact hp.squarefree
  refine ⟨p, QMobiusExactHead.exactHead (p - 1), hp, hp1, by omega,
    exactHead_mem_squarefreeSpan (p - 1) hsf, ?_, ?_⟩
  · intro k hk hkp
    exact QMobiusExactHead.exactHead_exact (p - 1) k hk (by omega)
  · have hmpos : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (by omega : 0 < p - 1)
    have hlt := (div_lt_iff₀ hmpos).mp (hK (p - 1) (by omega))
    exact hlt.trans_le (mul_le_mul_of_nonneg_left
      (by exact_mod_cast (Nat.sub_le p 1) : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ)) hc.le)

end RiemannResearch.RH.QSquarefreeSublinearHeads
