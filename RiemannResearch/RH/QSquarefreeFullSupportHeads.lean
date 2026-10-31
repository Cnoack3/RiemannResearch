/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRamanujanFullSupport
import RiemannResearch.Analysis.NormalizedEnergy
import RiemannResearch.RH.QMobiusStretchedEnergy
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.QMobiusExactHead
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual squarefree full-support exact heads with sublinear energy
Source: the user's construction request, 30 October 2026.
Prime-anchored Möbius trials are perturbed by less than 1/(j+1). Every squarefree
q >= 2 is used with nonzero coefficient at every stage j >= q. This preserves
complete sublinear energy and all fixed logarithmic savings.
The stronger subpolynomial bound is not established.
-/

namespace RiemannResearch.RH.QSquarefreeFullSupportHeads
open Filter
open scoped Topology BigOperators
open ZetaTwoHilbert ZetaTwoProbability QRamanujanPackets QRamanujanFullSupport
open RiemannResearch.Analysis.NormalizedEnergy
noncomputable section
/-- Actual cofinal exact heads, all squarefree packets persistently used, with
complete sublinear energy and every fixed logarithmic saving. -/
theorem exists_sublinear_full_support_heads :
    ∃ H : ℕ → ℕ, ∃ S : ℕ → Finset ℕ, ∃ a : ℕ → ℕ → ℝ,
      Tendsto H atTop atTop ∧
      (∀ j, (H j + 1).Prime) ∧
      (∀ j q, q ∈ S j → 1 < q ∧ Squarefree q ∧ a j q ≠ 0) ∧
      (∀ q, 2 ≤ q → Squarefree q → ∀ j, q ≤ j → q ∈ S j) ∧
      (∀ j, (∑ q ∈ S j, a j q • qRamanujanPacket q) ∈ qSquarefreeCRTSpan) ∧
      (∀ j n, 0 < n → n ≤ H j →
        qSequence (∑ q ∈ S j, a j q • qRamanujanPacket q) n = 1) ∧
      Tendsto (fun j => ‖∑ q ∈ S j, a j q • qRamanujanPacket q‖ ^ 2 / (H j : ℝ))
        atTop (𝓝 0) ∧
      (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ j : ℕ in atTop,
        ‖∑ q ∈ S j, a j q • qRamanujanPacket q‖ ^ 2 ≤
          12 / zetaTwo + 2 + C * (H j : ℝ) / (6 + Real.log (H j : ℝ)) ^ k) := by
  classical
  choose p hpbound hp using fun j => Nat.exists_infinite_primes (j + 2)
  let H : ℕ → ℕ := fun j => p j - 1
  have hHpos : ∀ j, 0 < H j := by intro j; dsimp [H]; have := hpbound j; omega
  have hHp (j : ℕ) : H j + 1 = p j := by dsimp [H]; have := hpbound j; omega
  have hcofinal : Tendsto H atTop atTop :=
    tendsto_atTop_mono (fun j => by dsimp [H]; have := hpbound j; omega) tendsto_id
  let F : ℕ → QHilbert := fun j => QMobiusExactHead.exactHead (H j)
  have hlegal : ∀ j, F j ∈ qSquarefreeCRTSpan := by
    intro j
    apply QSquarefreeSublinearHeads.exactHead_mem_squarefreeSpan
    rw [hHp j]
    exact (hp j).squarefree
  obtain ⟨S, a, hcoeff, hclose, hhead, hcover⟩ :=
    full_support_sequence F hlegal H (fun j => 1 / ((j : ℝ) + 1)) (by intro j; positivity)
  let A : ℕ → QHilbert := fun j => ∑ q ∈ S j, a j q • qRamanujanPacket q
  have hdist : ∀ j, ‖A j - F j‖ ≤ 1 := by
    intro j
    have he : 1 / ((j : ℝ) + 1) ≤ (1 : ℝ) := by
      apply (div_le_one (by positivity)).mpr
      have := Nat.cast_nonneg (α := ℝ) j
      linarith
    exact (hclose j).le.trans he
  have henergy (j : ℕ) : ‖A j‖ ^ 2 ≤ 2 * ‖F j‖ ^ 2 + 2 := by
    simpa only [one_pow, mul_one] using norm_sq_le_of_dist_le (F j) (A j) 1 zero_le_one (hdist j)
  refine ⟨H, S, a, hcofinal, ?_, hcoeff, hcover, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hHp j]
    exact hp j
  · intro j
    apply Submodule.sum_mem
    intro q hq
    exact Submodule.smul_mem _ _ (packet_mem_squarefree q (hcoeff j q hq).2.1)
  · intro j n hn hnH
    rw [hhead j n hnH]
    exact QMobiusExactHead.exactHead_exact (H j) n hn hnH
  · exact sublinear_of_bounded_perturbation F A (fun j => (H j : ℝ)) 1 zero_le_one
      (tendsto_natCast_atTop_atTop.comp hcofinal) (Eventually.of_forall hdist)
      (QSquarefreeSublinearHeads.exactHead_sublinear.comp hcofinal)
  · intro k
    obtain ⟨C, hC, hbound⟩ := QMobiusStretchedEnergy.exactHead_eventual_log_power_energy k
    refine ⟨2 * C, by positivity, ?_⟩
    filter_upwards [hcofinal.eventually hbound] with j hj
    calc
      _ ≤ 2 * ‖F j‖ ^ 2 + 2 := henergy j
      _ ≤ 2 * (6 / zetaTwo + C * (H j : ℝ) /
          (6 + Real.log (H j : ℝ)) ^ k) + 2 := by dsimp [F]; linarith
      _ = _ := by ring
end
end RiemannResearch.RH.QSquarefreeFullSupportHeads
