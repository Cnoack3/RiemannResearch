import RiemannResearch.RH.RawMobiusSignedGramEnergy
import RiemannResearch.RH.RawMobiusBudgetZeroFree
/-!
# Signed Gram moving-exponent reductions

Source: user's centered far-tail/subpower handoff (2026-09-24).
Proofs assemble local checked signed-Gram/Mellin results.
Literature context: Baez-Duarte, arXiv:math/0202141, Corollary 3.1 and
following paragraph (https://arxiv.org/abs/math/0202141), discusses
separate subsequences for damped approximations. This is motivation only,
not an assumed theorem or identification with the signed-Gram statements.
All arithmetic upper estimates below remain explicit open hypotheses.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto

theorem zeta_ne_zero_of_frequently_raw_offDiagonal_power
    (α : ℝ) (hα : 0 < α) (C : ℝ)
    (hC : ∃ᶠ N : ℕ in atTop,
      rawMobiusOffDiagonalEnergy N ≤ C * ((N : ℝ) + 1) ^ α)
    (s : ℂ) (hs : (1 + α) / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  obtain ⟨D, hD⟩ :=
    (frequently_power_rawMobiusBudget_iff_offDiagonal α hα).mpr ⟨C, hC⟩
  exact zeta_ne_zero_of_frequently_raw_square_budget_power α hα.le D hD s hs hs1

theorem riemannHypothesis_of_raw_offDiagonal_exponents_tendsto_zero
    (α : ℕ → ℝ)
    (hlim : Tendsto α atTop (𝓝 0))
    (hbound : ∀ j, ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
      rawMobiusOffDiagonalEnergy N ≤ C * ((N : ℝ) + 1) ^ (α j)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_subpower_raw_offDiagonal
  intro ε hε
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨C, hC⟩ := hbound j
  refine ⟨|C|, hC.mono ?_⟩
  intro N hN
  calc
    rawMobiusOffDiagonalEnergy N ≤ C * ((N : ℝ) + 1) ^ (α j) := hN
    _ ≤ |C| * ((N : ℝ) + 1) ^ (α j) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _)
    _ ≤ |C| * ((N : ℝ) + 1) ^ ε :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le
          (by linarith [Nat.cast_nonneg (α := ℝ) N]) hj.le) (abs_nonneg C)

theorem riemannHypothesis_of_raw_offDiagonal_moving_exponent
    (α : ℕ → ℝ) (hlim : Tendsto α atTop (𝓝 0)) (C : ℝ)
    (hbound : ∃ᶠ N : ℕ in atTop,
      rawMobiusOffDiagonalEnergy N ≤ C * ((N : ℝ) + 1) ^ (α N)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_subpower_raw_offDiagonal
  intro ε hε
  refine ⟨|C|, (hbound.and_eventually
    (hlim.eventually (gt_mem_nhds hε))).mono ?_⟩
  intro N hN
  calc
    rawMobiusOffDiagonalEnergy N ≤ C * ((N : ℝ) + 1) ^ (α N) := hN.1
    _ ≤ |C| * ((N : ℝ) + 1) ^ (α N) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _)
    _ ≤ |C| * ((N : ℝ) + 1) ^ ε :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le
          (by linarith [Nat.cast_nonneg (α := ℝ) N]) hN.2.le) (abs_nonneg C)

end RiemannResearch.RH.Pareto
