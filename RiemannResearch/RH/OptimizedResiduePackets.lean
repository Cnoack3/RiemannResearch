import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.DilationWaveletAlgebra
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# An explicit optimized two-seed residue packet

Source: user-provided argument, `RH_CRT_Packet_Research_2026-09-09.md`, §§4–6.
This module proves actual finite legal membership, exact coordinate formulas,
finite jump energies, and the exact finite substitution identity. Finite-period
jump energy is not identified with an asymptotic Pareto norm here. No uniform
global approximation estimate or RH assumption is supplied.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def optimizedResidueSeed (k : ℕ) : ℝ :=
  (3 / 4) * residue 2 k + (1 / 2) * residue 3 k - (1 / 4) * residue 6 k

def complementaryResidueSeed (k : ℕ) : ℝ := residue 2 k - optimizedResidueSeed k

theorem residue_six_synthesis : residue 6 = residue 2 + dilation 2 (residue 3) := by
  funext k
  have h := residue_mul_floor 2 3 k
  norm_num at h
  simp only [Pi.add_apply]
  linarith

theorem residue_two_legal : residue 2 ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  simpa only [dilation_one] using
    dilation_generator_mem ({2, 3} : Set ℕ) (a := 2) (m := 1) (by simp) (by omega)

theorem residue_three_legal : residue 3 ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  simpa only [dilation_one] using
    dilation_generator_mem ({2, 3} : Set ℕ) (a := 3) (m := 1) (by simp) (by omega)

theorem residue_six_legal : residue 6 ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  rw [residue_six_synthesis]
  exact (legalSeedSpan ({2, 3} : Set ℕ)).add_mem residue_two_legal
    (dilation_generator_mem ({2, 3} : Set ℕ) (a := 3) (m := 2) (by simp) (by omega))

theorem optimizedResidueSeed_legal :
    optimizedResidueSeed ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  change (3 / 4 : ℝ) • residue 2 + (1 / 2 : ℝ) • residue 3 -
    (1 / 4 : ℝ) • residue 6 ∈ legalSeedSpan ({2, 3} : Set ℕ)
  exact (legalSeedSpan ({2, 3} : Set ℕ)).sub_mem
    ((legalSeedSpan ({2, 3} : Set ℕ)).add_mem
      ((legalSeedSpan ({2, 3} : Set ℕ)).smul_mem _ residue_two_legal)
      ((legalSeedSpan ({2, 3} : Set ℕ)).smul_mem _ residue_three_legal))
    ((legalSeedSpan ({2, 3} : Set ℕ)).smul_mem _ residue_six_legal)

theorem complementaryResidueSeed_legal :
    complementaryResidueSeed ∈ legalSeedSpan ({2, 3} : Set ℕ) :=
  (legalSeedSpan ({2, 3} : Set ℕ)).sub_mem residue_two_legal optimizedResidueSeed_legal

@[simp] theorem optimizedResidueSeed_zero : optimizedResidueSeed 0 = 0 := by
  norm_num [optimizedResidueSeed, residue]
@[simp] theorem optimizedResidueSeed_one : optimizedResidueSeed 1 = 1 := by
  norm_num [optimizedResidueSeed, residue]
@[simp] theorem optimizedResidueSeed_two : optimizedResidueSeed 2 = 1 / 2 := by
  norm_num [optimizedResidueSeed, residue]
@[simp] theorem complementaryResidueSeed_zero : complementaryResidueSeed 0 = 0 := by
  norm_num [complementaryResidueSeed, optimizedResidueSeed, residue]
@[simp] theorem complementaryResidueSeed_one : complementaryResidueSeed 1 = 0 := by
  norm_num [complementaryResidueSeed, optimizedResidueSeed, residue]
@[simp] theorem complementaryResidueSeed_two : complementaryResidueSeed 2 = -(1 / 2) := by
  norm_num [complementaryResidueSeed, optimizedResidueSeed, residue]

theorem optimizedResidueSeed_mod_six (k : ℕ) :
    optimizedResidueSeed k = optimizedResidueSeed (k % 6) := by
  have h2 : k % 6 % 2 = k % 2 := by omega
  have h3 : k % 6 % 3 = k % 3 := by omega
  simp only [optimizedResidueSeed, residue, h2, h3, Nat.mod_mod]

theorem optimizedResidueSeed_periodic (k : ℕ) :
    optimizedResidueSeed (k + 6) = optimizedResidueSeed k := by
  simp [optimizedResidueSeed, residue, Nat.add_mod]

theorem complementaryResidueSeed_periodic (k : ℕ) :
    complementaryResidueSeed (k + 6) = complementaryResidueSeed k := by
  simp [complementaryResidueSeed, optimizedResidueSeed_periodic, residue, Nat.add_mod]

/-- Forward jump, so a period is indexed by 0 through 5 without a negative index. -/
def sequenceForwardJump (f : ℕ → ℝ) (k : ℕ) : ℝ := f (k + 1) - f k

theorem optimizedResidueSeed_forwardJump (k : ℕ) :
    sequenceForwardJump optimizedResidueSeed k =
      if (k + 1) % 6 = 1 ∨ (k + 1) % 6 = 5 then 1 else -(1 / 2) := by
  have hk : k % 6 < 6 := Nat.mod_lt _ (by omega)
  have hsucc : (k + 1) % 6 = (k % 6 + 1) % 6 := by omega
  unfold sequenceForwardJump
  rw [optimizedResidueSeed_mod_six (k + 1), optimizedResidueSeed_mod_six k, hsucc]
  interval_cases h : k % 6 <;> norm_num [h, optimizedResidueSeed, residue]

def sixJumpInner (f g : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range 6, sequenceForwardJump f k * sequenceForwardJump g k) / 6

theorem sixJumpInner_residue_gram :
    sixJumpInner (residue 2) (residue 2) = 1 ∧
    sixJumpInner (residue 2) (residue 3) = 0 ∧
    sixJumpInner (residue 2) (residue 6) = 1 ∧
    sixJumpInner (residue 3) (residue 3) = 2 ∧
    sixJumpInner (residue 3) (residue 6) = 2 ∧
    sixJumpInner (residue 6) (residue 6) = 5 := by
  norm_num [sixJumpInner, sequenceForwardJump, residue, Finset.sum_range_succ]

theorem sixJumpInner_optimized : sixJumpInner optimizedResidueSeed optimizedResidueSeed = 1 / 2 := by
  norm_num [sixJumpInner, sequenceForwardJump, optimizedResidueSeed, residue,
    Finset.sum_range_succ]

theorem sixJumpInner_complementary :
    sixJumpInner complementaryResidueSeed complementaryResidueSeed = 1 / 2 := by
  norm_num [sixJumpInner, sequenceForwardJump, complementaryResidueSeed,
    optimizedResidueSeed, residue, Finset.sum_range_succ]

theorem sixJumpInner_optimized_complementary :
    sixJumpInner optimizedResidueSeed complementaryResidueSeed = 0 := by
  norm_num [sixJumpInner, sequenceForwardJump, complementaryResidueSeed,
    optimizedResidueSeed, residue, Finset.sum_range_succ]

/-- Exact square completion for the original two neighboring channels. -/
theorem two_seed_jump_square_completion (a b : ℝ) (h : a + b = 1) :
    a ^ 2 + 2 * b ^ 2 = 2 / 3 + 3 * (a - 2 / 3) ^ 2 := by
  have hb : b = 1 - a := by linarith
  rw [hb]
  ring

/-- The complete three-channel quadratic form, with every cross term retained. -/
theorem three_seed_jump_square_completion (a b c : ℝ) (h : a + b + c = 1) :
    a ^ 2 + 2 * b ^ 2 + 5 * c ^ 2 + 2 * a * c + 4 * b * c =
      1 / 2 + (a + c - 1 / 2) ^ 2 + 2 * (b + c - 1 / 4) ^ 2 +
        2 * (c + 1 / 4) ^ 2 := by
  nlinarith

theorem three_seed_jump_energy_ge (a b c : ℝ) (h : a + b + c = 1) :
    1 / 2 ≤ a ^ 2 + 2 * b ^ 2 + 5 * c ^ 2 + 2 * a * c + 4 * b * c := by
  rw [three_seed_jump_square_completion a b c h]
  nlinarith [sq_nonneg (a + c - 1 / 2), sq_nonneg (b + c - 1 / 4),
    sq_nonneg (c + 1 / 4)]

/-- The exact substitution which retains the second channel. -/
theorem optimizedResidueSeed_substitution :
    (2 : ℝ) • optimizedResidueSeed - residue 2 =
      residue 3 - (1 / 2 : ℝ) • dilation 2 (residue 3) := by
  funext k
  have h := congrFun residue_six_synthesis k
  simp only [Pi.add_apply] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, optimizedResidueSeed]
  linarith

def optimizedCorrectionSequence (n : ℕ) : ℕ → ℝ :=
  -(1 / (n : ℝ)) • nearbyDilationPacket optimizedResidueSeed n

def complementaryCorrectionSequence (n : ℕ) : ℕ → ℝ :=
  -(1 / (n : ℝ)) • nearbyDilationPacket complementaryResidueSeed n

theorem optimizedCorrectionSequence_below (n k : ℕ) (hk : k < n) :
    optimizedCorrectionSequence n k = 0 := by
  simp [optimizedCorrectionSequence, nearbyDilationPacket,
    Nat.div_eq_of_lt hk, Nat.div_eq_of_lt (show k < n + 1 by omega)]

theorem optimizedCorrectionSequence_at (n : ℕ) (hn : 0 < n) :
    optimizedCorrectionSequence n n = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp [optimizedCorrectionSequence, nearbyDilationPacket, Nat.div_self hn,
    Nat.div_eq_of_lt (show n < n + 1 by omega), hn0]

theorem complementaryCorrectionSequence_through (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    complementaryCorrectionSequence n k = 0 := by
  rcases lt_or_eq_of_le hk with hk | heq
  · simp [complementaryCorrectionSequence, nearbyDilationPacket,
      Nat.div_eq_of_lt hk, Nat.div_eq_of_lt (show k < n + 1 by omega)]
  · subst k
    simp [complementaryCorrectionSequence, nearbyDilationPacket,
      Nat.div_self hn, Nat.div_eq_of_lt (show n < n + 1 by omega)]

theorem complementaryCorrectionSequence_twice (n : ℕ) (hn : 0 < n) :
    complementaryCorrectionSequence n (2 * n) = -(1 / 2) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hdiv : 2 * n / (n + 1) = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  simp [complementaryCorrectionSequence, nearbyDilationPacket, hdiv,
    Nat.mul_div_cancel, ne_of_gt hn]

end
end RiemannResearch.RH.Pareto
