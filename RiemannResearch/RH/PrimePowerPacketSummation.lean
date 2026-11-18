import RiemannResearch.RH.IntegratedRamanujanMarkedArithmetic
import Mathlib.Tactic.Ring

/-!
# Summation along a single prime-power tower

Section 3 of Christian Noack's *The categorical CRT of atoms and carries* uses
the difference of successive residues for the integrated Ramanujan packet.
The equal-weight sum recovers the largest residue. Summation by parts retains
the last coefficient and each successive coefficient difference.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Summing the integrated packets at one prime recovers the highest residue. -/
theorem sum_ramanujanPacket_prime_powers (p j n : ℕ) (hp : p.Prime) :
    (∑ i ∈ Finset.range j, ramanujanPacket (p ^ (i + 1)) n) = residue (p ^ j) n := by
  induction j with
  | zero => simp [residue, Nat.mod_one]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, ramanujanPacket_prime_pow_succ p j hp, residue_mul_floor,
      ← pow_succ]
    ring

/-- Summation by parts on an arbitrary weighted prime tower, with its upper endpoint. -/
theorem weighted_sum_ramanujanPacket_prime_powers (p a n : ℕ) (hp : p.Prime) (c : ℕ → ℝ) :
    (∑ j ∈ Finset.range (a + 1), c j * ramanujanPacket (p ^ (j + 1)) n) =
      c a * residue (p ^ (a + 1)) n +
        ∑ j ∈ Finset.range a, (c j - c (j + 1)) * residue (p ^ (j + 1)) n := by
  induction a with
  | zero => simp [ramanujanPacket_prime_eq_residue p hp]
  | succ a ih =>
    rw [Finset.sum_range_succ (fun j => c j * ramanujanPacket (p ^ (j + 1)) n) (a + 1), ih,
      Finset.sum_range_succ (fun j => (c j - c (j + 1)) * residue (p ^ (j + 1)) n) a,
      ramanujanPacket_prime_pow_succ p (a + 1) hp, residue_mul_floor, ← pow_succ]
    ring

end RiemannResearch.RH.Pareto
