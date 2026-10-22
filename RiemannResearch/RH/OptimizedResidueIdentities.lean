import RiemannResearch.RH.OptimizedResiduePackets

/-!
# Exact multiscale identities for the optimized residue packets

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md, §4.
All original generator terms are retained. The final finite averaging identity
is general algebra; its hypotheses are explicitly stated.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem dilation_residue_six_synthesis (n k : ℕ) :
    dilation n (residue 6) k = dilation n (residue 2) k +
      dilation (2 * n) (residue 3) k := by
  have h := congrArg (fun f : ℕ → ℝ => dilation n f k) residue_six_synthesis
  simpa only [dilation_add, Pi.add_apply, dilation_comp, Nat.mul_comm n 2] using h

theorem nearbyDilationPacket_residue_six (n : ℕ) :
    nearbyDilationPacket (residue 6) n =
      nearbyDilationPacket (residue 2) n + nearbyDilationPacket (residue 3) (2 * n) +
        nearbyDilationPacket (residue 3) (2 * n + 1) := by
  funext k
  simp only [nearbyDilationPacket_eq_dilation, Pi.add_apply, Pi.sub_apply]
  rw [dilation_residue_six_synthesis n k, dilation_residue_six_synthesis (n + 1) k]
  have hn : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
  rw [hn]
  ring

theorem nearbyDilationPacket_optimized_original (n : ℕ) :
    nearbyDilationPacket optimizedResidueSeed n =
      (3 / 4 : ℝ) • nearbyDilationPacket (residue 2) n +
      (1 / 2 : ℝ) • nearbyDilationPacket (residue 3) n -
      (1 / 4 : ℝ) • nearbyDilationPacket (residue 6) n := by
  funext k
  simp only [nearbyDilationPacket, optimizedResidueSeed, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem nearbyDilationPacket_optimized_multiscale (n : ℕ) :
    nearbyDilationPacket optimizedResidueSeed n =
      (1 / 2 : ℝ) • nearbyDilationPacket (residue 2) n +
      (1 / 2 : ℝ) • nearbyDilationPacket (residue 3) n -
      (1 / 4 : ℝ) • nearbyDilationPacket (residue 3) (2 * n) -
      (1 / 4 : ℝ) • nearbyDilationPacket (residue 3) (2 * n + 1) := by
  rw [nearbyDilationPacket_optimized_original, nearbyDilationPacket_residue_six]
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Exact finite averaging identity behind the sharp one-half jump bound.
For a smooth residue seed the distinguished set consists of the classes prime
to six. Establishing these hypotheses for an arbitrary conductor is separate
from this generic algebraic identity. -/
theorem jump_average_square_completion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w f : ι → ℝ) (A : ι → Prop) [DecidablePred A]
    (hw : ∑ i ∈ s, w i = 1)
    (hf : ∑ i ∈ s, w i * f i = 0)
    (hA : ∑ i ∈ s, w i * (if A i then 1 else 0) = 1 / 3)
    (hfixed : ∀ i ∈ s, A i → f i = 1) :
    (∑ i ∈ s, w i * f i ^ 2) =
      1 / 2 + ∑ i ∈ s, w i * (if A i then 0 else (f i + 1 / 2) ^ 2) := by
  have hi (i : ι) (hi : i ∈ s) :
      w i * f i ^ 2 =
        w i * (if A i then 0 else (f i + 1 / 2) ^ 2) - w i * f i -
        w i / 4 + (9 / 4) * (w i * (if A i then 1 else 0)) := by
    by_cases hai : A i
    · rw [hfixed i hi hai]
      simp [hai]
      ring
    · simp only [if_neg hai]
      ring
  calc
    _ = ∑ i ∈ s, (w i * (if A i then 0 else (f i + 1 / 2) ^ 2) - w i * f i -
        w i / 4 + (9 / 4) * (w i * (if A i then 1 else 0))) :=
      Finset.sum_congr rfl hi
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
        ← Finset.mul_sum, ← Finset.sum_mul, hw, hf, hA]
      ring

end
end RiemannResearch.RH.Pareto
