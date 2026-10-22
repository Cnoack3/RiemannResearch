import RiemannResearch.RH.RoughDiagonalLimit
import RiemannResearch.NumberTheory.SquarefreeEulerSeries

/-!
# Exact evaluation of the mandatory component diagonal growth

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 8, equation (40). This identifies the unconditional series limit
with its explicit positive constant, without a conditional provider.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators Topology
open Filter

noncomputable section

theorem roughDiagonalSeries_eq : roughDiagonalSeries = 6 / (5 * Real.pi ^ 2) := by
  have hs := RiemannResearch.NumberTheory.hasSum_squarefree_coprime_six.mul_left ((1 : ℝ) / 9)
  have hf (q : ℕ) :
      (1 : ℝ) / 9 * (if Nat.Coprime q 6 then
        (ArithmeticFunction.moebius q : ℝ) ^ 2 / (q : ℝ) ^ 2 else 0) =
      (if 0 < q ∧ Nat.Coprime q 6 then
        (ArithmeticFunction.moebius q : ℝ) ^ 2 / (9 * (q : ℝ) ^ 2) else 0) := by
    by_cases hq : q = 0
    · simp [hq]
    · have hp := Nat.pos_of_ne_zero hq
      by_cases hc : Nat.Coprime q 6 <;> simp [hc, hp] <;> field_simp <;> ring
  simp_rw [hf] at hs
  have he := hs.tsum_eq
  change roughDiagonalSeries = _ at he
  rw [he]
  ring

/-- The concrete asymptotic coefficient from equation (40). -/
theorem roughDiagonalHead_div_tendsto_explicit :
    Tendsto (fun N : ℕ => roughDiagonalHead N / (N : ℝ)) atTop
      (𝓝 (6 / (5 * Real.pi ^ 2))) := by
  simpa only [roughDiagonalSeries_eq] using roughDiagonalHead_div_tendsto

end
end RiemannResearch.RH.Pareto
