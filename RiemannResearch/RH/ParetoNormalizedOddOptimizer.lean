import RiemannResearch.RH.ParetoOddMomentHeadNormalization
import RiemannResearch.RH.ParetoOddMomentParity

/-!
# Explicit normalized odd-moment optimizers

Source: continuation of the user's Pareto head-normalization handoff,
21 September 2026. The original odd-moment optimizer is orthogonal to
every even atom. Consequently changing its modulus-two coefficient has
an exact nonnegative energy cost. Capacity divergence remains Open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteGramCapacity

theorem oddMomentOptimizer_even_orthogonal (n : ℕ) (i : EvenTailIndex n) :
    inner ℝ (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (oddMomentOptimizer n)) (evenTailAtom n i) = 0 := by
  rw [oddMomentOptimizer, map_smul, real_inner_smul_left, real_inner_comm]
  change _ * inner ℝ (evenTailAtom n i) (coprimeDefectMinimum n) = 0
  rw [coprimeDefectMinimum_even_observation, mul_zero]

def normalizedOddOptimizer (n : ℕ) (hn : 2 ≤ n) : Fin n → ℝ :=
  normalizeOddHead n (by omega) (oddMomentOptimizer n)

theorem normalizedOddOptimizer_moment (n : ℕ) (hn : 2 ≤ n) :
    oddMomentValue n (normalizedOddOptimizer n hn) = 1 := by
  rw [normalizedOddOptimizer, normalizeOddHead_moment]
  exact oddMomentOptimizer_normalized n hn

theorem normalizedOddOptimizer_head (n : ℕ) (hn : 2 ≤ n) :
    oddMomentHead n (normalizedOddOptimizer n hn) = oddHeadConstant := by
  rw [normalizedOddOptimizer, normalizeOddHead_head]
  rw [show oddMomentValue n (oddMomentOptimizer n) = 1 from
    oddMomentOptimizer_normalized n hn, mul_one]

theorem normalizedOddOptimizer_energy (n : ℕ) (hn : 2 ≤ n) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (normalizedOddOptimizer n hn)‖^2 =
    oddHeadConstant^2 / coprimeDefectCapacity n +
      4 * (inner ℝ
        (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
          (oddMomentOptimizer n)) (infiniteCoprimeCertificate 2))^2 * ‖tailAtom 0‖^2 := by
  have ho := oddMomentOptimizer_even_orthogonal n
    (⟨⟨0,by omega⟩,by norm_num⟩ : EvenTailIndex n)
  change inner ℝ (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
    (oddMomentOptimizer n)) (tailAtom 0) = 0 at ho
  rw [normalizedOddOptimizer, normalizeOddHead_energy_exact, ho, mul_zero,
    sub_zero, oddMomentOptimizer_energy n hn]
  rfl

theorem normalizedOddOptimizer_energy_le (n : ℕ) (hn : 2 ≤ n) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (normalizedOddOptimizer n hn)‖^2 ≤
    (1 + 4 * ‖infiniteCoprimeCertificate 2‖^2 * ‖tailAtom 0‖^2) *
      (oddHeadConstant^2 / coprimeDefectCapacity n) := by
  have hb := real_inner_mul_inner_self_le
    (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (oddMomentOptimizer n)) (infiniteCoprimeCertificate 2)
  simp only [real_inner_self_eq_norm_sq, ← pow_two] at hb
  rw [oddMomentOptimizer_energy n hn] at hb
  change (inner ℝ _ _)^2 ≤ (oddHeadConstant^2 / coprimeDefectCapacity n) *
    ‖infiniteCoprimeCertificate 2‖^2 at hb
  rw [normalizedOddOptimizer_energy n hn]
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖tailAtom 0‖)
  nlinarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
