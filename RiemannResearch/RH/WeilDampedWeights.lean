import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Damped von Mangoldt energies and a two-exponent tail estimate

Source: user-provided prime-side factorization continuation, Priority 1.
The tail argument here splits the damping exponent instead of estimating a
logarithmic tail integral. It uses absolute convergence of the von Mangoldt
Dirichlet series to the right of 1, and does not require PNT or RH.
-/

noncomputable section
open scoped BigOperators
open Classical
namespace RiemannResearch.RH.WeilDampedWeights
def energy (σ : ℝ) (m : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-2 * σ)

def amplitude (σ : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt (ArithmeticFunction.vonMangoldt m) * (m : ℝ) ^ (-σ)

theorem energy_nonneg (σ : ℝ) (m : ℕ) : 0 ≤ energy σ m :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem amplitude_nonneg (σ : ℝ) (m : ℕ) : 0 ≤ amplitude σ m := by
  unfold amplitude
  positivity

theorem amplitude_sq (σ : ℝ) (m : ℕ) : amplitude σ m ^ 2 = energy σ m := by
  unfold amplitude energy
  rw [mul_pow, Real.sq_sqrt ArithmeticFunction.vonMangoldt_nonneg,
    ← Real.rpow_two, ← Real.rpow_mul (Nat.cast_nonneg m)]
  congr 2
  ring

theorem vonMangoldt_rpow_summable {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-p)) := by
  have hs := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (p : ℂ)) (by simpa using hp)).norm
  apply hs.congr
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg, div_eq_mul_inv]

theorem energy_summable {σ : ℝ} (hσ : 1 / 2 < σ) : Summable (energy σ) := by
  have h := vonMangoldt_rpow_summable (p := 2 * σ) (by linarith)
  convert h using 1
  funext m
  unfold energy
  congr 2
  ring

def tailEnergy (σ Y : ℝ) : ℝ :=
  ∑' m : ℕ, if Y ≤ (m : ℝ) then energy σ m else 0

theorem tailEnergy_nonneg (σ Y : ℝ) : 0 ≤ tailEnergy σ Y := by
  apply tsum_nonneg
  intro m
  split_ifs <;> simp [energy_nonneg]

theorem tail_summable {σ : ℝ} (hσ : 1 / 2 < σ) (Y : ℝ) :
    Summable (fun m : ℕ => if Y ≤ (m : ℝ) then energy σ m else 0) := by
  apply Summable.of_nonneg_of_le _ _ (energy_summable hσ)
  · intro m; split_ifs <;> simp [energy_nonneg]
  · intro m; split_ifs <;> simp [energy_nonneg]

theorem energy_le_lower_exponent {σ β Y : ℝ} (hβσ : β ≤ σ)
    (hY : 0 < Y) {m : ℕ} (hm : Y ≤ (m : ℝ)) :
    energy σ m ≤ Y ^ (-2 * (σ - β)) * energy β m := by
  have hm0 : 0 < (m : ℝ) := lt_of_lt_of_le hY hm
  have hp : (m : ℝ) ^ (-2 * (σ - β)) ≤ Y ^ (-2 * (σ - β)) :=
    Real.rpow_le_rpow_of_nonpos hY hm (by linarith)
  have he : energy σ m =
      (m : ℝ) ^ (-2 * (σ - β)) * energy β m := by
    unfold energy
    rw [← mul_assoc, mul_comm ((m : ℝ) ^ _) (ArithmeticFunction.vonMangoldt m),
      mul_assoc, ← Real.rpow_add hm0]
    congr 2
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hp (energy_nonneg β m)

theorem tailEnergy_le {σ β Y : ℝ} (hβ : 1 / 2 < β) (hβσ : β ≤ σ)
    (hY : 0 < Y) :
    tailEnergy σ Y ≤ Y ^ (-2 * (σ - β)) * ∑' m, energy β m := by
  unfold tailEnergy
  calc
    _ ≤ ∑' m, Y ^ (-2 * (σ - β)) * energy β m := by
      apply Summable.tsum_le_tsum
      · intro m
        split_ifs with hm
        · exact energy_le_lower_exponent hβσ hY hm
        · exact mul_nonneg (Real.rpow_nonneg hY.le _) (energy_nonneg β m)
      · exact tail_summable (lt_of_lt_of_le hβ hβσ) Y
      · exact (energy_summable hβ).mul_left _
    _ = _ := tsum_mul_left

theorem tailEnergy_half_exponent {σ : ℝ} (hσ : 1 < σ) {Y : ℝ} (hY : 0 < Y) :
    tailEnergy σ Y ≤ Y ^ (-σ) * ∑' m, energy (σ / 2) m := by
  have ht := tailEnergy_le (σ := σ) (β := σ / 2) (by linarith) (by linarith) hY
  have he : -2 * (σ - σ / 2) = -σ := by ring
  simpa only [he] using ht

theorem prime_majorant_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(σ + 1) / 2)) := by
  simpa only [neg_div] using
    vonMangoldt_rpow_summable (p := (σ + 1) / 2) (by linarith)
end RiemannResearch.RH.WeilDampedWeights
