import RiemannResearch.RH.MertensWeightedEnergy
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absolute Mertens moments from weighted square energy

Source: user-provided `Reciprocal_Residue_Density_and_Direct_RH_Agenda (1).tex`,
Section 6 and agenda Step 2. This proves the discrete Cauchy--Schwarz input
at the exact threshold sigma > 1/2 + epsilon. The downstream module
MertensEnergyRH constructs the holomorphic first-difference series and
proves zero exclusion and the direct RH implication from these energies.
-/

noncomputable section
namespace RiemannResearch.RH.MertensWeightedEnergy

/-- Weighted square energy supplies every strictly interior absolute Mellin
moment. The half-plane margin is explicit. -/
theorem summable_absolute_mertens_moment (ε σ : ℝ)
    (hE : HasFiniteEnergy ε) (hσ : 1 / 2 + ε < σ) :
    Summable (fun n : ℕ => |mertensPrefix (n + 1)| *
      ((n : ℝ) + 1) ^ (-1 - σ)) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (2 * ε - 2 * σ)) := by
    have h := Real.summable_nat_rpow.mpr (show 2 * ε - 2 * σ < -1 by linarith)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (hE.add hs)
  intro n
  let x : ℝ := (n : ℝ) + 1
  have hx : 0 < x := by dsimp [x]; positivity
  have hp (r : ℝ) : (x ^ r) ^ 2 = x ^ (2 * r) := by
    rw [pow_two, ← Real.rpow_add hx]
    congr 1
    ring
  let a := |mertensPrefix (n + 1)| * x ^ (-1 - ε)
  let b := x ^ (ε - σ)
  have ha : a ^ 2 = weight ε n * mertensPrefix (n + 1) ^ 2 := by
    dsimp [a]
    rw [mul_pow, sq_abs, hp, show 2 * (-1 - ε) = -2 - 2 * ε by ring]
    simp only [weight, x]
    ring
  have hb : b ^ 2 = x ^ (2 * ε - 2 * σ) := by
    dsimp [b]
    rw [hp, show 2 * (ε - σ) = 2 * ε - 2 * σ by ring]
  have hab : a * b = |mertensPrefix (n + 1)| * x ^ (-1 - σ) := by
    dsimp [a, b]
    rw [mul_assoc, ← Real.rpow_add hx,
      show (-1 - ε) + (ε - σ) = -1 - σ by ring]
  have hab0 : 0 ≤ a * b := by dsimp [a, b]; positivity
  have hsq := sq_nonneg (a - b)
  change |mertensPrefix (n + 1)| * x ^ (-1 - σ) ≤
    weight ε n * mertensPrefix (n + 1) ^ 2 + x ^ (2 * ε - 2 * σ)
  nlinarith [ha, hb, hab]

end RiemannResearch.RH.MertensWeightedEnergy
