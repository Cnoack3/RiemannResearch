import RiemannResearch.RH.ParetoProgressionTails
import RiemannResearch.Analysis.RationalInterval
import Mathlib.Tactic

/-!
# Elementary rational intervals for complete Pareto progressions
A finite rational prefix and the proved telescoping tail bounds enclose the
entire infinite progression. No transcendental evaluation is needed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch

def elementaryProgressionInterval (P r K : ℕ) : RatInterval :=
  let t : ℚ := (r : ℚ) + P * K
  let S : ℚ := ∑ j ∈ Finset.range K,
    1 / (((r : ℚ) + P * j) * ((r : ℚ) + P * j + 1))
  ⟨S + 1 / ((P : ℚ) * t),
   S + 1 / (t * (t + 1)) + 1 / ((P : ℚ) * (t + 1))⟩

theorem elementaryProgressionInterval_contains (P r K : ℕ)
    (hP : 0 < P) (hr : 0 < r) :
    (elementaryProgressionInterval P r K).Contains (progressionWeight P r) := by
  have ht : 0 < r + P * K := by omega
  have hl := progressionWeight_lower P (r + P * K) hP ht
  have hu := progressionWeight_upper_one P (r + P * K) hP
  have he := progressionWeight_partial_split P r K hP
  unfold positiveWeight at hu he
  simp only [Nat.cast_add, Nat.cast_mul] at hl hu he
  unfold RatInterval.Contains elementaryProgressionInterval
  dsimp only
  push_cast
  constructor <;> linarith

end RiemannResearch.RH.Pareto
