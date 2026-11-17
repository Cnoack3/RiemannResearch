import RiemannResearch.RH.ParetoRationalWeightIntervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Nested complete Pareto weight intervals with explicit widths

Source: exact rational algebra applied to the proved telescoping progression
enclosures. Endpoint gains, losses and widths are identities before they are
bounded. The inverse-square rate is uniform in the positive residue.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Exact width of the complete rational progression enclosure. -/
theorem elementaryProgressionInterval_width (P r K : ℕ) (hP : 0 < P) (hr : 0 < r) :
    (elementaryProgressionInterval P r K).hi - (elementaryProgressionInterval P r K).lo =
      ((P : ℚ)-1) / ((P : ℚ) * ((r : ℚ)+P*K) * ((r : ℚ)+P*K+1)) := by
  have hp : (0 : ℚ) < P := by exact_mod_cast hP
  have hrr : (0 : ℚ) < r := by exact_mod_cast hr
  have ht : (0 : ℚ) < (r : ℚ)+P*K := by positivity
  have ht1 : (0 : ℚ) < (r : ℚ)+P*K+1 := by positivity
  dsimp [elementaryProgressionInterval]
  field_simp
  ring

/-- Exact gain of the lower endpoint after one more finite progression term. -/
theorem elementaryProgressionInterval_lower_step (P r K : ℕ) (hP : 0 < P) (hr : 0 < r) :
    (elementaryProgressionInterval P r (K+1)).lo - (elementaryProgressionInterval P r K).lo =
      ((P : ℚ)-1) /
        (((r : ℚ)+P*K) * ((r : ℚ)+P*K+1) * ((r : ℚ)+P*K+P)) := by
  have hp : (0 : ℚ) < P := by exact_mod_cast hP
  have hrr : (0 : ℚ) < r := by exact_mod_cast hr
  have ht : (0 : ℚ) < (r : ℚ)+P*K := by positivity
  have ht1 : (0 : ℚ) < (r : ℚ)+P*K+1 := by positivity
  have htP : (0 : ℚ) < (r : ℚ)+P*K+P := by positivity
  dsimp [elementaryProgressionInterval]
  rw [Finset.sum_range_succ]
  push_cast
  have he : (r : ℚ)+P*(K+1) = (r : ℚ)+P*K+P := by ring
  rw [he]
  field_simp
  <;> ring

/-- Exact decrease of the upper endpoint after one more finite progression term. -/
theorem elementaryProgressionInterval_upper_step (P r K : ℕ) (hP : 0 < P) (hr : 0 < r) :
    (elementaryProgressionInterval P r K).hi - (elementaryProgressionInterval P r (K+1)).hi =
      ((P : ℚ)-1) /
        (((r : ℚ)+P*K+1) * ((r : ℚ)+P*K+P) * ((r : ℚ)+P*K+P+1)) := by
  have hp : (0 : ℚ) < P := by exact_mod_cast hP
  have hrr : (0 : ℚ) < r := by exact_mod_cast hr
  have ht : (0 : ℚ) < (r : ℚ)+P*K := by positivity
  have ht1 : (0 : ℚ) < (r : ℚ)+P*K+1 := by positivity
  have htP : (0 : ℚ) < (r : ℚ)+P*K+P := by positivity
  have htP1 : (0 : ℚ) < (r : ℚ)+P*K+P+1 := by positivity
  dsimp [elementaryProgressionInterval]
  rw [Finset.sum_range_succ]
  push_cast
  have he : (r : ℚ)+P*(K+1) = (r : ℚ)+P*K+P := by ring
  rw [he]
  field_simp
  <;> ring

theorem elementaryProgressionInterval_lower_mono (P r : ℕ) (hP : 0 < P) (hr : 0 < r) :
    Monotone (fun K => (elementaryProgressionInterval P r K).lo) := by
  apply monotone_nat_of_le_succ
  intro K
  apply sub_nonneg.mp
  rw [elementaryProgressionInterval_lower_step P r K hP hr]
  have hp : (1 : ℚ) ≤ P := by exact_mod_cast hP
  positivity

theorem elementaryProgressionInterval_upper_antitone (P r : ℕ)
    (hP : 0 < P) (hr : 0 < r) :
    Antitone (fun K => (elementaryProgressionInterval P r K).hi) := by
  apply antitone_nat_of_succ_le
  intro K
  apply sub_nonneg.mp
  rw [elementaryProgressionInterval_upper_step P r K hP hr]
  have hp : (1 : ℚ) ≤ P := by exact_mod_cast hP
  positivity

/-- A uniform inverse-square width, with explicit period and prefix-length dependence. -/
theorem elementaryProgressionInterval_width_le (P r K : ℕ)
    (hP : 0 < P) (hr : 0 < r) (hK : 0 < K) :
    (elementaryProgressionInterval P r K).hi - (elementaryProgressionInterval P r K).lo ≤
      1 / (((P : ℚ)*K)^2) := by
  rw [elementaryProgressionInterval_width P r K hP hr]
  have hp : (0 : ℚ) < P := by exact_mod_cast hP
  have hrr : (0 : ℚ) < r := by exact_mod_cast hr
  have hk : (0 : ℚ) < K := by exact_mod_cast hK
  let t : ℚ := (r : ℚ)+P*K
  have ht : 0 < t := by dsimp [t]; positivity
  have hpk : 0 < (P : ℚ)*K := mul_pos hp hk
  calc
    ((P : ℚ)-1) / ((P : ℚ)*t*(t+1)) ≤ 1/t^2 := by
      apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos ht)).mpr
      nlinarith [sq_nonneg t, mul_nonneg hp.le ht.le]
    _ ≤ _ := by
      apply one_div_le_one_div_of_le (sq_pos_of_pos hpk)
      have hpt : (P : ℚ)*K ≤ t := by dsimp [t]; linarith
      nlinarith

/-- Each complete weight lies within the same explicit real error of either endpoint. -/
theorem progressionWeight_endpoint_errors (P r K : ℕ)
    (hP : 0 < P) (hr : 0 < r) (hK : 0 < K) :
    0 ≤ progressionWeight P r - ((elementaryProgressionInterval P r K).lo : ℝ) ∧
    progressionWeight P r - ((elementaryProgressionInterval P r K).lo : ℝ) ≤
      1 / (((P : ℝ)*K)^2) ∧
    0 ≤ ((elementaryProgressionInterval P r K).hi : ℝ) - progressionWeight P r ∧
    ((elementaryProgressionInterval P r K).hi : ℝ) - progressionWeight P r ≤
      1 / (((P : ℝ)*K)^2) := by
  have hw := elementaryProgressionInterval_contains P r K hP hr
  have he : ((elementaryProgressionInterval P r K).hi : ℝ) -
      ((elementaryProgressionInterval P r K).lo : ℝ) ≤ 1 / (((P : ℝ)*K)^2) := by
    have h := (Rat.cast_le (K := ℝ)).2
      (elementaryProgressionInterval_width_le P r K hP hr hK)
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
      Rat.cast_mul, Rat.cast_natCast] using h
  exact ⟨sub_nonneg.mpr hw.1, by linarith [hw.2],
    sub_nonneg.mpr hw.2, by linarith [hw.1]⟩

end RiemannResearch.RH.Pareto
