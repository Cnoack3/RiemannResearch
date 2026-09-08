import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The actual Pareto law induced by a uniform variable

Source: the user-provided Pareto--Nyman argument, September 2026.
This module derives the distribution from Lebesgue measure on `(0,1]`.
It does not assume the discrete weights or an RH-equivalent density theorem.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace RiemannResearch.RH.Pareto
noncomputable section

def uniformUnit : Measure ℝ := volume.restrict (Ioc 0 1)

def reciprocalFloor (u : ℝ) : ℕ := ⌊1 / u⌋₊

theorem reciprocalFloor_measurable : Measurable reciprocalFloor := by
  exact (measurable_const.div measurable_id).nat_floor

theorem uniformUnit_univ : uniformUnit univ = 1 := by
  simp [uniformUnit, Real.volume_Ioc]

instance uniformUnit_isProbabilityMeasure : IsProbabilityMeasure uniformUnit :=
  ⟨uniformUnit_univ⟩

/-- The endpoint convention is exact, including `u = 1/k`. -/
theorem reciprocalFloor_fiber (k : ℕ) (hk : 0 < k) :
    {u : ℝ | reciprocalFloor u = k} ∩ Ioc 0 1 =
      Ioc (1 / ((k : ℝ) + 1)) (1 / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hone : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_of_lt hk)
  ext u
  simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioc]
  constructor
  · rintro ⟨hf, hu, hu1⟩
    have hb := (Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ 1 / u)).mp hf
    constructor
    · apply (div_lt_iff₀ hk1).mpr
      have h := (div_lt_iff₀ hu).mp hb.2
      nlinarith
    · apply (le_div_iff₀ hkR).mpr
      have h := (le_div_iff₀ hu).mp hb.1
      nlinarith
  · rintro ⟨hlo, hhi⟩
    have hu : 0 < u := lt_trans (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)) hlo
    constructor
    · apply (Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ 1 / u)).mpr
      constructor
      · apply (le_div_iff₀ hu).mpr
        have h := (le_div_iff₀ hkR).mp hhi
        nlinarith
      · apply (div_lt_iff₀ hu).mpr
        have h := (div_lt_iff₀ hk1).mp hlo
        nlinarith
    · constructor
      · exact hu
      · have h := (le_div_iff₀ hkR).mp hhi
        nlinarith [mul_le_mul_of_nonneg_left hone hu.le]

/-- Every positive point mass is obtained from its actual uniform preimage. -/
theorem uniformUnit_reciprocalFloor_mass (k : ℕ) (hk : 0 < k) :
    uniformUnit {u | reciprocalFloor u = k} =
      ENNReal.ofReal (1 / ((k : ℝ) * ((k : ℝ) + 1))) := by
  have hs : MeasurableSet {u : ℝ | reciprocalFloor u = k} :=
    reciprocalFloor_measurable (measurableSet_singleton k)
  rw [uniformUnit, Measure.restrict_apply hs, reciprocalFloor_fiber k hk,
    Real.volume_Ioc]
  congr 1
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hkR, hk1]
  ring

/-- Pushforward formulation of `P(K=k)=1/(k(k+1))`. -/
theorem reciprocalFloor_map_mass (k : ℕ) (hk : 0 < k) :
    (Measure.map reciprocalFloor uniformUnit) {k} =
      ENNReal.ofReal (1 / ((k : ℝ) * ((k : ℝ) + 1))) := by
  rw [Measure.map_apply reciprocalFloor_measurable (measurableSet_singleton k)]
  exact uniformUnit_reciprocalFloor_mass k hk

/-- The zero value introduced by totalizing natural floor has probability zero. -/
theorem reciprocalFloor_zero_fiber :
    {u : ℝ | reciprocalFloor u = 0} ∩ Ioc 0 1 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hf : reciprocalFloor u = 0 := hu.1
  have hlo : (1 : ℝ) ≤ 1 / u :=
    (le_div_iff₀ hu.2.1).mpr (by simpa using hu.2.2)
  have hhi : 1 / u < (reciprocalFloor u : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [hf] at hhi
  norm_num at hhi
  simp only [one_div] at hlo
  linarith

theorem reciprocalFloor_map_zero_mass :
    (Measure.map reciprocalFloor uniformUnit) {0} = 0 := by
  rw [Measure.map_apply reciprocalFloor_measurable (measurableSet_singleton 0)]
  have hs : MeasurableSet {u : ℝ | reciprocalFloor u = 0} :=
    reciprocalFloor_measurable (measurableSet_singleton 0)
  change uniformUnit {u | reciprocalFloor u = 0} = 0
  rw [uniformUnit, Measure.restrict_apply hs, reciprocalFloor_zero_fiber, measure_empty]

/-- The same formula includes the zero atom, using Lean's totalized division. -/
theorem reciprocalFloor_map_mass_all (k : ℕ) :
    (Measure.map reciprocalFloor uniformUnit) {k} =
      ENNReal.ofReal (1 / ((k : ℝ) * ((k : ℝ) + 1))) := by
  by_cases hk : k = 0
  · subst k
    simp [reciprocalFloor_map_zero_mass]
  · exact reciprocalFloor_map_mass k (Nat.pos_of_ne_zero hk)

/-- The exact integral transfer, valid even before integrability is established. -/
theorem uniformUnit_lintegral_reciprocalFloor (f : ℕ → ℝ≥0∞) :
    (∫⁻ u, f (reciprocalFloor u) ∂uniformUnit) =
      ∑' k : ℕ, f k * ENNReal.ofReal (1 / ((k : ℝ) * ((k : ℝ) + 1))) := by
  have hf : Measurable f := continuous_of_discreteTopology.measurable
  rw [← lintegral_map hf reciprocalFloor_measurable, lintegral_countable']
  simp_rw [reciprocalFloor_map_mass_all]

/-- Square-error transfer retaining the complete infinite Pareto sum. -/
theorem uniformUnit_lintegral_square (f : ℕ → ℝ) :
    (∫⁻ u, ENNReal.ofReal ((f (reciprocalFloor u)) ^ 2) ∂uniformUnit) =
      ∑' k : ℕ, ENNReal.ofReal (1 / ((k : ℝ) * ((k : ℝ) + 1)) * (f k) ^ 2) := by
  rw [uniformUnit_lintegral_reciprocalFloor (fun k : ℕ => ENNReal.ofReal ((f k) ^ 2))]
  apply tsum_congr
  intro k
  rw [ENNReal.ofReal_mul (by positivity)]
  exact mul_comm _ _

end
end RiemannResearch.RH.Pareto
