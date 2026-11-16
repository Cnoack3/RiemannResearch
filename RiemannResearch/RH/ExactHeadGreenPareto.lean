import RiemannResearch.RH.ExactHeadGreenLowConductor
import RiemannResearch.RH.ParetoExactHeadCRT
import RiemannResearch.Analysis.GreenProfileBounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Actual periodized Pareto support bounds for Green profiles
Source: user - provided "Exact - Head Green Profiles in the Nyman--Beurling Program",
27 July 2026, Theorems 3.1 and 5.1. The full infinite progression weight is
used. Tail mass is proved, not assumed; no return or terminal mass is dropped
from a normalization identity.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadGreen
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.GreenProfileBounds
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.RH.ExactHeadGreenLowConductor

private theorem sum_Icc_eq_range (P : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 P, f r) = ∑ j ∈ Finset.range P, f (j + 1) := by
  induction P with
  | zero => simp
  | succ P ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

theorem period_mass (P : ℕ) (hP : 0 < P) :
    (∑ r ∈ Finset.Icc 1 P, progressionWeight P r) = 1 := by
  rw [sum_Icc_eq_range, ← Fin.sum_univ_eq_sum_range]
  exact progressionWeight_normalization P hP

/-- Every complete residue tail is a subset of the true Pareto integer tail. -/
theorem period_tail_mass_le (P x : ℕ) (hP : 0 < P) (hx : x ≤ P) :
    mass ((Finset.Icc 1 P).filter (fun r => x < r)) (progressionWeight P) ≤
      1 / ((x : ℝ) + 1) := by
  have hh : (∑ r ∈ Finset.Icc 1 P, if r ≤ x then positiveWeight r else 0) =
      (x : ℝ) / ((x : ℝ) + 1) := by
    rw [sum_Icc_eq_range, ← Fin.sum_univ_eq_sum_range]
    exact ExactHeadCRT.headMass P x hx
  have hb :
      (∑ r ∈ Finset.Icc 1 P, if r ≤ x then positiveWeight r else 0) +
        mass ((Finset.Icc 1 P).filter (fun r => x < r)) (progressionWeight P) ≤ 1 := by
    rw [mass, Finset.sum_filter, ← Finset.sum_add_distrib, ← period_mass P hP]
    apply Finset.sum_le_sum
    intro r hr
    by_cases hrx : r ≤ x
    · simp only [if_pos hrx, if_neg (Nat.not_lt.mpr hrx), add_zero]
      exact positiveWeight_le_progressionWeight P r hP
    · simp [hrx, Nat.lt_of_not_ge hrx]
  rw [hh] at hb
  have hid : (x : ℝ) / ((x : ℝ) + 1) + 1 / ((x : ℝ) + 1) = 1 := by
    have h : (x : ℝ) + 1 ≠ 0 := by positivity
    field_simp [h]
  linarith

theorem subset_tail_mass_le (P x : ℕ) (hP : 0 < P) (hx : x ≤ P)
    (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 P) :
    mass (s.filter (fun r => x < r)) (progressionWeight P) ≤ 1 / ((x : ℝ) + 1) := by
  apply le_trans _ (period_tail_mass_le P x hP hx)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    exact Finset.mem_filter.mpr ⟨hs (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2⟩
  · intro r hr hn
    exact progressionWeight_nonneg P r

/-- The paper's tail - charge bound for the actual infinite progression weights. -/
theorem tail_charge_sq_le (P x : ℕ) (hP : 0 < P) (hx : x ≤ P)
    (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 P) (R : ℕ → ℝ)
    (hhead : ∀ r ∈ s, r ≤ x → R r = 0) :
    pairing s (progressionWeight P) R (fun _ => 1) ^ 2 ≤
      energy s (progressionWeight P) R / ((x : ℝ) + 1) := by
  let t := s.filter (fun r => x < r)
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hz : ∀ r ∈ s, r ∉ t → R r = 0 := by
    intro r hr hrt
    apply hhead r hr
    by_contra! h
    exact hrt (Finset.mem_filter.mpr ⟨hr,h⟩)
  have he := energy_support s t (progressionWeight P) R hts hz
  have hp := pairing_support s t (progressionWeight P) R (fun _ => 1) hts hz
  have hc := pairing_sq_le t (progressionWeight P) R (fun _ => 1)
    (fun r hr => progressionWeight_nonneg P r)
  have hm := subset_tail_mass_le P x hP hx s hs
  have hq := energy_nonneg s (progressionWeight P) R (fun r hr => progressionWeight_nonneg P r)
  have h1 : energy t (progressionWeight P) (fun _ => 1) =
      mass t (progressionWeight P) := by simp [energy, mass]
  rw [he,hp,h1] at hc
  calc
    _ ≤ energy s (progressionWeight P) R * mass t (progressionWeight P) := hc
    _ ≤ energy s (progressionWeight P) R * (1 / ((x : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hm hq
    _ = _ := by ring

/-- Low - conductor estimate with the actual Pareto mass provider discharged. -/
theorem actual_low_conductor_bound (P x D : ℕ) (hP : 0 < P) (hx : x ≤ P)
    (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 P) (R : ℕ → ℝ)
    (hhead : ∀ r ∈ s, r ≤ x → R r = 0) :
    (∑ d ∈ Finset.Icc 1 D, MobiusAffineProfile.weight d *
      pairing s (progressionWeight P) R (centeredResidue d) ^ 2) ≤
      energy s (progressionWeight P) R * (D : ℝ) * ((D : ℝ) + 1) / (8 * ((x : ℝ) + 1)) :=
  low_conductor_bound s (progressionWeight P) R x D
    (fun r hr => progressionWeight_nonneg P r) hhead (subset_tail_mass_le P x hP hx s hs)

/-- Elementary terminal bound, sufficient without invoking zeta(2). -/
theorem terminal_weight_le (P : ℕ) (hP : 0 < P) :
    progressionWeight P P ≤ 2 / ((P : ℝ) * ((P : ℝ) + 1)) := by
  have h := progressionWeight_upper_one P P hP
  unfold positiveWeight at h
  convert h using 1 <;> ring

end RiemannResearch.RH.Pareto.ExactHeadGreen
