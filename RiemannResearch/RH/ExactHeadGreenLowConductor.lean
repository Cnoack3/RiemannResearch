import RiemannResearch.RH.ExactHeadGreenProfile
import RiemannResearch.RH.MobiusAffineProfile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Support - sensitive low - conductor Green energy
Source: user - provided "Exact - Head Green Profiles in the Nyman--Beurling Program",
27 July 2026, Theorem 5.1 and agenda A1.1 / R2 / R4.
The exact support mass and squarefree sum are retained before the polynomial
bound. The bound needs no assumption D <= x. Its relative - budget version
does not assume bounded optimized energy q.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ExactHeadGreenLowConductor
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.ExactHeadGreenProfile

theorem sum_cast_Icc (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, (d : ℝ)) = (D : ℝ) * ((D : ℝ) + 1) / 2 := by
  induction D with
  | zero => norm_num
  | succ D ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

theorem squarefree_centered_sum_le (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D,
      MobiusAffineProfile.weight d * (((d : ℝ) - 1) ^ 2 / 4)) ≤
      (D : ℝ) * ((D : ℝ) + 1) / 8 := by
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, (d : ℝ) / 4 := by
      apply Finset.sum_le_sum
      intro d hd
      have hd1 : (1:ℝ) ≤ (d : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hprod : (ArithmeticFunction.moebius d : ℝ) ^ 2 * ((d : ℝ) - 1) ^ 2 ≤ (d : ℝ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_right (MobiusAffineProfile.moebius_sq_le_one d)
          (sq_nonneg ((d : ℝ) - 1))
        nlinarith
      have he : MobiusAffineProfile.weight d * (((d : ℝ) - 1) ^ 2 / 4) =
          ((ArithmeticFunction.moebius d : ℝ) ^ 2 * ((d : ℝ) - 1) ^ 2) / (4 * (d : ℝ)) := by
        unfold MobiusAffineProfile.weight
        ring
      rw [he]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (d : ℝ))).2
      nlinarith
    _ = _ := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, sum_cast_Icc]
      ring

/-- Sharp support - mass bound, before dropping the squarefree arithmetic. -/
theorem low_conductor_sharp (s : Finset ℕ) (w R : ℕ → ℝ) (x D : ℕ)
    (hw : ∀ r ∈ s, 0 ≤ w r)
    (hhead : ∀ r ∈ s, r ≤ x → R r = 0) :
    (∑ d ∈ Finset.Icc 1 D, MobiusAffineProfile.weight d *
      pairing s w R (centeredResidue d) ^ 2) ≤
      energy s w R * mass (s.filter (fun r => x < r)) w *
      (∑ d ∈ Finset.Icc 1 D, MobiusAffineProfile.weight d * (((d : ℝ) - 1) ^ 2 / 4)) := by
  let t := s.filter (fun r => x < r)
  have hts : t ⊆ s := Finset.filter_subset _ _
  have hz : ∀ r ∈ s, r ∉ t → R r = 0 := by
    intro r hr hrt
    apply hhead r hr
    by_contra! hx
    exact hrt (Finset.mem_filter.mpr ⟨hr, hx⟩)
  have he := energy_support s t w R hts hz
  have hp (g : ℕ → ℝ) := pairing_support s t w R g hts hz
  have h := frame_bound t (Finset.Icc 1 D) w R MobiusAffineProfile.weight
    (fun d => ((d : ℝ) - 1) ^ 2 / 4) centeredResidue
    (fun r hr => hw r (hts hr)) (fun d _ => MobiusAffineProfile.weight_nonneg d)
    (fun d hd r _ => centeredResidue_sq_le d r (Finset.mem_Icc.mp hd).1)
  simpa only [he, hp] using h

/-- The paper's low - conductor bound, with arbitrary D and the tail - mass
hypothesis explicitly visible. -/
theorem low_conductor_bound (s : Finset ℕ) (w R : ℕ → ℝ) (x D : ℕ)
    (hw : ∀ r ∈ s, 0 ≤ w r)
    (hhead : ∀ r ∈ s, r ≤ x → R r = 0)
    (hmass : mass (s.filter (fun r => x < r)) w ≤ 1 / ((x : ℝ) + 1)) :
    (∑ d ∈ Finset.Icc 1 D, MobiusAffineProfile.weight d *
      pairing s w R (centeredResidue d) ^ 2) ≤
      energy s w R * (D : ℝ) * ((D : ℝ) + 1) / (8 * ((x : ℝ) + 1)) := by
  have hq := energy_nonneg s w R hw
  have hS : 0 ≤ ∑ d ∈ Finset.Icc 1 D,
      MobiusAffineProfile.weight d * (((d : ℝ) - 1) ^ 2 / 4) := by
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (MobiusAffineProfile.weight_nonneg d) (by positivity)
  calc
    _ ≤ energy s w R * mass (s.filter (fun r => x < r)) w *
        (∑ d ∈ Finset.Icc 1 D, MobiusAffineProfile.weight d * (((d : ℝ) - 1) ^ 2 / 4)) :=
      low_conductor_sharp s w R x D hw hhead
    _ ≤ energy s w R * (1 / ((x : ℝ) + 1)) *
        (∑ d ∈ Finset.Icc 1 D, MobiusAffineProfile.weight d * (((d : ℝ) - 1) ^ 2 / 4)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass hq) hS
    _ ≤ energy s w R * (1 / ((x : ℝ) + 1)) * ((D : ℝ) * ((D : ℝ) + 1) / 8) :=
      mul_le_mul_of_nonneg_left (squarefree_centered_sum_le D) (by positivity)
    _ = _ := by
      have hx : (x : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hx]
      <;> ring

/-- Finite relative budget. Choosing D of size sqrt(x / W) controls W times
the low - conductor energy by Cq without first assuming q is bounded. -/
theorem low_conductor_relative_budget (s : Finset ℕ) (w R : ℕ → ℝ) (x D : ℕ)
    (hw : ∀ r ∈ s, 0 ≤ w r)
    (hhead : ∀ r ∈ s, r ≤ x → R r = 0)
    (hmass : mass (s.filter (fun r => x < r)) w ≤ 1 / ((x : ℝ) + 1))
    (W C : ℝ) (hW : 0 ≤ W)
    (hbudget : W * (D : ℝ) * ((D : ℝ) + 1) ≤ 8 * C * ((x : ℝ) + 1)) :
    W * (∑ d ∈ Finset.Icc 1 D, MobiusAffineProfile.weight d *
      pairing s w R (centeredResidue d) ^ 2) ≤ C * energy s w R := by
  have h := low_conductor_bound s w R x D hw hhead hmass
  have hd : 0 < 8 * ((x : ℝ) + 1) := by positivity
  have h1 := mul_le_mul_of_nonneg_left ((le_div_iff₀ hd).mp h) hW
  have h2 := mul_le_mul_of_nonneg_left hbudget (energy_nonneg s w R hw)
  by_contra! hn
  have hp := mul_pos hd (sub_pos.mpr hn)
  nlinarith

end RiemannResearch.RH.ExactHeadGreenLowConductor
