import RiemannResearch.Analysis.MellinDifferenceBounds
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Holomorphic first-difference Mellin series

Source: classical Abel summation and the Weierstrass theorem, assembled using
the existing exact first-difference bound. The actual Mertens weighted-energy
application is in `RH/MertensEnergyRH.lean`.
The absolute moment is an explicit hypothesis.
-/

noncomputable section
open Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Analysis.Cesaro

def firstMellinSeries (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, a (n + 1) * mellinFirst s (n + 1)

/-- The absolute moment controls the complete first-difference series. -/
theorem firstMellinSeries_summable (a : ℕ → ℂ) (q : ℝ) (hq : 0 < q)
    (ha : Summable (fun n : ℕ => ‖a (n + 1)‖ * ((n : ℝ) + 1) ^ (-1 - q)))
    (s : ℂ) (hs : q ≤ s.re) :
    Summable (fun n : ℕ => a (n + 1) * mellinFirst s (n + 1)) := by
  apply Summable.of_norm_bounded (ha.mul_left ‖s‖)
  intro n
  rw [norm_mul]
  calc
    _ ≤ ‖a (n + 1)‖ * (‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) :=
      mul_le_mul_of_nonneg_left
        (mellinFirst_norm_le s (lt_of_lt_of_le hq hs) _ (by omega)) (norm_nonneg _)
    _ ≤ ‖s‖ * (‖a (n + 1)‖ * ((n : ℝ) + 1) ^ (-1 - q)) := by
      rw [Nat.cast_add, Nat.cast_one]
      have hpow := Real.rpow_le_rpow_of_exponent_le
        (by have := Nat.cast_nonneg (α := ℝ) n; linarith : 1 ≤ (n : ℝ) + 1)
        (show -s.re - 1 ≤ -1 - q by linarith)
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (norm_nonneg (a (n + 1))) (norm_nonneg s))

/-- The first-difference sum is holomorphic strictly inside the moment half-plane.
The normal-convergence majorant is proved on a bounded neighborhood of each point. -/
theorem firstMellinSeries_differentiableAt (a : ℕ → ℂ) (q : ℝ) (hq : 0 < q)
    (ha : Summable (fun n : ℕ => ‖a (n + 1)‖ * ((n : ℝ) + 1) ^ (-1 - q)))
    (s : ℂ) (hs : q < s.re) :
    DifferentiableAt ℂ (firstMellinSeries a) s := by
  let U : Set ℂ := {z | q < z.re} ∩ {z | ‖z‖ < ‖s‖ + 1}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := by
    change q < s.re ∧ ‖s‖ < ‖s‖ + 1
    exact ⟨hs, by linarith⟩
  have hd (n : ℕ) : DifferentiableOn ℂ (fun z => a (n + 1) * mellinFirst z (n + 1)) U := by
    intro z hz
    have h1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have h2 : ((n + 1 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (n + 1))
    exact ((differentiableAt_const (a (n + 1))).mul
      ((differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
        (differentiableAt_id.neg.const_cpow (Or.inl h2)))).differentiableWithinAt
  have hdom (n : ℕ) (z : ℂ) (hz : z ∈ U) :
      ‖a (n + 1) * mellinFirst z (n + 1)‖ ≤
        (‖s‖ + 1) * (‖a (n + 1)‖ * ((n : ℝ) + 1) ^ (-1 - q)) := by
    change q < z.re ∧ ‖z‖ < ‖s‖ + 1 at hz
    rw [norm_mul]
    have hm := mellinFirst_norm_le z (lt_trans hq hz.1) (n + 1) (by omega)
    have hp := Real.rpow_le_rpow_of_exponent_le
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith : 1 ≤ (n : ℝ) + 1)
      (show -z.re - 1 ≤ -1 - q by linarith [hz.1])
    simp only [Nat.cast_add, Nat.cast_one] at hm
    calc
      _ ≤ ‖a (n + 1)‖ * (‖z‖ * ((n : ℝ) + 1) ^ (-z.re - 1)) :=
        mul_le_mul_of_nonneg_left hm (norm_nonneg _)
      _ ≤ ‖a (n + 1)‖ * ((‖s‖ + 1) * ((n : ℝ) + 1) ^ (-1 - q)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hz.2.le hp (Real.rpow_nonneg (by positivity) _) (by positivity))
          (norm_nonneg _)
      _ = _ := by ring
  exact (Complex.differentiableOn_tsum_of_summable_norm (ha.mul_left (‖s‖ + 1))
    hd hU hdom).differentiableAt (hU.mem_nhds hsU)

/-- The absolute moment yields analyticity throughout its open half-plane. -/
theorem firstMellinSeries_analyticOnNhd (a : ℕ → ℂ) (q : ℝ) (hq : 0 < q)
    (ha : Summable (fun n : ℕ => ‖a (n + 1)‖ * ((n : ℝ) + 1) ^ (-1 - q))) :
    AnalyticOnNhd ℂ (firstMellinSeries a) {s : ℂ | q < s.re} := by
  have hd : DifferentiableOn ℂ (firstMellinSeries a) {s : ℂ | q < s.re} :=
    fun s hs => (firstMellinSeries_differentiableAt a q hq ha s hs).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end RiemannResearch.Analysis.Cesaro
