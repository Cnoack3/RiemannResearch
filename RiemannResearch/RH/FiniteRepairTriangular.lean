import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Finite triangular repair charges

The recurrence below retains the exact normalized divisor-jump relation until
the stated coefficient estimate.  It quantifies the obstruction to concentrating
a fixed nonzero charge on a bounded number of repair endpoints.
-/

namespace RiemannResearch.RH.FiniteRepairTriangular

open scoped BigOperators

theorem l1_bound (a : ℕ → ℝ) (Z : ℝ) (N : ℕ)
    (hstep : ∀ j < N, |a j| ≤ Z + (1 / 2 : ℝ) * ∑ i ∈ Finset.range j, |a i|) :
    (∑ i ∈ Finset.range N, |a i|) ≤
      2 * (((3 / 2 : ℝ) ^ N) - 1) * Z := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hprev := ih (fun j hj => hstep j (by omega))
    have hlast := hstep N (by omega)
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith

/-- A nonzero total charge, bounded jumps, and the triangular recurrence force
positive energy.  The factor `3/2` comes only from proper divisor ratios. -/
theorem energy_floor (a : ℕ → ℝ) (N : ℕ) (E : ℝ)
    (hN : 0 < N) (hE : 0 ≤ E)
    (hcharge : (∑ i ∈ Finset.range N, a i) = -(1 / 3 : ℝ))
    (hstep : ∀ j < N, |a j| ≤ Real.sqrt (2 * E) +
      (1 / 2 : ℝ) * ∑ i ∈ Finset.range j, |a i|) :
    1 / (72 * (((3 / 2 : ℝ) ^ N) - 1) ^ 2) ≤ E := by
  have hsumabs : (1 / 3 : ℝ) ≤ ∑ i ∈ Finset.range N, |a i| := by
    calc
      (1 / 3 : ℝ) = |∑ i ∈ Finset.range N, a i| := by rw [hcharge]; norm_num
      _ ≤ ∑ i ∈ Finset.range N, |a i| := Finset.abs_sum_le_sum_abs _ _
  have hbound := hsumabs.trans (l1_bound a (Real.sqrt (2 * E)) N hstep)
  have hpow : 1 < (3 / 2 : ℝ) ^ N := one_lt_pow₀ (by norm_num) (by omega)
  have hR : 0 < (3 / 2 : ℝ) ^ N - 1 := sub_pos.mpr hpow
  have hsqrt := Real.sqrt_nonneg (2 * E)
  have hsqrt_sq := Real.sq_sqrt (show 0 ≤ 2 * E by positivity)
  have hsq : (1 / 3 : ℝ) ^ 2 ≤
      (2 * (((3 / 2 : ℝ) ^ N) - 1) * Real.sqrt (2 * E)) ^ 2 :=
    (sq_le_sq₀ (by norm_num) (by positivity)).mpr hbound
  have hproduct : 1 ≤ (72 * (((3 / 2 : ℝ) ^ N) - 1) ^ 2) * E := by
    nlinarith [hsqrt_sq]
  exact (div_le_iff₀ (by positivity)).mpr (by nlinarith [hproduct])

/-- Exact signed-share variance identity, with all fluctuations retained. -/
theorem signed_share_square_completion {ι : Type*} (s : Finset ι)
    (ρ : ι → ℝ) (hs : s.Nonempty) (hρ : ∑ i ∈ s, ρ i = 1) :
    (∑ i ∈ s, (ρ i) ^ 2) =
      1 / (s.card : ℝ) + ∑ i ∈ s, (ρ i - 1 / (s.card : ℝ)) ^ 2 := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hs)
  have hexpand : (∑ i ∈ s, (ρ i - 1 / (s.card : ℝ)) ^ 2) =
      (∑ i ∈ s, (ρ i) ^ 2) - 2 / (s.card : ℝ) * (∑ i ∈ s, ρ i) +
        (s.card : ℝ) * (1 / (s.card : ℝ)) ^ 2 := by
    have he (x : ℝ) : (x - 1 / (s.card : ℝ)) ^ 2 =
        x ^ 2 - (2 / (s.card : ℝ)) * x + (1 / (s.card : ℝ)) ^ 2 := by ring
    simp_rw [he]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hrecip : (s.card : ℝ) * (1 / (s.card : ℝ)) ^ 2 = 1 / (s.card : ℝ) := by
    field_simp
  have htwo : 2 / (s.card : ℝ) = 2 * (1 / (s.card : ℝ)) := by ring
  rw [hρ, hrecip, htwo] at hexpand
  nlinarith

end RiemannResearch.RH.FiniteRepairTriangular
