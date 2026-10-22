import RiemannResearch.RH.DampedMobiusCoefficients
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Power-damped physical Möbius sums and primitive variation

Source: independently derived continuation of the user-provided
`RH_Lateral_Screening_Continuation_2026-09-24(2).md`.
The Euler product is supplied by `DampedMobiusCoefficients`.

These are unconditional finite arithmetic and convergence statements.
The parameter `c` represents a centering constant; identifying it with
`1 / zeta (1 + epsilon)` and interchanging an infinite legal-vector sum
with a primitive pairing require a separate analytic argument. In particular,
no Hilbert-space membership of the infinite damped approximant is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

def dampedPhysicalSum (ε c : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n, dampedDivisorCoefficient ε (k + 1)) - c * n

@[simp] theorem dampedPhysicalSum_zero (ε c : ℝ) :
    dampedPhysicalSum ε c 0 = 0 := by simp [dampedPhysicalSum]

theorem dampedPhysicalSum_step (ε c : ℝ) (n : ℕ) :
    dampedPhysicalSum ε c (n + 1) - dampedPhysicalSum ε c n =
      dampedDivisorCoefficient ε (n + 1) - c := by
  simp only [dampedPhysicalSum, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem dampedPhysicalSum_bounds {ε c : ℝ} (hε : 0 ≤ ε)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    -(n : ℝ) ≤ dampedPhysicalSum ε c n ∧ dampedPhysicalSum ε c n ≤ n := by
  have hs0 : 0 ≤ ∑ k ∈ Finset.range n, dampedDivisorCoefficient ε (k + 1) :=
    Finset.sum_nonneg fun k _ => dampedDivisorCoefficient_nonneg hε (k + 1)
  have hs1 : (∑ k ∈ Finset.range n, dampedDivisorCoefficient ε (k + 1)) ≤ n := by
    calc
      _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => dampedDivisorCoefficient_le_one hε (k + 1)
      _ = _ := by simp
  have hn := Nat.cast_nonneg (α := ℝ) n
  dsimp [dampedPhysicalSum]
  constructor <;> nlinarith

theorem dampedPhysicalSum_abs_step_le_one {ε c : ℝ} (hε : 0 ≤ ε)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    |dampedPhysicalSum ε c (n + 1) - dampedPhysicalSum ε c n| ≤ 1 := by
  rw [dampedPhysicalSum_step, abs_le]
  have ha0 := dampedDivisorCoefficient_nonneg hε (n + 1)
  have ha1 := dampedDivisorCoefficient_le_one hε (n + 1)
  constructor <;> linarith

def dampedPhysicalWeight (ε c : ℝ) (n : ℕ) : ℝ :=
  dampedPhysicalSum ε c n / ((n : ℝ) * ((n : ℝ) + 1))

theorem dampedPhysicalWeight_difference (ε c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    dampedPhysicalWeight ε c (n + 1) - dampedPhysicalWeight ε c n =
      ((n : ℝ) * (dampedDivisorCoefficient ε (n + 1) - c) -
          2 * dampedPhysicalSum ε c n) /
        ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hs := dampedPhysicalSum_step ε c n
  have hs' : dampedPhysicalSum ε c (n + 1) =
      dampedPhysicalSum ε c n + dampedDivisorCoefficient ε (n + 1) - c := by linarith
  dsimp [dampedPhysicalWeight]
  rw [hs']
  push_cast
  field_simp
  ring

/-- The signed divisor product removes the divisor-count loss completely. -/
theorem dampedPhysicalWeight_variation_le {ε c : ℝ} (hε : 0 ≤ ε)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    |dampedPhysicalWeight ε c (n + 1) - dampedPhysicalWeight ε c n| ≤
      2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs0 : 0 ≤ ∑ k ∈ Finset.range n, dampedDivisorCoefficient ε (k + 1) :=
    Finset.sum_nonneg fun k _ => dampedDivisorCoefficient_nonneg hε (k + 1)
  have hs1 : (∑ k ∈ Finset.range n, dampedDivisorCoefficient ε (k + 1)) ≤ n := by
    calc
      _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => dampedDivisorCoefficient_le_one hε (k + 1)
      _ = _ := by simp
  have ha0 := dampedDivisorCoefficient_nonneg hε (n + 1)
  have ha1 := dampedDivisorCoefficient_le_one hε (n + 1)
  have hnum : |(n : ℝ) * (dampedDivisorCoefficient ε (n + 1) - c) -
      2 * dampedPhysicalSum ε c n| ≤ 2 * n := by
    rw [abs_le]
    dsimp [dampedPhysicalSum]
    constructor <;> nlinarith
  rw [dampedPhysicalWeight_difference ε c n hn, abs_div,
    abs_of_pos (show 0 < (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) by positivity)]
  calc
    _ ≤ (2 * n) / ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by field_simp

theorem dampedDivisorCoefficient_tendsto_zero_of_two_le
    (ε : ℕ → ℝ) (hε : ∀ j, 0 ≤ ε j) (hlim : Tendsto ε atTop (𝓝 0))
    (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun j => dampedDivisorCoefficient (ε j) n) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun j => dampedDivisorCoefficient_nonneg (hε j) n)
    (fun j => dampedDivisorCoefficient_le_mul_log (hε j) hn)
  simpa only [zero_mul] using hlim.mul_const (Real.log n)

theorem dampedPhysicalSum_tendsto_one
    (ε c : ℕ → ℝ) (hε : ∀ j, 0 ≤ ε j)
    (hlim : Tendsto ε atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun j => dampedPhysicalSum (ε j) (c j) n) atTop (𝓝 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hs : Tendsto
      (fun j => ∑ k ∈ Finset.range m, dampedDivisorCoefficient (ε j) (k + 2))
      atTop (𝓝 0) := by
    have ht := tendsto_finsetSum (Finset.range m) (fun k _ =>
      dampedDivisorCoefficient_tendsto_zero_of_two_le ε hε hlim (k + 2) (by omega))
    simpa only [Finset.sum_const_zero] using ht
  have he (j : ℕ) : dampedPhysicalSum (ε j) (c j) (m + 1) =
      1 + (∑ k ∈ Finset.range m, dampedDivisorCoefficient (ε j) (k + 2)) -
        c j * (m + 1) := by
    rw [dampedPhysicalSum, Finset.sum_range_succ']
    simp only [zero_add, dampedDivisorCoefficient_one, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [he]
  simpa using (tendsto_const_nhds.add hs).sub (hc.mul_const ((m : ℝ) + 1))

/-- Pointwise convergence holds without asserting a norm limit. -/
theorem dampedPhysicalWeight_tendsto
    (ε c : ℕ → ℝ) (hε : ∀ j, 0 ≤ ε j)
    (hlim : Tendsto ε atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun j => dampedPhysicalWeight (ε j) (c j) n) atTop
      (𝓝 (1 / ((n : ℝ) * ((n : ℝ) + 1)))) := by
  exact (dampedPhysicalSum_tendsto_one ε c hε hlim hc n hn).div_const _

/-- The primitive-side pairing limit needs neither Hilbert membership of
an infinite damped approximant nor an exchange of damping and physical cutoffs.
The identification with legal-vector pairings remains a separate theorem. -/
theorem dampedPhysicalPrimitive_pairing_tendsto
    (H ε c : ℕ → ℝ) (hε : ∀ j, 0 ≤ ε j)
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hlim : Tendsto ε atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    (hH : Summable (fun n : ℕ => |H (n + 1)| *
      (2 / (((n : ℝ) + 2) * ((n : ℝ) + 3))))) :
    Tendsto (fun j => ∑' n : ℕ, H (n + 1) *
      (dampedPhysicalWeight (ε j) (c j) (n + 1) -
       dampedPhysicalWeight (ε j) (c j) (n + 2))) atTop
      (𝓝 (∑' n : ℕ, H (n + 1) *
        (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) -
         1 / (((n : ℝ) + 2) * ((n : ℝ) + 3))))) := by
  apply tendsto_tsum_of_dominated_convergence hH
  · intro n
    have h1 := dampedPhysicalWeight_tendsto ε c hε hlim hc (n + 1) (by omega)
    have h2 := dampedPhysicalWeight_tendsto ε c hε hlim hc (n + 2) (by omega)
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring,
      show (n : ℝ) + 2 + 1 = (n : ℝ) + 3 by ring] using
        (h1.sub h2).const_mul (H (n + 1))
  · filter_upwards [] with j
    intro n
    rw [Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [abs_sub_comm]
    simpa only [Nat.cast_add, Nat.cast_one,
      show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring,
      show (n : ℝ) + 1 + 2 = (n : ℝ) + 3 by ring,
      show n + 1 + 1 = n + 2 by omega] using
        dampedPhysicalWeight_variation_le (hε j) (hc0 j) (hc1 j) (n + 1) (by omega)

end RiemannResearch.RH.Pareto
