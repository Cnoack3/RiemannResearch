/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Finite Hankel positivity for zero-ordinate harmonic analysis.

The statements below do not posit the Riemann hypothesis or any assertion about
zeta zeros.  They establish the finite algebra and the passage to a pointwise
limit needed for a moment criterion.  A separate analytic argument must identify
the limiting moments with derivatives of a full-zero Gaussian trace.
-/

namespace RiemannResearch.Analysis.HankelMomentPositivity

open scoped BigOperators Topology
open Filter

def PSD2 (a b c : ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2

/-- Exact real symmetric two-by-two criterion, including the singular boundary. -/
theorem psd2_iff (a b c : ℝ) :
    PSD2 a b c ↔ 0 ≤ a ∧ 0 ≤ c ∧ b ^ 2 ≤ a * c := by
  constructor
  · intro h
    have ha : 0 ≤ a := by simpa [PSD2] using h 1 0
    have hc : 0 ≤ c := by simpa [PSD2] using h 0 1
    refine ⟨ha, hc, ?_⟩
    by_cases hz : a = 0
    · have hh := h (-(c + 1)) b
      rw [hz] at hh ⊢
      have hbc : 0 ≤ b ^ 2 * c := mul_nonneg (sq_nonneg b) hc
      nlinarith [sq_nonneg b]
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
      have hh := h b (-a)
      have hp : 0 ≤ a * (a * c - b ^ 2) := by nlinarith only [hh]
      have hd : 0 ≤ a * c - b ^ 2 := nonneg_of_mul_nonneg_right hp hap
      linarith
  · rintro ⟨ha, hc, hd⟩ x y
    by_cases hz : a = 0
    · have hb : b = 0 := by
        rw [hz] at hd
        nlinarith [sq_nonneg b]
      rw [hz, hb]
      simpa using mul_nonneg hc (sq_nonneg y)
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
      have hsq := sq_nonneg (a * x + b * y)
      have hrem : 0 ≤ (a * c - b ^ 2) * y ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg y)
      have hp : 0 ≤ a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) := by
        nlinarith only [hsq, hrem]
      exact nonneg_of_mul_nonneg_right hp hap

/-- When the leading diagonal is positive, `(b,-a)` is a negative direction. -/
theorem negative_direction_of_pos_leading {a b c : ℝ}
    (ha : 0 < a) (hd : a * c - b ^ 2 < 0) :
    a * b ^ 2 + 2 * b * b * (-a) + c * (-a) ^ 2 < 0 := by
  have hp := mul_neg_of_pos_of_neg ha hd
  nlinarith only [hp]

/-- The singular leading diagonal has an explicit denominator-free negative direction. -/
theorem negative_direction_of_zero_leading {b c : ℝ}
    (hc : 0 ≤ c) (hb : b ≠ 0) :
    (0 : ℝ) * (-(c + 1)) ^ 2 + 2 * b * (-(c + 1)) * b + c * b ^ 2 < 0 := by
  have hsq : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hp : 0 ≤ b ^ 2 * c := mul_nonneg hsq.le hc
  nlinarith

/-- Every negative determinant gives a finite real quadratic witness. -/
theorem exists_negative_direction_of_det_neg {a b c : ℝ}
    (hd : a * c - b ^ 2 < 0) :
    ∃ x y : ℝ, a * x ^ 2 + 2 * b * x * y + c * y ^ 2 < 0 := by
  by_cases ha : 0 ≤ a
  · by_cases hc : 0 ≤ c
    · by_cases hz : a = 0
      · have hb : b ≠ 0 := by
          intro hb
          simp [hz, hb] at hd
        refine ⟨-(c + 1), b, ?_⟩
        simpa [hz] using negative_direction_of_zero_leading hc hb
      · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
        exact ⟨b, -a, negative_direction_of_pos_leading hap hd⟩
    · refine ⟨0, 1, ?_⟩
      simpa using (lt_of_not_ge hc)
  · refine ⟨1, 0, ?_⟩
    simpa using (lt_of_not_ge ha)

def FinitePSD {ι : Type*} [Fintype ι] (A : ι → ι → ℝ) : Prop :=
  ∀ v : ι → ℝ, 0 ≤ ∑ i, ∑ j, v i * v j * A i j

/-- Positivity of arbitrary finite quadratic forms is closed under entrywise limits. -/
theorem finitePSD_limit {ι : Type*} [Fintype ι]
    {A : ℕ → ι → ι → ℝ} {K : ι → ι → ℝ}
    (hlim : ∀ i j, Tendsto (fun r => A r i j) atTop (𝓝 (K i j)))
    (hpos : ∀ r, FinitePSD (A r)) : FinitePSD K := by
  intro v
  have hq : Tendsto (fun r => ∑ i, ∑ j, v i * v j * A r i j)
      atTop (𝓝 (∑ i, ∑ j, v i * v j * K i j)) := by
    apply tendsto_finsetSum
    intro i hi
    apply tendsto_finsetSum
    intro j hj
    exact tendsto_const_nhds.mul (hlim i j)
  exact ge_of_tendsto' hq (fun r => hpos r v)

/-- This is the Stieltjes condition: every nonnegative shift and every finite size. -/
def ShiftedHankelPSD (m : ℕ → ℝ) : Prop :=
  ∀ k n : ℕ, FinitePSD (fun i j : Fin n => m (k + i.val + j.val))

theorem shiftedHankelPSD_limit {m : ℕ → ℕ → ℝ} {M : ℕ → ℝ}
    (hlim : ∀ k, Tendsto (fun r => m r k) atTop (𝓝 (M k)))
    (hpos : ∀ r, ShiftedHankelPSD (m r)) : ShiftedHankelPSD M := by
  intro k n
  apply finitePSD_limit (A := fun (r : ℕ) (i j : Fin n) => m r (k + i.val + j.val))
  · intro i j
    exact hlim (k + i.val + j.val)
  · intro r
    exact hpos r k n

theorem hankel_pair {m : ℕ → ℝ} (h : ShiftedHankelPSD m) (k : ℕ) :
    PSD2 (m k) (m (k + 1)) (m (k + 2)) := by
  intro x y
  have hh := h k 2 (fun i : Fin 2 => if i.val = 0 then x else y)
  simp only [Fin.sum_univ_two] at hh
  norm_num [Nat.add_assoc] at hh
  nlinarith only [hh]

/-- Every finite shifted Hankel PSD condition entails the adjacent moment inequality. -/
theorem moment_log_convex {m : ℕ → ℝ} (h : ShiftedHankelPSD m) (k : ℕ) :
    m (k + 1) ^ 2 ≤ m k * m (k + 2) :=
  ((psd2_iff (m k) (m (k + 1)) (m (k + 2))).mp (hankel_pair h k)).2.2

theorem moment_nonneg {m : ℕ → ℝ} (h : ShiftedHankelPSD m) (k : ℕ) :
    0 ≤ m k :=
  ((psd2_iff (m k) (m (k + 1)) (m (k + 2))).mp (hankel_pair h k)).1

/-- Positive adjacent moments have increasing moment ratios. -/
theorem moment_ratio_monotone {m : ℕ → ℝ} (h : ShiftedHankelPSD m) (k : ℕ)
    (hk : 0 < m k) (hk1 : 0 < m (k + 1)) :
    m (k + 1) / m k ≤ m (k + 2) / m (k + 1) := by
  apply (div_le_div_iff₀ hk hk1).2
  simpa [pow_two, mul_comm] using moment_log_convex h k

/-- A violated moment determinant provides a two-coordinate negative witness. -/
theorem moment_determinant_negative_witness (m : ℕ → ℝ) (k : ℕ)
    (hd : m k * m (k + 2) - m (k + 1) ^ 2 < 0) :
    ∃ x y : ℝ, m k * x ^ 2 + 2 * m (k + 1) * x * y + m (k + 2) * y ^ 2 < 0 :=
  exists_negative_direction_of_det_neg hd

/--
Conditional derivative inequality.  Set `D n = S_a^(n)(0)` for the real
full-zero Gaussian trace.  The hypothesis is the precise finite shifted Hankel
PSD condition on its signed even derivatives; it is not assumed automatically.
-/
theorem signed_even_derivative_log_convex (D : ℕ → ℝ)
    (h : ShiftedHankelPSD (fun k => (-1 : ℝ) ^ k * D (2 * k))) (k : ℕ) :
    D (2 * (k + 1)) ^ 2 ≤ D (2 * k) * D (2 * (k + 2)) := by
  have hs : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  have hleft : ((-1 : ℝ) ^ (k + 1) * D (2 * (k + 1))) ^ 2 =
      D (2 * (k + 1)) ^ 2 := by
    simp [pow_add, mul_pow, hs]
  have hright : ((-1 : ℝ) ^ k * D (2 * k)) *
      ((-1 : ℝ) ^ (k + 2) * D (2 * (k + 2))) =
      D (2 * k) * D (2 * (k + 2)) := by
    calc
      _ = ((-1 : ℝ) ^ k) ^ 2 * (D (2 * k) * D (2 * (k + 2))) := by
        simp only [pow_add]
        norm_num
        ring
      _ = _ := by rw [hs, one_mul]
  have hh := moment_log_convex h k
  change ((-1 : ℝ) ^ (k + 1) * D (2 * (k + 1))) ^ 2 ≤
      ((-1 : ℝ) ^ k * D (2 * k)) *
      ((-1 : ℝ) ^ (k + 2) * D (2 * (k + 2))) at hh
  rwa [hleft, hright] at hh

def atomicMoment {α : Type*} (s : Finset α) (w x : α → ℝ) (k : ℕ) : ℝ :=
  ∑ r ∈ s, w r * x r ^ k

/-- Finite moments are a Gram form, with the full square retained. -/
theorem atomic_hankel_quadratic {α : Type*} (s : Finset α) (w x : α → ℝ)
    (k n : ℕ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * v j * atomicMoment s w x (k + i.val + j.val)) =
      ∑ r ∈ s, w r * x r ^ k * (∑ i, v i * x r ^ i.val) ^ 2 := by
  classical
  simp only [atomicMoment, Finset.mul_sum]
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ r ∈ s,
        v i * v j * (w r * x r ^ (k + i.val + j.val))) =
        ∑ i : Fin n, ∑ r ∈ s, ∑ j : Fin n,
          v i * v j * (w r * x r ^ (k + i.val + j.val)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ r ∈ s, ∑ i : Fin n, ∑ j : Fin n,
          v i * v j * (w r * x r ^ (k + i.val + j.val)) := Finset.sum_comm
    _ = ∑ r ∈ s, w r * x r ^ k * (∑ i : Fin n, v i * x r ^ i.val) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [pow_add, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Nonnegative nodes and weights give all finite shifted Hankel positivity. -/
theorem atomicMoment_shiftedHankelPSD {α : Type*} (s : Finset α) (w x : α → ℝ)
    (hw : ∀ r ∈ s, 0 ≤ w r) (hx : ∀ r ∈ s, 0 ≤ x r) :
    ShiftedHankelPSD (atomicMoment s w x) := by
  intro k n v
  rw [atomic_hankel_quadratic]
  exact Finset.sum_nonneg (fun r hr =>
    mul_nonneg (mul_nonneg (hw r hr) (pow_nonneg (hx r hr) k)) (sq_nonneg _))

/-- In particular, limits of finite positive atomic moments have log-convex moments. -/
theorem limiting_atomic_moments_log_convex {α : Type*}
    (s : ℕ → Finset α) (w x : α → ℝ) (M : ℕ → ℝ)
    (hw : ∀ r, 0 ≤ w r) (hx : ∀ r, 0 ≤ x r)
    (hlim : ∀ k, Tendsto (fun N => atomicMoment (s N) w x k) atTop (𝓝 (M k)))
    (k : ℕ) : M (k + 1) ^ 2 ≤ M k * M (k + 2) := by
  apply moment_log_convex (shiftedHankelPSD_limit hlim ?_) k
  intro N
  exact atomicMoment_shiftedHankelPSD (s N) w x (fun r _ => hw r) (fun r _ => hx r)

end RiemannResearch.Analysis.HankelMomentPositivity
