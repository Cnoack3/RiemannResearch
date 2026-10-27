/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Gap-one tensorization for commuting averaging projections

Source: the countable prime-resampling Poincare proof in the user-supplied
PrimeResamplingResearch20261027.md agenda. The finite-dimensional estimate
is purely Hilbert-space algebra. Actual prime averaging, its commutation,
and convergence to the mean are separate arithmetic providers.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.CommutingProjectionEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Sequential averaging of the first `n` coordinates. -/
def prefixAverage (P : ℕ → E →L[ℝ] E) : ℕ → E →L[ℝ] E
  | 0 => ContinuousLinearMap.id ℝ E
  | n + 1 => (P n).comp (prefixAverage P n)

@[simp] theorem prefixAverage_zero (P : ℕ → E →L[ℝ] E) (x : E) :
    prefixAverage P 0 x = x := rfl

@[simp] theorem prefixAverage_succ (P : ℕ → E →L[ℝ] E) (n : ℕ) (x : E) :
    prefixAverage P (n + 1) x = P n (prefixAverage P n x) := rfl

theorem prefixAverage_norm_le (P : ℕ → E →L[ℝ] E)
    (hcontract : ∀ i x, ‖P i x‖ ≤ ‖x‖) (n : ℕ) (x : E) :
    ‖prefixAverage P n x‖ ≤ ‖x‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (hcontract n (prefixAverage P n x)).trans ih

theorem prefixAverage_commute (P : ℕ → E →L[ℝ] E)
    (hcomm : ∀ i j x, P i (P j x) = P j (P i x))
    (n i : ℕ) (x : E) :
    P i (prefixAverage P n x) = prefixAverage P n (P i x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [prefixAverage_succ, prefixAverage_succ, hcomm i n, ih]

/-- Averaging other coordinates cannot increase one coordinate's defect. -/
theorem prefixAverage_defect_norm_le (P : ℕ → E →L[ℝ] E)
    (hcontract : ∀ i x, ‖P i x‖ ≤ ‖x‖)
    (hcomm : ∀ i j x, P i (P j x) = P j (P i x))
    (n i : ℕ) (x : E) :
    ‖prefixAverage P n x - P i (prefixAverage P n x)‖ ≤ ‖x - P i x‖ := by
  rw [prefixAverage_commute P hcomm, ← map_sub]
  exact prefixAverage_norm_le P hcontract n (x - P i x)

/-- Finite-product Efron--Stein inequality with exact constant one.
The Pythagorean identity and contraction are satisfied by orthogonal
conditional-expectation projections. -/
theorem norm_sq_sub_prefixAverage_norm_sq_le (P : ℕ → E →L[ℝ] E)
    (hcontract : ∀ i x, ‖P i x‖ ≤ ‖x‖)
    (hpyth : ∀ i x, ‖x‖ ^ 2 = ‖P i x‖ ^ 2 + ‖x - P i x‖ ^ 2)
    (hcomm : ∀ i j x, P i (P j x) = P j (P i x))
    (n : ℕ) (x : E) :
    ‖x‖ ^ 2 - ‖prefixAverage P n x‖ ^ 2 ≤
      ∑ i ∈ Finset.range n, ‖x - P i x‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [prefixAverage_succ, Finset.sum_range_succ]
      have he := hpyth n (prefixAverage P n x)
      have hn := prefixAverage_defect_norm_le P hcontract hcomm n n x
      have hsq : ‖prefixAverage P n x - P n (prefixAverage P n x)‖ ^ 2 ≤
          ‖x - P n x‖ ^ 2 := by
        nlinarith [norm_nonneg (prefixAverage P n x - P n (prefixAverage P n x)),
          norm_nonneg (x - P n x)]
      linarith

/-- Any uniform bound on the finite defect sums passes to the limiting
average, preserving the sharp constant. -/
theorem norm_sq_sub_limit_norm_sq_le (P : ℕ → E →L[ℝ] E)
    (hcontract : ∀ i x, ‖P i x‖ ≤ ‖x‖)
    (hpyth : ∀ i x, ‖x‖ ^ 2 = ‖P i x‖ ^ 2 + ‖x - P i x‖ ^ 2)
    (hcomm : ∀ i j x, P i (P j x) = P j (P i x))
    (x c : E) (hlim : Tendsto (fun n => prefixAverage P n x) atTop (𝓝 c))
    (D : ℝ) (hD : ∀ n, (∑ i ∈ Finset.range n, ‖x - P i x‖ ^ 2) ≤ D) :
    ‖x‖ ^ 2 - ‖c‖ ^ 2 ≤ D := by
  have ht : Tendsto (fun n => ‖x‖ ^ 2 - ‖prefixAverage P n x‖ ^ 2)
      atTop (𝓝 (‖x‖ ^ 2 - ‖c‖ ^ 2)) := tendsto_const_nhds.sub (hlim.norm.pow 2)
  apply le_of_tendsto ht
  exact Eventually.of_forall (fun n =>
    (norm_sq_sub_prefixAverage_norm_sq_le P hcontract hpyth hcomm n x).trans (hD n))

/-- Countable gap-one inequality when the nonnegative defect series is
summable. The extended-real nonsummable case is automatically infinite. -/
theorem norm_sq_sub_limit_norm_sq_le_tsum (P : ℕ → E →L[ℝ] E)
    (hcontract : ∀ i x, ‖P i x‖ ≤ ‖x‖)
    (hpyth : ∀ i x, ‖x‖ ^ 2 = ‖P i x‖ ^ 2 + ‖x - P i x‖ ^ 2)
    (hcomm : ∀ i j x, P i (P j x) = P j (P i x))
    (x c : E) (hlim : Tendsto (fun n => prefixAverage P n x) atTop (𝓝 c))
    (hs : Summable (fun i => ‖x - P i x‖ ^ 2)) :
    ‖x‖ ^ 2 - ‖c‖ ^ 2 ≤ ∑' i : ℕ, ‖x - P i x‖ ^ 2 := by
  apply norm_sq_sub_limit_norm_sq_le P hcontract hpyth hcomm x c hlim
  intro n
  exact Summable.sum_le_tsum (Finset.range n) (fun i hi => sq_nonneg _) hs

/-- The finite intersection of the first invariant subspaces. -/
def prefixSpace (K : ℕ → Submodule ℝ E) : ℕ → Submodule ℝ E
  | 0 => ⊤
  | n + 1 => prefixSpace K n ⊓ K n

theorem mem_prefixSpace (K : ℕ → Submodule ℝ E) (n : ℕ) (x : E) :
    x ∈ prefixSpace K n ↔ ∀ i < n, x ∈ K i := by
  induction n with
  | zero => simp [prefixSpace]
  | succ n ih =>
      change (x ∈ prefixSpace K n ∧ x ∈ K n) ↔ ∀ i < n + 1, x ∈ K i
      rw [ih]
      constructor
      · rintro ⟨hprev, hlast⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
        · exact hprev i hi
        · subst i; exact hlast
      · intro h
        exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem prefixSpace_antitone (K : ℕ → Submodule ℝ E) : Antitone (prefixSpace K) := by
  intro m n hmn x hx
  rw [mem_prefixSpace] at hx ⊢
  intro i hi
  exact hx i (hi.trans_le hmn)

theorem iInf_prefixSpace_eq_iInf (K : ℕ → Submodule ℝ E) :
    (⨅ n, prefixSpace K n) = ⨅ i, K i := by
  ext x
  simp only [Submodule.mem_iInf, mem_prefixSpace]
  constructor
  · intro h i
    exact h (i + 1) i (Nat.lt_succ_self i)
  · intro h n i hi
    exact h i

section Submodules
variable (K : ℕ → Submodule ℝ E) [∀ i, (K i).HasOrthogonalProjection]

theorem prefixAverage_mem_prefixSpace
    (hcomm : ∀ i j x, (K i).starProjection ((K j).starProjection x) =
      (K j).starProjection ((K i).starProjection x))
    (n : ℕ) (x : E) :
    prefixAverage (fun i => (K i).starProjection) n x ∈ prefixSpace K n := by
  induction n generalizing x with
  | zero => exact Submodule.mem_top
  | succ n ih =>
      change (K n).starProjection
        (prefixAverage (fun i => (K i).starProjection) n x) ∈ prefixSpace K n ⊓ K n
      constructor
      · rw [prefixAverage_commute (fun i => (K i).starProjection) hcomm n n]
        exact ih _
      · exact (K n).starProjection_apply_mem _

theorem prefixAverage_residual_inner_zero (n : ℕ) (x z : E)
    (hz : z ∈ prefixSpace K n) :
    inner ℝ (x - prefixAverage (fun i => (K i).starProjection) n x) z = 0 := by
  induction n generalizing x z with
  | zero => simp
  | succ n ih =>
      have hz' : z ∈ prefixSpace K n ⊓ K n := hz
      rw [prefixAverage_succ]
      have he : x - (K n).starProjection
          (prefixAverage (fun i => (K i).starProjection) n x) =
          (x - prefixAverage (fun i => (K i).starProjection) n x) +
            (prefixAverage (fun i => (K i).starProjection) n x -
              (K n).starProjection
                (prefixAverage (fun i => (K i).starProjection) n x)) := by abel
      rw [he, inner_add_left, ih x z hz'.1,
        Submodule.starProjection_inner_eq_zero _ z hz'.2, add_zero]

theorem prefixAverage_residual_mem_orthogonal (n : ℕ) (x : E) :
    x - prefixAverage (fun i => (K i).starProjection) n x ∈ (prefixSpace K n)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro z hz
  rw [real_inner_comm]
  exact prefixAverage_residual_inner_zero K n x z hz

/-- Commutativity provides the projection onto every finite intersection,
even without an ambient completeness assumption. -/
theorem prefixSpace_hasOrthogonalProjection
    (hcomm : ∀ i j x, (K i).starProjection ((K j).starProjection x) =
      (K j).starProjection ((K i).starProjection x))
    (n : ℕ) : (prefixSpace K n).HasOrthogonalProjection := by
  constructor
  intro x
  exact ⟨prefixAverage (fun i => (K i).starProjection) n x,
    prefixAverage_mem_prefixSpace K hcomm n x,
    prefixAverage_residual_mem_orthogonal K n x⟩

theorem prefixAverage_eq_starProjection
    (hcomm : ∀ i j x, (K i).starProjection ((K j).starProjection x) =
      (K j).starProjection ((K i).starProjection x))
    (n : ℕ) [(prefixSpace K n).HasOrthogonalProjection] (x : E) :
    prefixAverage (fun i => (K i).starProjection) n x =
      (prefixSpace K n).starProjection x := by
  have hm := prefixAverage_mem_prefixSpace K hcomm n x
  have hz := (prefixSpace K n).starProjection_apply_eq_zero_iff.mpr
    (prefixAverage_residual_mem_orthogonal K n x)
  rw [map_sub, Submodule.starProjection_eq_self_iff.mpr hm] at hz
  exact (sub_eq_zero.mp hz).symm

/-- Finite-intersection form of the sharp tensorization inequality. -/
theorem norm_sq_sub_prefixSpace_projection_norm_sq_le
    (hcomm : ∀ i j x, (K i).starProjection ((K j).starProjection x) =
      (K j).starProjection ((K i).starProjection x))
    (n : ℕ) [(prefixSpace K n).HasOrthogonalProjection] (x : E) :
    ‖x‖ ^ 2 - ‖(prefixSpace K n).starProjection x‖ ^ 2 ≤
      ∑ i ∈ Finset.range n, ‖x - (K i).starProjection x‖ ^ 2 := by
  rw [← prefixAverage_eq_starProjection K hcomm n x]
  apply norm_sq_sub_prefixAverage_norm_sq_le
  · intro i y
    calc
      _ ≤ ‖(K i).starProjection‖ * ‖y‖ := (K i).starProjection.le_opNorm y
      _ ≤ ‖y‖ := by
        simpa using mul_le_mul_of_nonneg_right
          (Submodule.starProjection_norm_le (K i)) (norm_nonneg y)
  · intro i y
    simpa only [Submodule.starProjection_orthogonal_val] using
      Submodule.norm_sq_eq_add_norm_sq_starProjection y (K i)
  · exact hcomm

end Submodules

end RiemannResearch.Analysis.CommutingProjectionEnergy
