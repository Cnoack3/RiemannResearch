/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeGridLaw
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Mean-square and simultaneous continuous-test limits of prime CRT grids

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros*, 5 November
2026, §2.4. A single full-measure event works for all continuous tests on
the closed unit interval by separability of the continuous-function space.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
namespace RiemannResearch.RH.PrimeTreeHaarRows

private theorem abs_row_average_le {n : ℕ} (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ j < n, |a j| ≤ C) : |(∑ j ∈ Finset.range n, a j)/(n : ℝ)| ≤ C := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa using hC
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [abs_div, abs_of_pos hnR, div_le_iff₀ hnR]
    calc
      _ ≤ ∑ j ∈ Finset.range n, |a j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range n, C := Finset.sum_le_sum fun j hj => h j (Finset.mem_range.mp hj)
      _ = _ := by simp [mul_comm]

/-- The mean square of the error goes to zero under the actual product law. -/
theorem permuted_grid_average_meanSquare (p : ℕ → ℕ) [∀ j, NeZero (p j)]
    (hp : Tendsto p atTop atTop) (e : ∀ n j : ℕ, Equiv.Perm (Fin (p j)))
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun n : ℕ => ∫ ω, ((∑ j ∈ Finset.range n,
      f (((e n j (ω j)).val : ℝ)/(p j)))/(n : ℝ) - ∫ x in (0 : ℝ)..1, f x)^2
      ∂Measure.infinitePi (fun j => gridLaw (p j))) atTop (𝓝 0) := by
  let H := Measure.infinitePi (fun j => gridLaw (p j))
  let A := fun (n : ℕ) (ω : ∀ j, Fin (p j)) => (∑ j ∈ Finset.range n,
    f (((e n j (ω j)).val : ℝ)/(p j)))/(n : ℝ)
  let I := ∫ x in (0 : ℝ)..1, f x
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  have hA (n : ℕ) (ω : ∀ j, Fin (p j)) : |A n ω| ≤ C := by
    apply abs_row_average_le _ _ hC0
    intro j _
    have hpR : 0 < (p j : ℝ) := by exact_mod_cast NeZero.pos (p j)
    exact hC _ ⟨div_nonneg (Nat.cast_nonneg _) hpR.le,
      (div_le_one hpR).mpr (by exact_mod_cast (e n j (ω j)).isLt.le)⟩
  have hm (n : ℕ) : Measurable (A n) := by
    apply Measurable.div_const
    apply Finset.measurable_fun_sum
    intro j _
    exact (measurable_of_countable (fun x : Fin (p j) => f (((e n j x).val : ℝ)/(p j)))).comp
      (measurable_pi_apply j)
  have hlim : ∀ᵐ ω ∂H, Tendsto (fun n => (A n ω-I)^2) atTop (𝓝 0) := by
    filter_upwards [permuted_grid_average_ae p hp e f hf] with ω hω
    simpa using ((show Tendsto (fun n => A n ω) atTop (𝓝 I) from hω).sub_const I).pow 2
  have hbound (n : ℕ) : ∀ᵐ ω ∂H, ‖(A n ω-I)^2‖ ≤ (C+|I|)^2 := by
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub (A n ω) I).trans (add_le_add (hA n ω) (le_refl |I|))) 2
  simpa using (tendsto_integral_of_dominated_convergence (μ := H)
    (F := fun n ω => (A n ω-I)^2) (f := fun _ => (0 : ℝ)) (fun _ => (C+|I|)^2)
    (fun n => ((hm n).sub_const I |>.pow_const 2).aestronglyMeasurable)
    (integrable_const _) hbound hlim)

private def extendGridTest (f : C(Set.Icc (0 : ℝ) 1, ℝ)) (x : ℝ) : ℝ :=
  f (Set.projIcc 0 1 zero_le_one x)

private theorem extendGridTest_continuous (f : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    Continuous (extendGridTest f) := f.continuous.comp continuous_projIcc

/-- A common full Haar measure event for every continuous test on [0,1].
`extendGridTest` is the constant extension outside the two endpoints. -/
theorem permuted_grid_average_ae_all (p : ℕ → ℕ) [∀ j, NeZero (p j)]
    (hp : Tendsto p atTop atTop) (e : ∀ n j : ℕ, Equiv.Perm (Fin (p j))) :
    ∀ᵐ ω ∂Measure.infinitePi (fun j => gridLaw (p j)), ∀ f : C(Set.Icc (0 : ℝ) 1, ℝ), Tendsto
      (fun n : ℕ => (∑ j ∈ Finset.range n, extendGridTest f (((e n j (ω j)).val : ℝ)/(p j)))/(n : ℝ))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, extendGridTest f x)) := by
  let T := C(Set.Icc (0 : ℝ) 1, ℝ)
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq T
  have htest := fun i => permuted_grid_average_ae p hp e (extendGridTest (u i))
    (extendGridTest_continuous (u i)).continuousOn
  filter_upwards [ae_all_iff.2 htest] with ω hω
  intro f
  let A := fun (n : ℕ) (g : T) => (∑ j ∈ Finset.range n,
    extendGridTest g (((e n j (ω j)).val : ℝ)/(p j))) / (n : ℝ)
  let I := fun g : T => ∫ x in (0 : ℝ)..1, extendGridTest g x
  have hpoint (g : T) (x : ℝ) : |extendGridTest f x-extendGridTest g x| ≤ dist f g :=
    by simpa only [extendGridTest, Real.dist_eq] using
      (ContinuousMap.dist_apply_le_dist (f := f) (g := g) (Set.projIcc 0 1 zero_le_one x))
  have hA (n : ℕ) (g : T) : dist (A n f) (A n g) ≤ dist f g := by
    rw [Real.dist_eq]
    simp only [A, ← sub_div, ← Finset.sum_sub_distrib]
    exact abs_row_average_le _ _ dist_nonneg (fun _ _ => hpoint g _)
  have hI (g : T) : dist (I f) (I g) ≤ dist f g := by
    rw [Real.dist_eq]
    change |(∫ x in (0 : ℝ)..1, extendGridTest f x) - ∫ x in (0 : ℝ)..1, extendGridTest g x| ≤ _
    rw [← intervalIntegral.integral_sub ((extendGridTest_continuous f).intervalIntegrable _ _)
      ((extendGridTest_continuous g).intervalIntegrable _ _)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun x => extendGridTest f x-extendGridTest g x) (C := dist f g) (fun x _ => hpoint g x)
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using h
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨i, hi⟩ := hu.exists_dist_lt f (by positivity : 0 < ε/3)
  have hv := Metric.tendsto_nhds.mp (hω i) (ε/3) (by positivity)
  filter_upwards [hv] with n hn
  change dist (A n f) (I f) < ε
  have h1 := dist_triangle (A n f) (A n (u i)) (I f)
  have h2 := dist_triangle (A n (u i)) (I (u i)) (I f)
  have hin := hI (u i)
  rw [dist_comm] at hin
  change dist (A n (u i)) (I (u i)) < ε/3 at hn
  linarith [hA n (u i)]

end RiemannResearch.RH.PrimeTreeHaarRows
