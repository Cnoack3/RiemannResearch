/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeGridLimits
import RiemannResearch.RH.QPrimeCRTCarries
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Signed CRT lifts induce actual finite-grid permutations

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros*, 5 November
2026, §2.4. This identifies the `Int.fract` observable for signed lifts
with the grid permutation in the Haar limit theorem.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
namespace RiemannResearch.RH.PrimeTreeHaarRows

private def gridZModEquiv (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun x := (x.val : ZMod p)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv x := Fin.ext (ZMod.val_natCast_of_lt x.isLt)
  right_inv := ZMod.natCast_zmod_val

private def unitGridPerm (p : ℕ) [NeZero p] (u : (ZMod p)ˣ) : Equiv.Perm (Fin p) :=
  let m : Equiv.Perm (ZMod p) :=
    { toFun := fun x => (u : ZMod p) * x
      invFun := fun x => (↑(u⁻¹) : ZMod p) * x
      left_inv := fun x => by simp [← mul_assoc]
      right_inv := fun x => by simp [← mul_assoc] }
  (gridZModEquiv p).trans (m.trans (gridZModEquiv p).symm)

/-- The floor convention handles every signed lift, including negative ones. -/
theorem signed_lift_grid_permutation (p : ℕ) [NeZero p] (a : ℤ) (hu : IsUnit (a : ZMod p)) :
    ∃ e : Equiv.Perm (Fin p), ∀ x : Fin p,
      Int.fract ((a : ℝ) * (x.val : ℝ)/(p : ℝ)) = ((e x).val : ℝ)/(p : ℝ) := by
  refine ⟨unitGridPerm p hu.unit, ?_⟩
  intro x
  let z : ℤ := a * (x.val : ℤ)
  let r : ℕ := (z : ZMod p).val
  have he : (unitGridPerm p hu.unit x).val = r := by
    change ((hu.unit : ZMod p) * (x.val : ZMod p)).val = (z : ZMod p).val
    simp only [z, hu.unit_spec, Int.cast_mul, Int.cast_natCast]
  rw [he]
  have hpR : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hzr : (r : ℤ) + (p : ℤ) * (z / (p : ℤ)) = z := by
    rw [show (r : ℤ) = z % (p : ℤ) from ZMod.val_intCast z]
    exact Int.emod_add_mul_ediv z p
  apply Int.fract_eq_iff.mpr
  refine ⟨div_nonneg (Nat.cast_nonneg _) hpR.le,
    (div_lt_one hpR).mpr (by exact_mod_cast ZMod.val_lt (z : ZMod p)), z/(p : ℤ), ?_⟩
  have hzR : (r : ℝ) + (p : ℝ) * ((z/(p : ℤ) : ℤ) : ℝ) = (a : ℝ)*(x.val : ℝ) := by
    exact_mod_cast hzr
  field_simp [hpR.ne']
  linarith only [hzR]

/-- Every representative from the complete real-lift classification gives an
invertible element on its prime grid. -/
theorem unit_of_canonical_lift (d p : ℕ) (hsf : Squarefree d) (hp : p.Prime) (hpd : p ∣ d)
    (t : ℤ) : IsUnit (((QPrimeCRTCarries.canonicalCoefficient d p : ℤ) + (p : ℤ)*t : ℤ) : ZMod p) := by
  have h := QPrimeCRTCarries.canonicalCoefficient_inverse d p hsf hp hpd
  have hu := IsUnit.of_mul_eq_one_right _ h
  simpa using hu

/-- The a.s. limit for the paper's signed fractional parts with arbitrary
integral unit coefficients, one test at a time. -/
theorem signed_grid_average_ae (p : ℕ → ℕ) [∀ j, NeZero (p j)]
    (hp : Tendsto p atTop atTop) (a : ℕ → ℕ → ℤ)
    (ha : ∀ n j, IsUnit (a n j : ZMod (p j))) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) :
    ∀ᵐ ω ∂Measure.infinitePi (fun j => gridLaw (p j)), Tendsto
      (fun n : ℕ => (∑ j ∈ Finset.range n,
        f (Int.fract ((a n j : ℝ) * ((ω j).val : ℝ)/(p j))))/(n : ℝ))
      atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  choose e he using fun n j => signed_lift_grid_permutation (p j) (a n j) (ha n j)
  simpa only [he] using permuted_grid_average_ae p hp e f hf

private theorem floor_div_tendsto (S : ℕ → ℝ) (L : ℝ)
    (hs : Tendsto (fun n : ℕ => S n / n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => (⌊S n⌋ : ℝ)/n) atTop (𝓝 L) := by
  have hl : Tendsto (fun n : ℕ => S n/n - 1/n) atTop (𝓝 L) := by
    simpa using hs.sub (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hs
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith [Int.lt_floor_add_one (S n)]) (Nat.cast_nonneg n)
  · exact Eventually.of_forall fun n => div_le_div_of_nonneg_right (Int.floor_le _) (Nat.cast_nonneg n)

def reducedGridSum (p : ℕ → ℕ) (a : ℕ → ℕ → ℤ) (n : ℕ) (ω : ∀ j, Fin (p j)) : ℝ :=
  ∑ j ∈ Finset.range n, Int.fract ((a n j : ℝ) * ((ω j).val : ℝ)/(p j))

/-- The reduced signed CRT carry divided by depth tends a.s. to one half. -/
theorem reducedGridCarry_ae_half (p : ℕ → ℕ) [∀ j, NeZero (p j)]
    (hp : Tendsto p atTop atTop) (a : ℕ → ℕ → ℤ) (ha : ∀ n j, IsUnit (a n j : ZMod (p j))) :
    ∀ᵐ ω ∂Measure.infinitePi (fun j => gridLaw (p j)), Tendsto
      (fun n : ℕ => (⌊reducedGridSum p a n ω⌋ : ℝ)/n) atTop (𝓝 (1/2)) := by
  filter_upwards [signed_grid_average_ae p hp a ha (fun x => x) continuous_id.continuousOn] with ω hω
  apply floor_div_tendsto
  norm_num at hω
  exact hω

/-- The same reduced floor-carry limit in squared Haar mean. -/
theorem reducedGridCarry_meanSquare_half (p : ℕ → ℕ) [∀ j, NeZero (p j)]
    (hp : Tendsto p atTop atTop) (a : ℕ → ℕ → ℤ) (ha : ∀ n j, IsUnit (a n j : ZMod (p j))) :
    Tendsto (fun n : ℕ => ∫ ω, ((⌊reducedGridSum p a n ω⌋ : ℝ)/n - 1/2)^2
      ∂Measure.infinitePi (fun j => gridLaw (p j))) atTop (𝓝 0) := by
  let H := Measure.infinitePi (fun j => gridLaw (p j))
  let F := fun (n : ℕ) (ω : ∀ j, Fin (p j)) => (⌊reducedGridSum p a n ω⌋ : ℝ)/n
  have hm (n : ℕ) : Measurable (F n) := by
    have hs : Measurable (reducedGridSum p a n) := by
      apply Finset.measurable_fun_sum
      intro j _
      exact (measurable_of_countable (fun x : Fin (p j) => Int.fract ((a n j : ℝ) * (x.val : ℝ)/(p j)))).comp
        (measurable_pi_apply j)
    exact ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (Int.measurable_floor.comp hs)).div_const _
  have hbound (n : ℕ) : ∀ᵐ ω ∂H, ‖(F n ω-1/2)^2‖ ≤ 1 := by
    apply ae_of_all
    intro ω
    have hS0 : 0 ≤ reducedGridSum p a n ω := Finset.sum_nonneg (fun _ _ => Int.fract_nonneg _)
    have hS1 : reducedGridSum p a n ω ≤ n := calc
      _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun _ _ => (Int.fract_lt_one _).le
      _ = _ := by simp
    have hF0 : 0 ≤ F n ω := div_nonneg (by exact_mod_cast Int.floor_nonneg.mpr hS0) (Nat.cast_nonneg n)
    have hF1 : F n ω ≤ 1 := by
      rcases n.eq_zero_or_pos with rfl | hn
      · simp [F]
      · exact (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).mpr ((Int.floor_le _).trans hS1)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_nonneg hF0 (sub_nonneg.mpr hF1)]
  have hlim : ∀ᵐ ω ∂H, Tendsto (fun n => (F n ω-1/2)^2) atTop (𝓝 0) := by
    filter_upwards [reducedGridCarry_ae_half p hp a ha] with ω hω
    simpa using ((show Tendsto (fun n => F n ω) atTop (𝓝 (1/2)) from hω).sub_const (1/2)).pow 2
  simpa using (tendsto_integral_of_dominated_convergence (μ := H)
    (F := fun n ω => (F n ω-1/2)^2) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun n => ((hm n).sub_const (1/2) |>.pow_const 2).aestronglyMeasurable)
    (integrable_const _) hbound hlim)

end RiemannResearch.RH.PrimeTreeHaarRows
