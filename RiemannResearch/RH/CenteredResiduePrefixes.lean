/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoResidueUniformCovariance
import RiemannResearch.Analysis.ReciprocalEnergyFromPrefix
import RiemannResearch.RH.ParetoDilation

/-!
# Exact centered residue primitives and signed Pareto tail cancellation

Source: user-provided RH_Centered_Far_Tail_and_Subpower_Obstruction_2026-09-24(1).md,
Part I, Sections 5--7, for the centered-prefix target and Abel application.
The discrete primitive proof is a direct algebraic derivation: its successive
difference is the centered normalized residue, and its range is [-d/8,0].
This supplies unconditional arithmetic prefix bounds for the actual Mobius
coefficients and proves summability before applying signed Abel transfer.
These are signed first-moment bounds; they do not bound the squared middle
energy required by the RH subpower criterion.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

def centeredResiduePrimitive (d k : ℕ) : ℝ :=
  residue d k * (residue d k - (d : ℝ)) / (2 * (d : ℝ))

theorem centeredResiduePrimitive_step (d k : ℕ) (hd : 0 < d) :
    centeredResiduePrimitive d (k+1) - centeredResiduePrimitive d k =
      (residue d k - ((d : ℝ)-1)/2) / (d : ℝ) := by
  by_cases hd1 : d = 1
  · subst d
    simp [centeredResiduePrimitive, residue, Nat.mod_one]
  have h1d : 1 < d := by omega
  have hr := Nat.mod_lt k hd
  have hmod : (k+1)%d = (k%d+1)%d := by
    rw [Nat.add_mod k 1 d, Nat.mod_eq_of_lt h1d]
  have hdR : (d : ℝ) ≠ 0 := by positivity
  by_cases he : k%d+1 = d
  · have heR : ((k%d : ℕ) : ℝ)+1 = (d : ℝ) := by exact_mod_cast he
    unfold centeredResiduePrimitive residue
    rw [hmod, he, Nat.mod_self]
    push_cast
    field_simp
    nlinarith
  · have hlt : k%d+1 < d := by omega
    unfold centeredResiduePrimitive residue
    rw [hmod, Nat.mod_eq_of_lt hlt]
    push_cast
    field_simp
    <;> ring

theorem centeredResiduePrimitive_bounds (d k : ℕ) (hd : 0 < d) :
    -(d : ℝ)/8 ≤ centeredResiduePrimitive d k ∧ centeredResiduePrimitive d k ≤ 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0 : 0 ≤ residue d k := by unfold residue; positivity
  have hr1 : residue d k ≤ (d : ℝ) := by
    unfold residue
    exact_mod_cast (Nat.mod_lt k hd).le
  unfold centeredResiduePrimitive
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2*(d : ℝ))).mpr
    nlinarith [sq_nonneg (residue d k-(d : ℝ)/2)]
  · exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hr0 (by linarith)) (by positivity)

theorem centeredResidue_prefix_eq (d K L : ℕ) (hd : 0 < d) :
    (∑ i ∈ Finset.range L,
      (residue d (K+i) - ((d : ℝ)-1)/2) / (d : ℝ)) =
      centeredResiduePrimitive d (K+L) - centeredResiduePrimitive d K := by
  simp_rw [← centeredResiduePrimitive_step d _ hd]
  simpa only [Nat.add_assoc, Nat.add_zero] using
    Finset.sum_range_sub (fun i => centeredResiduePrimitive d (K+i)) L

theorem centeredResidue_prefix_abs_le (d K L : ℕ) (hd : 0 < d) :
    |∑ i ∈ Finset.range L,
      (residue d (K+i) - ((d : ℝ)-1)/2) / (d : ℝ)| ≤ (d : ℝ)/8 := by
  rw [centeredResidue_prefix_eq d K L hd, abs_le]
  have h0 := centeredResiduePrimitive_bounds d K hd
  have h1 := centeredResiduePrimitive_bounds d (K+L) hd
  constructor <;> linarith

theorem centeredResidue_combination_prefix_abs_le
    (s : Finset ℕ) (c : ℕ → ℝ) (K L : ℕ) (hs : ∀ d ∈ s, 0 < d) :
    |∑ i ∈ Finset.range L, ∑ d ∈ s, c d *
      ((residue d (K+i)-((d : ℝ)-1)/2)/(d : ℝ))| ≤
      (∑ d ∈ s, |c d| *(d : ℝ))/8 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ d ∈ s, |c d *
        (∑ i ∈ Finset.range L, (residue d (K+i)-((d : ℝ)-1)/2)/(d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ s, |c d| *((d : ℝ)/8) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (centeredResidue_prefix_abs_le d K L (hs d hd))
        (abs_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv, Finset.sum_mul]; ring

theorem centeredMobius_prefix_abs_le (N K L : ℕ) :
    |∑ i ∈ Finset.range L, ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
      ((residue d (K+i)-((d : ℝ)-1)/2)/(d : ℝ))| ≤
      (∑ d ∈ Finset.Icc 1 N, |(ArithmeticFunction.moebius d : ℝ)| *(d : ℝ))/8 :=
  centeredResidue_combination_prefix_abs_le (Finset.Icc 1 N)
    (fun d => (ArithmeticFunction.moebius d : ℝ)) K L
    (fun _d hd => (Finset.mem_Icc.mp hd).1)


theorem centeredMobius_prefix_abs_le_quadratic (N K L : ℕ) :
    |∑ i ∈ Finset.range L, ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
      ((residue d (K+i)-((d : ℝ)-1)/2)/(d : ℝ))| ≤
      (N : ℝ)*((N : ℝ)+1)/16 := by
  have hmass : (∑ d ∈ Finset.Icc 1 N, |(ArithmeticFunction.moebius d : ℝ)| * (d : ℝ)) ≤
      (N : ℝ)*((N : ℝ)+1)/2 := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 N, (d : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
        simpa using mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg d : (0 : ℝ) ≤ _)
      _ = _ := by
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1), ih]
          push_cast
          ring
  have h := centeredMobius_prefix_abs_le N K L
  linarith


theorem centeredMobius_pareto_tail_abs_le (N K : ℕ) :
    |∑' i : ℕ, positiveWeight (i+(K+1)) *
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
        ((residue d (i+(K+1))-((d : ℝ)-1)/2)/(d : ℝ)))| ≤
      ((N : ℝ)*((N : ℝ)+1)/16) / (((K : ℝ)+1)*((K : ℝ)+2)) := by
  let P : ℝ := (N : ℝ)*((N : ℝ)+1)/16
  let a : ℕ → ℝ := fun i => ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
    ((residue d (i+(K+1))-((d : ℝ)-1)/2)/(d : ℝ))
  have hp (L : ℕ) : |∑ i ∈ Finset.range L, a i| ≤ P := by
    simpa only [a, P, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      centeredMobius_prefix_abs_le_quadratic N (K+1) L
  have ha (i : ℕ) : |a i| ≤ P := by
    simpa [a, P] using centeredMobius_prefix_abs_le_quadratic N (i+(K+1)) 1
  let f : ℕ → ℝ := fun i => a i / (((K : ℝ)+i+1)*((K : ℝ)+i+2))
  have hid (i : ℕ) : f i = positiveWeight (i+(K+1))*a i := by
    dsimp [f, positiveWeight]
    push_cast
    ring
  have hw := (summable_nat_add_iff (K+1)).mpr positiveWeight_summable
  have hf : Summable f := (hw.mul_right P).of_norm_bounded (fun i => by
    rw [hid, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (positiveWeight_nonneg _)]
    exact mul_le_mul_of_nonneg_left (ha i) (positiveWeight_nonneg _))
  have ht := RiemannResearch.Analysis.reciprocal_tsum_abs_le_of_abs_prefix
    a K P (Nat.cast_nonneg K) hp hf
  change |∑' i : ℕ, f i| ≤ _ at ht
  simp_rw [hid] at ht
  exact ht

end RiemannResearch.RH.Pareto
