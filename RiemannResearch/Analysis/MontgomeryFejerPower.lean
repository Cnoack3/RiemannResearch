/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryFejerCertificate
import RiemannResearch.Analysis.MontgomeryIntervalIdentity
import RiemannResearch.Analysis.OrdinateTriangularIntegral
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Iterated triangular averaging and the absolute Fejér certificate

Montgomery (1973), Equation (3), uses a Fourier test to evaluate a weighted
sum of gaps (https://public.websites.umich.edu/~hlm/paircor1.pdf).
Convolution powers of the triangle retain the same equal-ordinate atom.
Each iteration multiplies a nonzero gap by another sinc square. The
frequency interval used by the iterated test has radius at most the
number of iterations times the single-step radius.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open MontgomeryPoisson

/-- Apply the normalized Fourier triangle at a translated center. -/
def fejerTriangleStep (R : ℝ) (f : ℝ → ℝ) (α : ℝ) : ℝ :=
  (1 / R) * ∫ u in (-R)..R, (1 - |u| / R) * f (α + u)

def iteratedFejerTriangle (R : ℝ) (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | n + 1 => fejerTriangleStep R (iteratedFejerTriangle R f n)

/-- The nth test at α depends on the input only in the stated frequency band. -/
theorem iteratedFejerTriangle_eq_of_eqOn {R : ℝ} (hR : 0 ≤ R) {f g : ℝ → ℝ}
    (n : ℕ) (α : ℝ) (h : EqOn f g (Icc (α - n * R) (α + n * R))) :
    iteratedFejerTriangle R f n α = iteratedFejerTriangle R g n α := by
  induction n generalizing α with
  | zero =>
      apply h
      simp
  | succ n ih =>
      simp only [iteratedFejerTriangle, fejerTriangleStep]
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (show -R ≤ R by linarith only [hR])] at hu
      change (1 - |u| / R) * iteratedFejerTriangle R f n (α + u) =
        (1 - |u| / R) * iteratedFejerTriangle R g n (α + u)
      apply congrArg (fun x : ℝ => (1 - |u| / R) * x)
      apply ih
      intro x hx
      apply h
      rw [mem_Icc] at hx ⊢
      push_cast
      exact ⟨by nlinarith only [hu.1, hx.1], by nlinarith only [hu.2, hx.2]⟩

theorem fejerTriangleStep_cosine {R : ℝ} (hR : 0 < R) (v α : ℝ) :
    fejerTriangleStep R (fun x => Real.cos (v * x)) α =
      sincSquared R v * Real.cos (v * α) := by
  let c : ℝ → ℝ := fun u => (1 - |u| / R) * Real.cos (v * u)
  let s : ℝ → ℝ := fun u => (1 - |u| / R) * Real.sin (v * u)
  have hc : Continuous c := by dsimp [c]; fun_prop
  have hs : Continuous s := by dsimp [s]; fun_prop
  have hodd (u : ℝ) : s (-u) = -s u := by simp only [s, abs_neg, mul_neg, Real.sin_neg]
  have hS : (∫ u in (-R)..R, s u) = 0 := by
    have hh := intervalIntegral.integral_comp_neg (f := s) (a := -R) (b := R)
    simp only [hodd, neg_neg, intervalIntegral.integral_neg] at hh
    linarith only [hh]
  have hsplit (u : ℝ) :
      (1 - |u| / R) * Real.cos (v * (α + u)) =
        c u * Real.cos (v * α) - s u * Real.sin (v * α) := by
    dsimp only [c, s]
    rw [mul_add, Real.cos_add]
    ring
  unfold fejerTriangleStep
  simp_rw [hsplit]
  rw [intervalIntegral.integral_sub ((hc.mul_const _).intervalIntegrable (-R) R)
    ((hs.mul_const _).intervalIntegrable (-R) R),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, hS,
    zero_mul, sub_zero, ← mul_assoc]
  exact congrArg (fun x : ℝ => x * Real.cos (v * α)) (triangular_cos_transform hR v)

private theorem fejerTriangleStep_cosSeries {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    (a v : ι → ℝ) (α : ℝ) :
    fejerTriangleStep R (fun x => ∑ i, a i * Real.cos (v i * x)) α =
      ∑ i, (a i * sincSquared R (v i)) * Real.cos (v i * α) := by
  let g (i : ι) (u : ℝ) := (1 - |u| / R) * (a i * Real.cos (v i * (α + u)))
  have hg (i : ι) : Continuous (g i) := by dsimp [g]; fun_prop
  unfold fejerTriangleStep
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (hg i).intervalIntegrable (-R) R)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (1 / R) * (∫ u in (-R)..R, g i u) = _
  have heq : g i = fun u => a i * ((1 - |u| / R) * Real.cos (v i * (α + u))) := by
    funext u
    dsimp [g]
    ring
  rw [heq, intervalIntegral.integral_const_mul, mul_left_comm]
  change a i * fejerTriangleStep R (fun x => Real.cos (v i * x)) α = _
  rw [fejerTriangleStep_cosine hR, ← mul_assoc]

theorem iteratedFejerTriangle_cosSeries {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    (a v : ι → ℝ) (n : ℕ) :
    iteratedFejerTriangle R (fun x => ∑ i, a i * Real.cos (v i * x)) n =
      fun x => ∑ i, (a i * sincSquared R (v i) ^ n) * Real.cos (v i * x) := by
  induction n with
  | zero =>
      funext x
      simp [iteratedFejerTriangle]
  | succ n ih =>
      funext x
      rw [iteratedFejerTriangle, ih, fejerTriangleStep_cosSeries hR]
      simp_rw [pow_succ, mul_assoc]

/-- The nth normalized Fourier triangle convolution, evaluated at frequency zero. -/
def fejerPowerFormFactor (T R : ℝ) (n : ℕ) : ℝ :=
  iteratedFejerTriangle R (formFactor T) n 0

@[simp] theorem fejerPowerFormFactor_one (T R : ℝ) :
    fejerPowerFormFactor T R 1 = fejerFormFactor T R := by
  simp [fejerPowerFormFactor, iteratedFejerTriangle, fejerTriangleStep, fejerFormFactor]

private theorem formFactor_eq_pair_cosSeries (T : ℝ) :
    formFactor T = fun α => ∑ p : Copies T × Copies T,
      (cauchyWeight (copyOrdinate T p.1 - copyOrdinate T p.2) /
        (T * Real.log T / (2 * Real.pi))) *
      Real.cos ((Real.log T * (copyOrdinate T p.1 - copyOrdinate T p.2)) * α) := by
  funext α
  unfold formFactor
  rw [pairSum_re_cos, Fintype.sum_prod_type]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show α * Real.log T * (copyOrdinate T i - copyOrdinate T j) =
    Real.log T * (copyOrdinate T i - copyOrdinate T j) * α by ring]
  ring

/-- A translated frequency triangle is bounded above by the centered one:
every coefficient of the finite cosine series after the triangle test
is nonnegative. -/
theorem fejerTriangleStep_formFactor_le_fejerFormFactor {T R : ℝ}
    (hT : 1 < T) (hR : 0 < R) (α : ℝ) :
    fejerTriangleStep R (formFactor T) α ≤ fejerFormFactor T R := by
  rw [← fejerPowerFormFactor_one, fejerPowerFormFactor]
  change iteratedFejerTriangle R (formFactor T) 1 α ≤
    iteratedFejerTriangle R (formFactor T) 1 0
  rw [formFactor_eq_pair_cosSeries, iteratedFejerTriangle_cosSeries hR]
  simp only [pow_one, mul_zero, Real.cos_zero, mul_one]
  have hnorm : 0 < T * Real.log T / (2 * Real.pi) :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  apply Finset.sum_le_sum
  intro p _
  exact mul_le_of_le_one_right
    (mul_nonneg (div_nonneg (by unfold cauchyWeight; positivity) hnorm.le)
      (sincSquared_nonneg _ _)) (Real.cos_le_one _)

theorem fejerPowerFormFactor_eq_kernelEnergy (T : ℝ) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    fejerPowerFormFactor T R n =
      kernelEnergy (copyOrdinate T) (fun d => cauchyWeight d *
        sincSquared R (Real.log T * d) ^ n) / (T * Real.log T / (2 * Real.pi)) := by
  unfold fejerPowerFormFactor
  rw [formFactor_eq_pair_cosSeries, iteratedFejerTriangle_cosSeries hR]
  simp only [mul_zero, Real.cos_zero, mul_one, Fintype.sum_prod_type, kernelEnergy,
    div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def fejerPowerNonzeroGapRemainder (T R : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ i : Copies T, ∑ j : Copies T, if copyOrdinate T i = copyOrdinate T j then 0 else
    cauchyWeight (copyOrdinate T i - copyOrdinate T j) *
      sincSquared R (Real.log T * (copyOrdinate T i - copyOrdinate T j)) ^ n

theorem fejerPowerNonzeroGapRemainder_nonneg (T R : ℝ) (n : ℕ) :
    0 ≤ fejerPowerNonzeroGapRemainder T R n := by
  classical
  unfold fejerPowerNonzeroGapRemainder
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by unfold cauchyWeight; positivity)
      (pow_nonneg (sincSquared_nonneg _ _) _)

theorem normalized_fejerPower_sub_analytic_eq {T R : ℝ}
    (hT : 1 < T) (hR : 0 < R) (n : ℕ) :
    (T * Real.log T / (2 * Real.pi)) * fejerPowerFormFactor T R n - (analyticPairCount T : ℝ) =
      (distinctZeroCollision T : ℝ) + fejerPowerNonzeroGapRemainder T R n := by
  classical
  let D := T * Real.log T / (2 * Real.pi)
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hC :
      D * fejerPowerFormFactor T R n =
        (actualCollision T : ℝ) + fejerPowerNonzeroGapRemainder T R n := by
    rw [fejerPowerFormFactor_eq_kernelEnergy T hR]
    change D * (_ / D) = _
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hD.ne']
    unfold kernelEnergy actualCollision occurrenceCollision fejerPowerNonzeroGapRemainder
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : copyOrdinate T i = copyOrdinate T j
    · simp [hij, cauchyWeight]
    · simp [hij]
  change D * fejerPowerFormFactor T R n - (analyticPairCount T : ℝ) = _
  rw [hC, collision_eq_analytic_add_distinctZeroCollision]
  push_cast
  ring

private theorem sincSquared_le_quarter_of_phaseFloor {R δ v : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hgap : δ ≤ |v|) (hwidth : 4 ≤ R * δ) :
    sincSquared R v ≤ 1 / 4 := by
  have hv : v ≠ 0 := by
    intro hv
    simp only [hv, abs_zero] at hgap
    linarith
  have harg := hwidth.trans (mul_le_mul_of_nonneg_left hgap hR.le)
  have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 4)
    (mul_nonneg hR.le (abs_nonneg v))).mpr harg
  rw [mul_pow, sq_abs] at hsq
  refine (sincSquared_le_inverse_square hR.ne' hv).trans ?_
  exact (div_le_iff₀ (mul_pos (by positivity) (sq_pos_of_ne_zero hv))).mpr
    (by linarith only [hsq])

/-- A single-step radius of at least 4/δ gives geometric suppression of
every nonzero phase gap at least δ away from zero. -/
theorem fejerPowerNonzeroGapRemainder_le_of_phaseFloor {T R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hwidth : 4 ≤ R * δ) (n : ℕ)
    (hgap : ∀ i j : Copies T, copyOrdinate T i ≠ copyOrdinate T j →
      δ ≤ |Real.log T * (copyOrdinate T i - copyOrdinate T j)|) :
    fejerPowerNonzeroGapRemainder T R n ≤ (Ncount 0 T : ℝ) ^ 2 / 4 ^ n := by
  classical
  unfold fejerPowerNonzeroGapRemainder
  have hsum :
      (∑ _i : Copies T, ∑ _j : Copies T, (1 / 4 : ℝ) ^ n) = (Ncount 0 T : ℝ) ^ 2 / 4 ^ n := by
    simp only [Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul, div_pow, one_pow]
    ring
  rw [← hsum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : copyOrdinate T i = copyOrdinate T j
  · simpa only [if_pos hij] using (by positivity : 0 ≤ (1 / 4 : ℝ) ^ n)
  · rw [if_neg hij]
    let d := copyOrdinate T i - copyOrdinate T j
    let v := Real.log T * d
    have hw : cauchyWeight d ≤ 1 := by
      unfold cauchyWeight
      apply (div_le_iff₀ (by positivity : 0 < 4 + d ^ 2)).mpr
      linarith only [sq_nonneg d]
    change cauchyWeight d * sincSquared R v ^ n ≤ (1 / 4 : ℝ) ^ n
    calc
      _ ≤ 1 * sincSquared R v ^ n :=
        mul_le_mul_of_nonneg_right hw (pow_nonneg (sincSquared_nonneg _ _) _)
      _ = sincSquared R v ^ n := one_mul _
      _ ≤ _ := pow_le_pow_left₀ (sincSquared_nonneg _ _)
        (sincSquared_le_quarter_of_phaseFloor hR hδ (hgap i j hij) hwidth) _

/-- A positive lower bound for the absolute nonzero phase gaps. Inserting
one provides a value for cutoffs with no gaps. -/
def fejerPositivePhaseFloor (T : ℝ) : ℝ := by
  classical
  let s := ((Finset.univ : Finset (Copies T × Copies T)).image fun p =>
    |Real.log T * (copyOrdinate T p.1 - copyOrdinate T p.2)|).filter (fun v => 0 < v)
  exact (insert 1 s).min' (Finset.insert_nonempty _ _)

theorem fejerPositivePhaseFloor_pos (T : ℝ) : 0 < fejerPositivePhaseFloor T := by
  classical
  unfold fejerPositivePhaseFloor
  have hm := Finset.min'_mem _ (Finset.insert_nonempty (1 : ℝ)
    (((Finset.univ : Finset (Copies T × Copies T)).image fun p =>
      |Real.log T * (copyOrdinate T p.1 - copyOrdinate T p.2)|).filter (fun v => 0 < v)))
  rcases Finset.mem_insert.mp hm with he | hm'
  · rw [he]
    exact zero_lt_one
  · exact (Finset.mem_filter.mp hm').2

theorem fejerPositivePhaseFloor_le {T : ℝ} (hT : 1 < T)
    (i j : Copies T) (hij : copyOrdinate T i ≠ copyOrdinate T j) :
    fejerPositivePhaseFloor T ≤ |Real.log T * (copyOrdinate T i - copyOrdinate T j)| := by
  classical
  unfold fejerPositivePhaseFloor
  apply Finset.min'_le
  apply Finset.mem_insert_of_mem
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩,
      abs_pos.mpr (mul_ne_zero (Real.log_pos hT).ne' (sub_ne_zero.mpr hij))⟩

def fejerPowerRadius (T : ℝ) : ℝ := 4 / fejerPositivePhaseFloor T

def fejerPowerOrder (T : ℝ) : ℕ := Nat.clog 4 ((Ncount 0 T) ^ 2 + 1)

/-- A logarithmic number of triangle convolutions suffices for a unit
interval containing the exact absolute distinct-zero collision count. -/
theorem normalized_fejerPower_sub_analytic_in_collision_unit_interval {T : ℝ} (hT : 1 < T) :
    let v := (T * Real.log T / (2 * Real.pi)) *
      fejerPowerFormFactor T (fejerPowerRadius T) (fejerPowerOrder T) - (analyticPairCount T : ℝ)
    (distinctZeroCollision T : ℝ) ≤ v ∧ v < (distinctZeroCollision T : ℝ) + 1 := by
  dsimp only
  let δ := fejerPositivePhaseFloor T
  have hδ : 0 < δ := fejerPositivePhaseFloor_pos T
  have hR : 0 < fejerPowerRadius T := div_pos (by norm_num) hδ
  have hwidth : 4 ≤ fejerPowerRadius T * δ := by
    change 4 ≤ 4 / δ * δ
    rw [div_mul_cancel₀ _ hδ.ne']
  have hcount : (Ncount 0 T) ^ 2 < 4 ^ fejerPowerOrder T :=
    (Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide) _)
  have hsmall : (Ncount 0 T : ℝ) ^ 2 / 4 ^ fejerPowerOrder T < 1 := by
    apply (div_lt_iff₀ (by positivity : 0 < (4 : ℝ) ^ fejerPowerOrder T)).mpr
    rw [one_mul]
    exact_mod_cast hcount
  have he := (fejerPowerNonzeroGapRemainder_le_of_phaseFloor hR hδ hwidth (fejerPowerOrder T)
    (fejerPositivePhaseFloor_le hT)).trans_lt hsmall
  rw [normalized_fejerPower_sub_analytic_eq hT hR]
  exact ⟨le_add_of_nonneg_right (fejerPowerNonzeroGapRemainder_nonneg T _ _),
    by linarith only [he]⟩

theorem prescribed_fejerPower_critical_line_iff {T : ℝ} (hT : 1 < T) :
    (T * Real.log T / (2 * Real.pi)) *
      fejerPowerFormFactor T (fejerPowerRadius T) (fejerPowerOrder T) -
      (analyticPairCount T : ℝ) < 2 ↔ ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 := by
  obtain ⟨hlo, hhi⟩ := normalized_fejerPower_sub_analytic_in_collision_unit_interval hT
  constructor
  · intro hs ρ hρ
    by_contra hoff
    have hc : (2 : ℝ) ≤ distinctZeroCollision T := by
      exact_mod_cast two_le_distinctZeroCollision_of_off_line hρ hoff
    linarith only [hs, hlo, hc]
  · intro hall
    have hc := (collision_eq_analyticPairCount_iff T).mpr hall
    have hz : distinctZeroCollision T = 0 := by
      have he := collision_eq_analytic_add_distinctZeroCollision T
      omega
    rw [hz, Nat.cast_zero, zero_add] at hhi
    exact hhi.trans (by norm_num)

theorem cofinal_prescribed_fejerPower_critical_line_iff_RH :
    (∀ H : ℝ, ∃ T : ℝ, H ≤ T ∧ 1 < T ∧
      (T * Real.log T / (2 * Real.pi)) *
        fejerPowerFormFactor T (fejerPowerRadius T) (fejerPowerOrder T) -
        (analyticPairCount T : ℝ) < 2) ↔ RiemannHypothesis := by
  rw [← cofinal_fejer_critical_line_iff_RH, cofinal_fejer_critical_line_iff]
  constructor
  · intro h H ρ hρ
    obtain ⟨T, hHT, hT, hs⟩ := h H
    obtain ⟨hz, hi, hheight⟩ := mem_cutoff.mp hρ
    exact (prescribed_fejerPower_critical_line_iff hT).mp hs ρ
      (mem_cutoff.mpr ⟨hz, hi, hheight.trans hHT⟩)
  · intro h H
    let T := max H 2
    have hT : 1 < T := lt_of_lt_of_le (by norm_num) (le_max_right H 2)
    exact ⟨T, le_max_left H 2, hT, (prescribed_fejerPower_critical_line_iff hT).mpr (h T)⟩

end RiemannResearch.Analysis.MontgomeryFormFactor
