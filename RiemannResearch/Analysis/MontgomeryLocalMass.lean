/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/

import RiemannResearch.Analysis.MontgomeryFormFactor
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.RH.WeilExplicitFormula.RvM.NcountWindow
import RiemannResearch.Analysis.GaussianCellGeometry
import RiemannResearch.Analysis.MontgomeryCauchyGram
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
/-! # Local Cauchy mass for the actual zeta-zero multiset

Source: the unit-window zero-count estimate already proved in
ActualZeroOrdinate.local_zero_count, and the Montgomery Cauchy Gram framework
(Montgomery 1973, https://websites.umich.edu/~hlm/paircor1.pdf).
The cell envelope and Schur estimates are elementary analytic deductions.
All analytic multiplicities and coincident ordinates are retained.
No RH or zero-density hypothesis is imposed. These upper bounds do not assert
a pair-correlation asymptotic or bounded limiting form-factor masses.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.MontgomeryLocalMass
open MontgomeryPoisson GaussianCellGeometry MarkedFourierTail

def inverseSquareEnvelope (z : ℤ) : ℝ := 8 / (1 + (z.natAbs : ℝ))^2

theorem inverseSquareEnvelope_nonneg (z : ℤ) : 0 ≤ inverseSquareEnvelope z := by
  unfold inverseSquareEnvelope
  positivity

theorem summable_inverseSquareEnvelope : Summable inverseSquareEnvelope := by
  have h := summable_window_tail (fun _ => (8 : ℝ))
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 8)
    (fun _ => by norm_num) (fun _ => le_rfl)
  apply Summable.of_nat_of_neg
  · simpa only [inverseSquareEnvelope, Int.natAbs_natCast] using h
  · simpa only [inverseSquareEnvelope, Int.natAbs_neg, Int.natAbs_natCast] using h

theorem tsum_inverseSquareEnvelope_le :
    (∑' z : ℤ, inverseSquareEnvelope z) ≤ 32 := by
  have h := window_tsum_tail_le (fun _ => (8 : ℝ))
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 8)
    (fun _ => by norm_num) (fun _ => le_rfl)
  have hn : Summable (fun n : ℕ => inverseSquareEnvelope (n : ℤ)) := by
    simpa only [inverseSquareEnvelope, Int.natAbs_natCast] using
      (summable_window_tail (fun _ => (8 : ℝ))
        (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 8)
        (fun _ => by norm_num) (fun _ => le_rfl))
  have hm : Summable (fun n : ℕ => inverseSquareEnvelope (-(n : ℤ))) := by
    simpa only [inverseSquareEnvelope, Int.natAbs_neg, Int.natAbs_natCast] using hn
  rw [Summable.tsum_of_nat_of_neg hn hm]
  simp only [inverseSquareEnvelope, Int.natAbs_neg, Int.natAbs_natCast,
    Int.natAbs_zero, Nat.cast_zero, add_zero, one_pow, div_one]
  norm_num at h
  linarith

theorem inverseSquareEnvelope_row_le (s : Finset ℤ) (a : ℤ) :
    (∑ b ∈ s, inverseSquareEnvelope (a-b)) ≤ 32 := by
  classical
  have hi : Function.Injective (fun b : ℤ => a - b) := by
    intro b c h
    change a-b = a-c at h
    omega
  calc
    _ = ∑ z ∈ s.image (fun b => a-b), inverseSquareEnvelope z := by
      rw [Finset.sum_image hi.injOn]
    _ ≤ ∑' z : ℤ, inverseSquareEnvelope z :=
      summable_inverseSquareEnvelope.sum_le_tsum _
        (fun z _ => inverseSquareEnvelope_nonneg z)
    _ ≤ 32 := tsum_inverseSquareEnvelope_le

theorem cauchyWeight_le_cell_envelope (x y : ℝ) :
    cauchyWeight (x-y) ≤
      inverseSquareEnvelope (Int.floor x - Int.floor y) := by
  have hd := floor_separation_le x y
  have hn : 0 ≤ (((Int.floor x - Int.floor y).natAbs : ℕ) : ℝ) := Nat.cast_nonneg _
  have ha : 0 ≤ |x-y| := abs_nonneg _
  unfold cauchyWeight inverseSquareEnvelope
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [sq_abs (x-y), sq_nonneg (|x-y|-2),
    mul_self_le_mul_self (by positivity : 0 ≤ 1 + (((Int.floor x - Int.floor y).natAbs : ℕ) : ℝ))
      (by linarith : 1 + (((Int.floor x - Int.floor y).natAbs : ℕ) : ℝ) ≤ |x-y|+2)]

/-- Unit-cell occupancy, including multiplicities, controls every Cauchy row. -/
theorem cauchy_row_le_of_occupancy {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hmass : ∀ a ∈ s.image (fun i => Int.floor (x i)),
      occupancy s (fun i => Int.floor (x i)) a ≤ C) (y : ℝ) :
    (∑ i ∈ s, cauchyWeight (y-x i)) ≤ 32*C := by
  classical
  calc
    _ ≤ ∑ i ∈ s, inverseSquareEnvelope (Int.floor y - Int.floor (x i)) :=
      Finset.sum_le_sum (fun i _ => cauchyWeight_le_cell_envelope y (x i))
    _ = ∑ a ∈ s.image (fun i => Int.floor (x i)),
        occupancy s (fun i => Int.floor (x i)) a *
          inverseSquareEnvelope (Int.floor y-a) :=
      sum_by_cells s (fun i => Int.floor (x i))
        (fun a => inverseSquareEnvelope (Int.floor y-a))
    _ ≤ ∑ a ∈ s.image (fun i => Int.floor (x i)),
        C * inverseSquareEnvelope (Int.floor y-a) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right (hmass a ha) (inverseSquareEnvelope_nonneg _)
    _ = C * ∑ a ∈ s.image (fun i => Int.floor (x i)),
        inverseSquareEnvelope (Int.floor y-a) := by rw [Finset.mul_sum]
    _ ≤ C*32 := mul_le_mul_of_nonneg_left (inverseSquareEnvelope_row_le _ _) hC
    _ = _ := by ring

end RiemannResearch.Analysis.MontgomeryLocalMass

noncomputable section
open scoped BigOperators
open Zeta23
namespace RiemannResearch.Analysis.MontgomeryLocalMass
open ActualZeroOrdinate MontgomeryFormFactor GaussianCellGeometry

abbrev WindowCopies (a b : ℝ) :=
  (ρ : {z : ℂ // z ∈ (zerosIn_finite a b).toFinset}) × Fin (zeroMult ρ.val)

theorem card_windowCopies (a b : ℝ) :
    Fintype.card (WindowCopies a b) = Ncount a b := by
  rw [Ncount, finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite a b)]
  simp [WindowCopies, Fintype.card_sigma, Finset.sum_attach]

theorem actual_cell_occupancy_le_count (T : ℝ) (a : ℤ) :
    occupancy (Finset.univ : Finset (Copies T))
      (fun i => Int.floor (-copyOrdinate T i)) a ≤
      (Ncount (-(a : ℝ)-1) (-(a : ℝ)) : ℝ) := by
  classical
  let s := (Finset.univ : Finset (Copies T)).filter
    (fun i => Int.floor (-copyOrdinate T i) = a)
  let f : {i // i ∈ s} → WindowCopies (-(a : ℝ)-1) (-(a : ℝ)) := fun i =>
    ⟨⟨i.val.1.val, by
      have hcell : Int.floor (-copyOrdinate T i.val) = a :=
        (Finset.mem_filter.mp i.property).2
      have hl := Int.floor_le (-copyOrdinate T i.val)
      have hu := Int.lt_floor_add_one (-copyOrdinate T i.val)
      rw [hcell] at hl hu
      rw [Set.Finite.mem_toFinset]
      exact ⟨(mem_cutoff.mp i.val.1.property).1,
        by change -(a : ℝ)-1 < copyOrdinate T i.val; linarith,
        by change copyOrdinate T i.val ≤ -(a : ℝ); linarith⟩⟩, i.val.2⟩
  have hi : Function.Injective f := by
    rintro ⟨⟨⟨ρ,hρ⟩,k⟩,hi⟩ ⟨⟨⟨σ,hσ⟩,l⟩,hj⟩ h
    have hv : ρ = σ := congrArg (fun w => w.1.val) h
    subst σ
    have hk : k = l := by
      have he := (Sigma.mk.inj_iff.mp h).2
      exact eq_of_heq he
    subst l
    rfl
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_coe, card_windowCopies] at hc
  change (s.card : ℝ) ≤ (Ncount (-(a : ℝ)-1) (-(a : ℝ)) : ℝ)
  exact_mod_cast hc

theorem actual_cell_occupancy_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ∀ a ∈ (Finset.univ : Finset (Copies T)).image
        (fun i => Int.floor (-copyOrdinate T i)),
      occupancy (Finset.univ : Finset (Copies T))
        (fun i => Int.floor (-copyOrdinate T i)) a ≤
        C * Real.log (T+3) := by
  obtain ⟨C,hC,hcount⟩ := local_zero_count
  refine ⟨C,hC,?_⟩
  intro T hT a ha
  obtain ⟨i,hi,hcell⟩ := Finset.mem_image.mp ha
  have hz := mem_cutoff.mp i.1.property
  have hl := Int.floor_le (-copyOrdinate T i)
  have hu := Int.lt_floor_add_one (-copyOrdinate T i)
  rw [hcell] at hl hu
  have ha0 : (a : ℝ) < 0 := by
    have hz0 : 0 < copyOrdinate T i := hz.2.1
    linarith
  have haZ : a ≤ -1 := by
    have : a < 0 := by exact_mod_cast ha0
    omega
  have haR : (a : ℝ) ≤ -1 := by exact_mod_cast haZ
  have hstart : 0 ≤ -(a : ℝ)-1 := by linarith
  have hend : -(a : ℝ)-1 ≤ T := by
    have hzT : copyOrdinate T i ≤ T := hz.2.2
    linarith
  have hlocal := hcount (-(a : ℝ)-1)
  have he : -(a : ℝ)-1+1 = -(a : ℝ) := by ring
  rw [he, abs_of_nonneg hstart] at hlocal
  calc
    _ ≤ (Ncount (-(a : ℝ)-1) (-(a : ℝ)) : ℝ) :=
      actual_cell_occupancy_le_count T a
    _ ≤ C * Real.log (-(a : ℝ)-1+3) := hlocal
    _ ≤ C * Real.log (T+3) := mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith) (by linarith)) (by linarith)

end RiemannResearch.Analysis.MontgomeryLocalMass

open MeasureTheory

namespace RiemannResearch.Analysis.MontgomeryLocalMass
open MontgomeryPoisson GaussianCellGeometry MarkedFourierTail

theorem cauchyWeight_nonneg (d : ℝ) : 0 ≤ cauchyWeight d := by
  unfold cauchyWeight
  positivity

theorem cauchyWeight_neg (d : ℝ) : cauchyWeight (-d) = cauchyWeight d := by
  simp [cauchyWeight]

/-- Schur's estimate retains all coefficients and all repeated ordinates. -/
theorem kernelQuadratic_norm_le_of_rows {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (c : ι → ℂ) (D : ℝ)
    (hrow : ∀ i, (∑ j, cauchyWeight (t i-t j)) ≤ D) :
    ‖kernelQuadratic t c‖ ≤ D * ∑ i, ‖c i‖^2 := by
  have hs : ∀ i j, cauchyWeight (t i-t j) = cauchyWeight (t j-t i) := by
    intro i j
    unfold cauchyWeight
    congr 2
    ring
  calc
    _ ≤ ∑ i, ‖∑ j, c i * conj (c j) * (cauchyWeight (t i-t j) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, cauchyWeight (t i-t j) * ‖c i‖ * ‖c j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ j, ‖c i * conj (c j) * (cauchyWeight (t i-t j) : ℂ)‖ :=
          norm_sum_le _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (cauchyWeight_nonneg _)]
          ring
    _ ≤ _ := symmetric_kernel_quadratic_le_row_bound
      Finset.univ (fun i => ‖c i‖) (fun i j => cauchyWeight (t i-t j)) D
      (fun i _ j _ => cauchyWeight_nonneg _) (fun i _ j _ => hs i j)
      (fun i _ => hrow i)

theorem weighted_signal_energy_le_of_rows {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (c : ι → ℂ) (D : ℝ)
    (hrow : ∀ i, (∑ j, cauchyWeight (t i-t j)) ≤ D) :
    (∫ s : ℝ, Real.exp (-2*|s|)*‖signal t c s‖^2) ≤ D * ∑ i, ‖c i‖^2 := by
  rw [finite_gram]
  exact (Complex.re_le_norm _).trans (kernelQuadratic_norm_le_of_rows t c D hrow)

end RiemannResearch.Analysis.MontgomeryLocalMass

namespace RiemannResearch.Analysis.MontgomeryLocalMass
open MontgomeryPoisson ActualZeroOrdinate MontgomeryFormFactor
open scoped BigOperators ComplexConjugate

/-- Unconditional row bound for the complete actual zero multiset. -/
theorem exists_actual_cauchy_row_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ y : ℝ,
      (∑ i : Copies T, cauchyWeight (y-copyOrdinate T i)) ≤
        C * Real.log (T+3) := by
  obtain ⟨A,hA,hmass⟩ := actual_cell_occupancy_bound
  refine ⟨32*A, by positivity, ?_⟩
  intro T hT y
  have hlog : 0 ≤ Real.log (T+3) := Real.log_nonneg (by linarith)
  have h := cauchy_row_le_of_occupancy
    (Finset.univ : Finset (Copies T)) (fun i => -copyOrdinate T i)
    (A * Real.log (T+3)) (by positivity) (hmass T hT) (-y)
  have he (i : Copies T) :
      cauchyWeight (-y - -copyOrdinate T i) =
        cauchyWeight (y-copyOrdinate T i) := by
    rw [show -y - -copyOrdinate T i = -(y-copyOrdinate T i) by ring,
      cauchyWeight_neg]
  simpa only [he, mul_assoc] using h

/-- An actual-zero Bessel estimate, uniform in the coefficients and in frequency. -/
theorem exists_actual_cauchy_gram_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ c : Copies T → ℂ,
      ‖kernelQuadratic (copyOrdinate T) c‖ ≤
        C * Real.log (T+3) * ∑ i, ‖c i‖^2 := by
  obtain ⟨C,hC,hrow⟩ := exists_actual_cauchy_row_bound
  refine ⟨C,hC,?_⟩
  intro T hT c
  exact kernelQuadratic_norm_le_of_rows _ _ _ (fun i => hrow T hT _)

/-- This is a uniform upper bound, not an asymptotic pair-correlation formula. -/
theorem exists_formFactor_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ T α : ℝ, 9 ≤ T →
      MontgomeryFormFactor.formFactor T α ≤ C * Real.log T := by
  obtain ⟨C,hC,hgram⟩ := exists_actual_cauchy_gram_bound
  obtain ⟨B,hB,hcount⟩ := ActualZeroOrdinate.exists_count_le_height_log
  refine ⟨4*Real.pi*C*B, by positivity, ?_⟩
  intro T α hT
  have ht : 0 < T := by linarith
  have hl : 0 < Real.log T := Real.log_pos (by linarith)
  have hlog : Real.log (T+3) ≤ 2*Real.log T := by
    calc
      _ ≤ Real.log (T*T) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_mul ht.ne' ht.ne']; ring
  have hpair : ‖pairSum (copyOrdinate T) (α*Real.log T)‖ ≤
      C * Real.log (T+3) * (Ncount 0 T : ℝ) := by
    rw [pairSum_eq_kernel]
    have h := hgram T ht.le (fun i => ZeroOrdinate.phase (α*Real.log T) (copyOrdinate T i))
    simpa only [ZeroOrdinate.phase_norm, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, card_copies] using h
  unfold MontgomeryFormFactor.formFactor
  apply (div_le_iff₀ (by positivity : 0 < T*Real.log T/(2*Real.pi))).mpr
  calc
    _ ≤ ‖pairSum (copyOrdinate T) (α*Real.log T)‖ := Complex.re_le_norm _
    _ ≤ C * Real.log (T+3) * (Ncount 0 T : ℝ) := hpair
    _ ≤ (C*(2*Real.log T))*(B*T*Real.log T) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hlog hC.le
      · exact hcount T hT
      · positivity
      · positivity
    _ = _ := by field_simp; ring

end RiemannResearch.Analysis.MontgomeryLocalMass
