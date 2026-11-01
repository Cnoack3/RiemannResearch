/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.SquarefreeMobiusCesaroHeads
import RiemannResearch.RH.CRTSquarefreeBoundedTail
import RiemannResearch.RH.SquarefreeStageExhaustion
import RiemannResearch.RH.CesaroResidueMean
import RiemannResearch.RH.MultiRangeEnergyCertificates
import RiemannResearch.RH.MobiusReciprocalNonvanishing
import RiemannResearch.NumberTheory.MobiusReciprocalSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Complete Cesaro energy of squarefree Mobius heads

Source: direct algebra and estimates developed for the user's November 1,
2026 investigation. The centered residue formula and existing complete-tail
certificate are reused. Every signed Mobius term, including composite
squarefree conductors, remains present. No subpolynomial growth is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro ArithmeticCumulative
open ArithmeticCumulative.CesaroResidue

def mobiusPrefixSum (H : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius d : ℝ)

def mobiusPrefixDefect (H t : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius d : ℝ) * residueCesaroDefect d t

def mobiusPrefixDefectBudget (H : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 H, |(ArithmeticFunction.moebius d : ℝ)| * (d : ℝ)) / 8

theorem mobiusPrefixDefect_abs_le (H t : ℕ) :
    |mobiusPrefixDefect H t| ≤ mobiusPrefixDefectBudget H := by
  unfold mobiusPrefixDefect mobiusPrefixDefectBudget
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 H,
        |(ArithmeticFunction.moebius d : ℝ) * residueCesaroDefect d t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 H,
        |(ArithmeticFunction.moebius d : ℝ)| * ((d : ℝ) / 8) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (residueCesaroDefect_abs_le d t (Finset.mem_Icc.mp hd).1) (abs_nonneg _)
    _ = _ := by simp only [mul_div_assoc, Finset.sum_div]

theorem mobiusPrefixDefectBudget_nonneg (H : ℕ) :
    0 ≤ mobiusPrefixDefectBudget H := by
  unfold mobiusPrefixDefectBudget
  positivity

theorem mobiusPrefix_cesaro_centered (H t : ℕ) (ht : 0 < t) :
    (∑ d ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius d : ℝ) *
      cesaro (residueFraction d) t) =
      (mobiusPrefixSum H - mobiusReciprocalSum H) / 2 -
        mobiusPrefixDefect H t / (t : ℝ) := by
  unfold mobiusPrefixSum mobiusReciprocalSum mobiusPrefixDefect
  rw [sub_div, Finset.sum_div, Finset.sum_div, Finset.sum_div,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  have hdR : (d : ℝ) ≠ 0 := by positivity
  rw [cesaro_residue_centered d t hd0 ht]
  field_simp
  <;> ring

def mobiusHeadCesaroCenter (H D : ℕ) : ℝ :=
  ((D : ℝ) * mobiusReciprocalSum H - mobiusPrefixSum H) / 2

def mobiusHeadCesaroRemainder (H D t : ℕ) : ℝ :=
  mobiusPrefixDefect H t - (D : ℝ) * mobiusReciprocalSum H * residueCesaroDefect D t

def mobiusHeadCesaroBudget (H D : ℕ) : ℝ :=
  mobiusPrefixDefectBudget H + |mobiusReciprocalSum H| * (D : ℝ)^2 / 8

theorem squarefreeMobiusHead_cesaro_linear (H D t : ℕ) :
    cesaro (squarefreeMobiusHead H D) t =
      -(∑ d ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius d : ℝ) *
        cesaro (residueFraction d) t) +
      (D : ℝ) * mobiusReciprocalSum H * cesaro (residueFraction D) t := by
  simp only [cesaro, squarefreeMobiusHead, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_div, add_div, neg_div, mul_div_assoc]
  rw [Finset.sum_comm]

/-- Exact signed mean and endpoint remainder, before any estimate. -/
theorem squarefreeMobiusHead_cesaro_centered (H D t : ℕ)
    (hD : 0 < D) (ht : 0 < t) :
    cesaro (squarefreeMobiusHead H D) t = mobiusHeadCesaroCenter H D +
      mobiusHeadCesaroRemainder H D t / (t : ℝ) := by
  have hdR : (D : ℝ) ≠ 0 := by positivity
  rw [squarefreeMobiusHead_cesaro_linear, mobiusPrefix_cesaro_centered H t ht,
    cesaro_residue_centered D t hD ht]
  unfold mobiusHeadCesaroCenter mobiusHeadCesaroRemainder
  field_simp
  <;> ring

theorem mobiusHeadCesaroRemainder_abs_le (H D t : ℕ) (hD : 0 < D) :
    |mobiusHeadCesaroRemainder H D t| ≤ mobiusHeadCesaroBudget H D := by
  have hr := residueCesaroDefect_abs_le D t hD
  have hp := mobiusPrefixDefect_abs_le H t
  unfold mobiusHeadCesaroRemainder mobiusHeadCesaroBudget
  calc
    _ ≤ |mobiusPrefixDefect H t| +
        |(D : ℝ) * mobiusReciprocalSum H * residueCesaroDefect D t| := abs_sub _ _
    _ ≤ mobiusPrefixDefectBudget H +
        ((D : ℝ) * |mobiusReciprocalSum H|) * ((D : ℝ) / 8) := by
      simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg D : (0 : ℝ) ≤ (D : ℝ))]
      exact add_le_add hp (mul_le_mul_of_nonneg_left hr (by positivity))
    _ = _ := by ring

/-- Complete tail certificate; the finite head is not substituted for the tail. -/
theorem squarefreeMobiusHead_tail_bound (H D N : ℕ) (hD : H < D) :
    conditionalMeanTailSquare N (squarefreeMobiusHead H D) ≤
      2 / ((N : ℝ) + 2) * (|mobiusHeadCesaroCenter H D| +
        mobiusHeadCesaroBudget H D / ((N : ℝ) + 1)) ^ 2 := by
  have hB : 0 ≤ mobiusHeadCesaroBudget H D := by
    unfold mobiusHeadCesaroBudget
    exact add_nonneg (mobiusPrefixDefectBudget_nonneg H) (by positivity)
  apply conditionalMeanTailSquare_le_centered _
    (squarefreeMobiusHead_mem_legal H D hD) N _ _ hB
  intro t ht
  rw [squarefreeMobiusHead_cesaro_centered H D t (by omega) ht,
    add_sub_cancel_left, abs_div, abs_of_nonneg (Nat.cast_nonneg t : (0 : ℝ) ≤ (t : ℝ))]
  exact div_le_div_of_nonneg_right (mobiusHeadCesaroRemainder_abs_le H D t (by omega))
    (Nat.cast_nonneg t)

/-- Exact full weighted energy, with all signed cross terms retained in the square. -/
theorem squarefreeMobiusHead_energy_identity (H D : ℕ) (hD : H < D) :
    conditionalMeanSquare (squarefreeMobiusHead H D) =
      (H : ℝ) / ((H : ℝ) + 2) +
      ∑' k : ℕ, conditionalWeight (k + H) *
        (mobiusHeadCesaroCenter H D +
          mobiusHeadCesaroRemainder H D (k + H + 1) / (k + H + 1 : ℕ)) ^ 2 := by
  rw [conditionalMeanSquare_exact_head_split H
    (show squarefreeMobiusHead H D ∈ conditionalHeadClass H from
      ⟨squarefreeMobiusHead_mem_legal H D hD,
       fun n hn hnH => squarefreeMobiusHead_exact H D n hD hn hnH⟩)]
  congr 1
  apply tsum_congr
  intro k
  rw [squarefreeMobiusHead_cesaro_centered H D (k + H + 1) (by omega) (by omega)]

/-- Repair-only signed averaging leaves every original Mobius prefix coefficient fixed. -/
theorem squarefreeMobiusHead_average_cesaro_centered
    {ι : Type*} (S : Finset ι) (w : ι → ℝ) (D : ι → ℕ) (H t : ℕ)
    (hw : ∑ i ∈ S, w i = 1) (hD : ∀ i ∈ S, 0 < D i) (ht : 0 < t) :
    cesaro (fun n => ∑ i ∈ S, w i * squarefreeMobiusHead H (D i) n) t =
      (mobiusReciprocalSum H * (∑ i ∈ S, w i * (D i : ℝ)) - mobiusPrefixSum H) / 2 +
      (mobiusPrefixDefect H t - mobiusReciprocalSum H *
        (∑ i ∈ S, w i * (D i : ℝ) * residueCesaroDefect (D i) t)) / (t : ℝ) := by
  rw [cesaro_finsetCombination]
  calc
    _ = ∑ i ∈ S, w i * (mobiusHeadCesaroCenter H (D i) +
        mobiusHeadCesaroRemainder H (D i) t / (t : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [squarefreeMobiusHead_cesaro_centered H (D i) t (hD i hi) ht]
    _ = ∑ i ∈ S,
        (w i * (-mobiusPrefixSum H / 2 + mobiusPrefixDefect H t / (t : ℝ)) +
          (mobiusReciprocalSum H / 2) * (w i * (D i : ℝ)) -
          (mobiusReciprocalSum H / (t : ℝ)) *
            (w i * (D i : ℝ) * residueCesaroDefect (D i) t)) := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold mobiusHeadCesaroCenter mobiusHeadCesaroRemainder
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, hw]
      ring

def mobiusRepairAverageBudget {ι : Type*}
    (S : Finset ι) (w : ι → ℝ) (D : ι → ℕ) (H : ℕ) : ℝ :=
  mobiusPrefixDefectBudget H + |mobiusReciprocalSum H| *
    (∑ i ∈ S, |w i| * (D i : ℝ)^2) / 8

theorem mobiusRepairAverage_remainder_abs_le {ι : Type*}
    (S : Finset ι) (w : ι → ℝ) (D : ι → ℕ) (H t : ℕ)
    (hD : ∀ i ∈ S, 0 < D i) :
    |mobiusPrefixDefect H t - mobiusReciprocalSum H *
      (∑ i ∈ S, w i * (D i : ℝ) * residueCesaroDefect (D i) t)| ≤
      mobiusRepairAverageBudget S w D H := by
  have hs : |∑ i ∈ S, w i * (D i : ℝ) * residueCesaroDefect (D i) t| ≤
      (∑ i ∈ S, |w i| * (D i : ℝ)^2) / 8 := by
    calc
      _ ≤ ∑ i ∈ S, |w i * (D i : ℝ) * residueCesaroDefect (D i) t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ S, |w i| * (D i : ℝ)^2 / 8 := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (D i) : (0 : ℝ) ≤ (D i : ℝ))]
        calc
          _ ≤ |w i| * (D i : ℝ) * ((D i : ℝ) / 8) :=
            mul_le_mul_of_nonneg_left (residueCesaroDefect_abs_le (D i) t (hD i hi))
              (by positivity)
          _ = _ := by ring
      _ = _ := by rw [Finset.sum_div]
  calc
    _ ≤ |mobiusPrefixDefect H t| + |mobiusReciprocalSum H *
        (∑ i ∈ S, w i * (D i : ℝ) * residueCesaroDefect (D i) t)| := abs_sub _ _
    _ ≤ mobiusPrefixDefectBudget H + |mobiusReciprocalSum H| *
        ((∑ i ∈ S, |w i| * (D i : ℝ)^2) / 8) := by
      rw [abs_mul]
      exact add_le_add (mobiusPrefixDefect_abs_le H t)
        (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
    _ = _ := by unfold mobiusRepairAverageBudget; ring

theorem squarefreeMobiusHead_average_tail_bound {ι : Type*}
    (S : Finset ι) (w : ι → ℝ) (D : ι → ℕ) (H N : ℕ)
    (hw : ∑ i ∈ S, w i = 1) (hD : ∀ i ∈ S, H < D i) :
    conditionalMeanTailSquare N
      (fun n => ∑ i ∈ S, w i * squarefreeMobiusHead H (D i) n) ≤
      2 / ((N : ℝ) + 2) *
        (|(mobiusReciprocalSum H * (∑ i ∈ S, w i * (D i : ℝ)) -
            mobiusPrefixSum H) / 2| +
          mobiusRepairAverageBudget S w D H / ((N : ℝ) + 1))^2 := by
  have hlegal : (fun n => ∑ i ∈ S, w i * squarefreeMobiusHead H (D i) n) ∈
      legalSeedSpan (Set.Ici 1) := by
    have hh : (∑ i ∈ S, w i • squarefreeMobiusHead H (D i)) ∈
        legalSeedSpan (Set.Ici 1) := by
      apply (legalSeedSpan (Set.Ici 1)).sum_mem
      intro i hi
      exact (legalSeedSpan (Set.Ici 1)).smul_mem _
        (squarefreeMobiusHead_mem_legal H (D i) (hD i hi))
    convert hh using 1
    ext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hB : 0 ≤ mobiusRepairAverageBudget S w D H := by
    unfold mobiusRepairAverageBudget
    exact add_nonneg (mobiusPrefixDefectBudget_nonneg H) (by positivity)
  apply conditionalMeanTailSquare_le_centered _ hlegal N _ _ hB
  intro t ht
  have hDp : ∀ i ∈ S, 0 < D i := by intro i hi; have := hD i hi; omega
  rw [squarefreeMobiusHead_average_cesaro_centered S w D H t hw hDp ht,
    add_sub_cancel_left, abs_div, abs_of_nonneg (Nat.cast_nonneg t : (0 : ℝ) ≤ (t : ℝ))]
  exact div_le_div_of_nonneg_right (mobiusRepairAverage_remainder_abs_le S w D H t hDp)
    (Nat.cast_nonneg t)

/-- Mean neutrality changes the complete far-tail certificate to cubic decay.
It is not a bound uniform in the moving head or its coefficient budget. -/
theorem squarefreeMobiusHead_average_cubic_tail {ι : Type*}
    (S : Finset ι) (w : ι → ℝ) (D : ι → ℕ) (H N : ℕ)
    (hw : ∑ i ∈ S, w i = 1) (hD : ∀ i ∈ S, H < D i)
    (hmean : mobiusReciprocalSum H * (∑ i ∈ S, w i * (D i : ℝ)) = mobiusPrefixSum H) :
    conditionalMeanTailSquare N
      (fun n => ∑ i ∈ S, w i * squarefreeMobiusHead H (D i) n) ≤
      2 * (mobiusRepairAverageBudget S w D H)^2 /
        (((N : ℝ) + 2) * ((N : ℝ) + 1)^2) := by
  have h := squarefreeMobiusHead_average_tail_bound S w D H N hw hD
  simp only [hmean, sub_self, zero_div, abs_zero, zero_add] at h
  simpa only [div_pow, div_mul_div_comm] using h

def mobiusRepairWeightLeft (H D E : ℕ) : ℝ :=
  ((E : ℝ) * mobiusReciprocalSum H - mobiusPrefixSum H) /
    (((E : ℝ) - (D : ℝ)) * mobiusReciprocalSum H)

def mobiusRepairWeightRight (H D E : ℕ) : ℝ :=
  (mobiusPrefixSum H - (D : ℝ) * mobiusReciprocalSum H) /
    (((E : ℝ) - (D : ℝ)) * mobiusReciprocalSum H)

/-- Two deterministic signed weights satisfy both exact-head and mean-neutrality
constraints. No lower bound on the finite reciprocal Mobius sum is needed. -/
theorem mobiusRepairWeights_constraints (H D E : ℕ) (hH : 0 < H) (hDE : D < E) :
    mobiusRepairWeightLeft H D E + mobiusRepairWeightRight H D E = 1 ∧
    mobiusReciprocalSum H *
      (mobiusRepairWeightLeft H D E * (D : ℝ) +
        mobiusRepairWeightRight H D E * (E : ℝ)) = mobiusPrefixSum H := by
  have ha := mobiusReciprocalSum_ne_zero hH
  have hgap : (E : ℝ) - (D : ℝ) ≠ 0 := by
    have : (D : ℝ) < E := by exact_mod_cast hDE
    linarith
  unfold mobiusRepairWeightLeft mobiusRepairWeightRight
  constructor <;> field_simp <;> ring

def meanNeutralMobiusHead (H D E : ℕ) (n : ℕ) : ℝ :=
  mobiusRepairWeightLeft H D E * squarefreeMobiusHead H D n +
    mobiusRepairWeightRight H D E * squarefreeMobiusHead H E n

theorem meanNeutralMobiusHead_exact (H D E : ℕ) (hH : 0 < H)
    (hD : H < D) (hDE : D < E) (n : ℕ) (hn : 0 < n) (hnH : n ≤ H) :
    meanNeutralMobiusHead H D E n = 1 := by
  unfold meanNeutralMobiusHead
  rw [squarefreeMobiusHead_exact H D n hD hn hnH,
    squarefreeMobiusHead_exact H E n (lt_trans hD hDE) hn hnH, mul_one, mul_one]
  exact (mobiusRepairWeights_constraints H D E hH hDE).1

/-- The explicit two-repair family has an unconditional complete cubic-tail bound. -/
theorem meanNeutralMobiusHead_cubic_tail (H D E N : ℕ) (hH : 0 < H)
    (hD : H < D) (hDE : D < E) :
    conditionalMeanTailSquare N (meanNeutralMobiusHead H D E) ≤
      2 * (mobiusPrefixDefectBudget H + |mobiusReciprocalSum H| *
        (|mobiusRepairWeightLeft H D E| * (D : ℝ)^2 +
          |mobiusRepairWeightRight H D E| * (E : ℝ)^2) / 8)^2 /
        (((N : ℝ) + 2) * ((N : ℝ) + 1)^2) := by
  let w : ℕ → ℝ := fun i => if i = 0 then mobiusRepairWeightLeft H D E
    else mobiusRepairWeightRight H D E
  let R : ℕ → ℕ := fun i => if i = 0 then D else E
  have hc := mobiusRepairWeights_constraints H D E hH hDE
  have hw : ∑ i ∈ ({0, 1} : Finset ℕ), w i = 1 := by simpa [w] using hc.1
  have hR : ∀ i ∈ ({0, 1} : Finset ℕ), H < R i := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simpa [R] using hD
    · simpa [R] using lt_trans hD hDE
  have hm : mobiusReciprocalSum H *
      (∑ i ∈ ({0, 1} : Finset ℕ), w i * (R i : ℝ)) = mobiusPrefixSum H := by
    simpa [w, R] using hc.2
  change conditionalMeanTailSquare N (fun n =>
    mobiusRepairWeightLeft H D E * squarefreeMobiusHead H D n +
      mobiusRepairWeightRight H D E * squarefreeMobiusHead H E n) ≤ _
  simpa [w, R, mobiusRepairAverageBudget] using
    squarefreeMobiusHead_average_cubic_tail ({0, 1} : Finset ℕ) w R H N hw hR hm

/-- Canceling the small reciprocal sum in the actual coefficients avoids
spurious large bounds coming from the averaging weights themselves. -/
theorem meanNeutralMobiusHead_coefficients (H D E : ℕ) (hH : 0 < H)
    (hDE : D < E) (n : ℕ) :
    meanNeutralMobiusHead H D E n =
      -(∑ d ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) +
      ((D : ℝ) * ((E : ℝ) * mobiusReciprocalSum H - mobiusPrefixSum H) /
        ((E : ℝ) - (D : ℝ))) * residueFraction D n +
      ((E : ℝ) * (mobiusPrefixSum H - (D : ℝ) * mobiusReciprocalSum H) /
        ((E : ℝ) - (D : ℝ))) * residueFraction E n := by
  have ha := mobiusReciprocalSum_ne_zero hH
  have hgap : (E : ℝ) - (D : ℝ) ≠ 0 := by
    have : (D : ℝ) < E := by exact_mod_cast hDE
    linarith
  unfold meanNeutralMobiusHead squarefreeMobiusHead
    mobiusRepairWeightLeft mobiusRepairWeightRight
  field_simp
  <;> ring

/-- The two-repair construction remains in the literal squarefree finite span. -/
theorem meanNeutralMobiusHead_mem_divisorSpan (H D E : ℕ) (hH : 0 < H)
    (hD : H < D) (hDE : D < E) (hDs : Squarefree D) (hEs : Squarefree E) :
    meanNeutralMobiusHead H D E ∈
      divisorResidueSpan (SquarefreeStageExhaustion.primorialPeriod E) := by
  let S := divisorResidueSpan (SquarefreeStageExhaustion.primorialPeriod E)
  have hHE : H < E := lt_trans hD hDE
  have hb : squarefreeMobiusHead H E ∈ S := by
    simpa only [max_eq_right hHE.le] using
      squarefreeMobiusHead_mem_divisorSpan H E hH hHE hEs
  have hd : residueFraction D ∈ S :=
    Submodule.subset_span ⟨D, by omega,
      SquarefreeStageExhaustion.squarefree_dvd_primorialPeriod D E hDs hDE.le, rfl⟩
  have he : residueFraction E ∈ S :=
    Submodule.subset_span ⟨E, by omega,
      SquarefreeStageExhaustion.squarefree_dvd_primorialPeriod E E hEs le_rfl, rfl⟩
  let a := (D : ℝ) * ((E : ℝ) * mobiusReciprocalSum H - mobiusPrefixSum H) /
    ((E : ℝ) - (D : ℝ))
  let b := (E : ℝ) * (mobiusPrefixSum H - (D : ℝ) * mobiusReciprocalSum H) /
    ((E : ℝ) - (D : ℝ))
  have h := S.add_mem (S.add_mem hb (S.smul_mem a hd))
    (S.smul_mem (b - (E : ℝ) * mobiusReciprocalSum H) he)
  convert h using 1
  ext n
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [meanNeutralMobiusHead_coefficients H D E hH hDE]
  unfold squarefreeMobiusHead
  dsimp [a, b]
  ring


/-- The signed cumulative remainder of the mean-neutral two-repair family.
Composite squarefree conductors remain in the full Möbius prefix. -/
def meanNeutralMobiusRemainder (H D E n : ℕ) : ℝ :=
  mobiusPrefixDefect H n - mobiusReciprocalSum H *
    (mobiusRepairWeightLeft H D E * (D : ℝ) * residueCesaroDefect D n +
      mobiusRepairWeightRight H D E * (E : ℝ) * residueCesaroDefect E n)

/-- Exact primitive, with the canceled mean separated before taking squares. -/
theorem meanNeutralMobiusHead_cumulative (H D E n : ℕ)
    (hH : 0 < H) (hD : H < D) (hDE : D < E) (hn : 0 < n) :
    cumulative (meanNeutralMobiusHead H D E) n = meanNeutralMobiusRemainder H D E n := by
  have hw := mobiusRepairWeights_constraints H D E hH hDE
  have hl : cesaro (meanNeutralMobiusHead H D E) n =
      mobiusRepairWeightLeft H D E * cesaro (squarefreeMobiusHead H D) n +
      mobiusRepairWeightRight H D E * cesaro (squarefreeMobiusHead H E) n := by
    simp only [cesaro, meanNeutralMobiusHead, Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_div, add_div, mul_div_assoc]
  rw [squarefreeMobiusHead_cesaro_centered H D n (hH.trans hD) hn,
    squarefreeMobiusHead_cesaro_centered H E n ((hH.trans hD).trans hDE) hn] at hl
  have hcenter : mobiusRepairWeightLeft H D E * mobiusHeadCesaroCenter H D +
      mobiusRepairWeightRight H D E * mobiusHeadCesaroCenter H E = 0 := by
    unfold mobiusHeadCesaroCenter
    calc
      _ = (mobiusReciprocalSum H *
          (mobiusRepairWeightLeft H D E * (D : ℝ) +
            mobiusRepairWeightRight H D E * (E : ℝ)) -
          mobiusPrefixSum H *
            (mobiusRepairWeightLeft H D E + mobiusRepairWeightRight H D E)) / 2 := by ring
      _ = 0 := by rw [hw.1, hw.2]; ring
  have hrem : mobiusRepairWeightLeft H D E * mobiusHeadCesaroRemainder H D n +
      mobiusRepairWeightRight H D E * mobiusHeadCesaroRemainder H E n =
      meanNeutralMobiusRemainder H D E n := by
    unfold mobiusHeadCesaroRemainder meanNeutralMobiusRemainder
    calc
      _ = (mobiusRepairWeightLeft H D E + mobiusRepairWeightRight H D E) *
          mobiusPrefixDefect H n - mobiusReciprocalSum H *
            (mobiusRepairWeightLeft H D E * (D : ℝ) * residueCesaroDefect D n +
              mobiusRepairWeightRight H D E * (E : ℝ) * residueCesaroDefect E n) := by ring
      _ = _ := by rw [hw.1]; ring
  rw [CesaroResidue.cesaro_eq_cumulative] at hl
  have he : cumulative (meanNeutralMobiusHead H D E) n / (n : ℝ) =
      meanNeutralMobiusRemainder H D E n / (n : ℝ) := by
    calc
      _ = _ := hl
      _ = (mobiusRepairWeightLeft H D E * mobiusHeadCesaroCenter H D +
            mobiusRepairWeightRight H D E * mobiusHeadCesaroCenter H E) +
          (mobiusRepairWeightLeft H D E * mobiusHeadCesaroRemainder H D n +
            mobiusRepairWeightRight H D E * mobiusHeadCesaroRemainder H E n) / (n : ℝ) := by ring
      _ = _ := by rw [hcenter, hrem, zero_add]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp at he
  exact he
end RiemannResearch.RH.Pareto
