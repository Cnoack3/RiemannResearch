/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.Analysis.FiniteGramScalarConstraint
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.FiniteHilbertConstraints
import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Normalization capacity of large legal Q conductors

Source: user-provided `Q_LCM_Periods_RH_Criterion_and_Research_Agenda_2026-10-16.md`,
Sections 7, 8 and research priorities 1--2, for the legal family and scalar
constraint. The exact head--tail capacity identity below is a continuation of
that argument. It applies to any finite independent residue family with all
conductors greater than H, hence in particular the squarefree divisors of the
stage radical that are greater than H. The Q norm and the complete tail remain
exact; a uniform constrained-energy bound is still open.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QLargeConductorCapacity

open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative QCovarianceInvertibility
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity

/-- Complete Q energy beyond physical site H, in the weighted l2 realization. -/
def tailEnergy (H : ℕ) (f : QHilbert) : ℝ := ∑' n : ℕ, (f (n + H)) ^ 2

theorem tailEnergy_nonneg (H : ℕ) (f : QHilbert) : 0 ≤ tailEnergy H f :=
  tsum_nonneg (fun _ => sq_nonneg _)

/-- An exact identity before using tail nonnegativity. Each of the H physical
head sites contributes exactly s²/zetaTwo. -/
theorem linear_head_energy (H : ℕ) (f : QHilbert) (s : ℝ)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = (n : ℝ) * s) :
    ‖f‖ ^ 2 = (H : ℝ) / zetaTwo * s ^ 2 + tailEnergy H f := by
  have hterm (n : ℕ) (hn : n < H) : (f n) ^ 2 = s ^ 2 / zetaTwo := by
    rw [← qSequence_weighted_square f n, hh (n + 1) (Nat.succ_pos n) (by omega)]
    have hnR : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    unfold positiveQWeight
    field_simp
  rw [qNorm_sq, ← (qCoordinate_square_summable f).sum_add_tsum_nat_add H]
  change (∑ n ∈ Finset.range H, (f n) ^ 2) + tailEnergy H f = _
  have hs : (∑ n ∈ Finset.range H, (f n) ^ 2) = (H : ℝ) / zetaTwo * s ^ 2 := by
    calc
      _ = ∑ n ∈ Finset.range H, s ^ 2 / zetaTwo := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hterm n (Finset.mem_range.mp hn)
      _ = _ := by simp; ring
  rw [hs]

variable {ι : Type*} [Fintype ι]

def normalizationSource (d : ι → ℕ) (i : ι) : ℝ := 1 / (d i : ℝ)

theorem synthesis_head (d : ι → ℕ) (H : ℕ) (hd : ∀ i, H < d i)
    (c : ι → ℝ) (n : ℕ) (hnH : n ≤ H) :
    qSequence (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) n =
      (n : ℝ) * ∑ i, c i * normalizationSource d i := by
  change qSequenceLinear
    (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) n = _
  rw [Fintype.linearCombination_apply, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, c i * qSequence (qResidue (d i)) n) = _
  simp_rw [qSequence_qResidue, residueFraction,
    Nat.mod_eq_of_lt (lt_of_le_of_lt hnH (hd _))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold normalizationSource
  ring

/-- Exact signed Gram energy split for every coefficient vector. -/
theorem synthesis_energy (d : ι → ℕ) (H : ℕ) (hd : ∀ i, H < d i) (c : ι → ℝ) :
    ‖Fintype.linearCombination ℝ (fun i => qResidue (d i)) c‖ ^ 2 =
      (H : ℝ) / zetaTwo * (∑ i, c i * normalizationSource d i) ^ 2 +
        tailEnergy H (Fintype.linearCombination ℝ (fun i => qResidue (d i)) c) :=
  linear_head_energy H _ _ (fun n _ hn => synthesis_head d H hd c n hn)

/-- C = (H/zetaTwo) C² + full tail energy of the actual normal vector. -/
theorem capacity_head_tail (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i)))
    (H : ℕ) (hd : ∀ i, H < d i) :
    capacity hv (normalizationSource d) =
      (H : ℝ) / zetaTwo * capacity hv (normalizationSource d) ^ 2 +
        tailEnergy H (minimumVector hv (normalizationSource d)) := by
  have he := synthesis_energy d H hd (inverseSource hv (normalizationSource d))
  change ‖minimumVector hv (normalizationSource d)‖ ^ 2 =
    (H : ℝ) / zetaTwo * capacity hv (normalizationSource d) ^ 2 +
      tailEnergy H (minimumVector hv (normalizationSource d)) at he
  rwa [← capacity_eq_norm_sq] at he

omit [Fintype ι] in
theorem normalizationSource_ne_zero [Nonempty ι] (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) : normalizationSource d ≠ 0 := by
  intro hzero
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hi : (d i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hd i))
  have hs : normalizationSource d i ≠ 0 := one_div_ne_zero hi
  exact hs (congrFun hzero i)

/-- Increasing the stage cannot make this full-Q normalization capacity
diverge when all allowed conductors exceed the matched head. -/
theorem capacity_le_zetaTwo_div_head [Nonempty ι] (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i)))
    (H : ℕ) (hH : 0 < H) (hd : ∀ i, H < d i) :
    capacity hv (normalizationSource d) ≤ zetaTwo / (H : ℝ) := by
  have hb := normalizationSource_ne_zero d (fun i => lt_trans hH (hd i))
  have hp := capacity_pos hv (normalizationSource d) hb
  have he := capacity_head_tail d hv H hd
  have ht := tailEnergy_nonneg H (minimumVector hv (normalizationSource d))
  have hmul : capacity hv (normalizationSource d) *
      ((H : ℝ) / zetaTwo * capacity hv (normalizationSource d)) ≤
      capacity hv (normalizationSource d) * 1 := by nlinarith only [he, ht]
  have hnorm := (mul_le_mul_iff_right₀ hp).mp hmul
  have hdiv : (H : ℝ) * capacity hv (normalizationSource d) / zetaTwo ≤ 1 := by
    simpa only [div_mul_eq_mul_div] using hnorm
  have hprod := (div_le_iff₀ zetaTwo_pos).mp hdiv
  apply (le_div_iff₀ (show (0 : ℝ) < H by exact_mod_cast hH)).mpr
  simpa only [mul_one, mul_comm] using hprod

/-- The inverse-capacity cost equals the mandatory head cost plus an exact
nonnegative tail cost; no off-head terms are discarded. -/
theorem inverse_capacity_head_tail [Nonempty ι] (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i)))
    (H : ℕ) (hH : 0 < H) (hd : ∀ i, H < d i) :
    1 / capacity hv (normalizationSource d) = (H : ℝ) / zetaTwo +
      tailEnergy H (minimumVector hv (normalizationSource d)) /
        capacity hv (normalizationSource d) ^ 2 := by
  have hp := ne_of_gt (capacity_pos hv (normalizationSource d)
    (normalizationSource_ne_zero d (fun i => lt_trans hH (hd i))))
  have he := capacity_head_tail d hv H hd
  field_simp [ne_of_gt zetaTwo_pos] at he
  field_simp [hp, ne_of_gt zetaTwo_pos]
  nlinarith only [he]

/-- A concrete distinct legal family automatically supplies the independence
needed for the capacity estimate. Squarefree families are a special case. -/
theorem distinct_residue_capacity_bound [Nonempty ι] (d : ι → ℕ)
    (hd2 : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (H : ℕ) (hH : 0 < H) (hd : ∀ i, H < d i) :
    capacity (qResidue_linearIndependent d hd2 hinj) (normalizationSource d) ≤
      zetaTwo / (H : ℝ) :=
  capacity_le_zetaTwo_div_head d (qResidue_linearIndependent d hd2 hinj) H hH hd

/-- A bounded normalization penalty forces H times the squared mismatch to
remain bounded. This is a necessary rate, not a provider of the RH bound. -/
theorem head_scaled_mismatch_le [Nonempty ι] (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i)))
    (H : ℕ) (hH : 0 < H) (hd : ∀ i, H < d i)
    (m B : ℝ) (hbudget : m ^ 2 / capacity hv (normalizationSource d) ≤ B) :
    (H : ℝ) * m ^ 2 ≤ zetaTwo * B := by
  have hp := capacity_pos hv (normalizationSource d)
    (normalizationSource_ne_zero d (fun i => lt_trans hH (hd i)))
  have hc := capacity_le_zetaTwo_div_head d hv H hH hd
  have hB : 0 ≤ B := (div_nonneg (sq_nonneg m) hp.le).trans hbudget
  have hm := (div_le_iff₀ hp).mp hbudget
  have hcap := (le_div_iff₀ (show (0 : ℝ) < H by exact_mod_cast hH)).mp hc
  have hstep := mul_le_mul_of_nonneg_right hm (show (0 : ℝ) ≤ H by positivity)
  have hstep' := mul_le_mul_of_nonneg_left hcap hB
  nlinarith only [hstep, hstep']

/-- The scalar constrained optimizer exactly removes a linear physical head.
For the manuscript the target here is r_H^0 and the slope is S_H. -/
theorem scalar_optimizer_head_zero [Nonempty ι] (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i)))
    (H : ℕ) (hH : 0 < H) (hd : ∀ i, H < d i)
    (f : QHilbert) (s : ℝ)
    (hf : ∀ n, 0 < n → n ≤ H → qSequence f n = (n : ℝ) * s)
    (n : ℕ) (hn : 0 < n) (hnH : n ≤ H) :
    qSequence (f - Fintype.linearCombination ℝ (fun i => qResidue (d i))
      (scalarCoefficients hv (normalizationSource d) f s)) n = 0 := by
  have hb := normalizationSource_ne_zero d (fun i => lt_trans hH (hd i))
  change qSequenceLinear (f - Fintype.linearCombination ℝ
    (fun i => qResidue (d i)) (scalarCoefficients hv (normalizationSource d) f s)) n = 0
  rw [map_sub]
  change qSequence f n - qSequence (Fintype.linearCombination ℝ
    (fun i => qResidue (d i)) (scalarCoefficients hv (normalizationSource d) f s)) n = 0
  rw [hf n hn hnH, synthesis_head d H hd _ n hnH,
    scalarCoefficients_source hv (normalizationSource d) hb f s, sub_self]

/-- In particular, bounding the actual constrained minimum implies the
head-scaled mismatch estimate. No independent penalty bound is assumed. -/
theorem constrained_mismatch_bound [Nonempty ι] (d : ι → ℕ)
    (hv : LinearIndependent ℝ (fun i => qResidue (d i)))
    (H : ℕ) (hH : 0 < H) (hd : ∀ i, H < d i)
    (f : QHilbert) (s B : ℝ)
    (hbound : ‖f - Fintype.linearCombination ℝ (fun i => qResidue (d i))
      (scalarCoefficients hv (normalizationSource d) f s)‖ ^ 2 ≤ B) :
    (H : ℝ) * scalarMismatch hv (normalizationSource d) f s ^ 2 ≤ zetaTwo * B := by
  have hb := normalizationSource_ne_zero d (fun i => lt_trans hH (hd i))
  have he := scalarCoefficients_energy hv (normalizationSource d) hb f s
  rw [← residual_schur_value] at he
  have hpen : scalarMismatch hv (normalizationSource d) f s ^ 2 /
      capacity hv (normalizationSource d) ≤ B := by
    nlinarith only [he, hbound,
      sq_nonneg ‖f - Fintype.linearCombination ℝ
        (fun i => qResidue (d i)) (inverseCoeff hv f)‖]
  exact head_scaled_mismatch_le d hv H hH hd _ B hpen

end RiemannResearch.RH.QLargeConductorCapacity
