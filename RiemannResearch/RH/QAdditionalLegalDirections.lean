/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSixAtomTrialBound
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QResidueConditional
import RiemannResearch.RH.QParityProjectionDefect
import RiemannResearch.Analysis.ProjectionCompressionDefect
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases

/-!
# An additional legal squarefree direction and a thirty-period trial

Source: the user's request to improve the complete-Q error using additional
legal squarefree directions. The added direction is g_5 - (6/5) g_6.
All period sums retain the entire infinite Q tail; no finite-tail approximation
or special-function numerical output is assumed by the theorems below.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QAdditionalLegalDirections
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative QResidueConditional
open QSquarefreeLatticePackets QSixAtomTrialBound

/-- The compensated fifth conductor preserves the first four coordinates. -/
def fifthDirection : QHilbert := compensatedResidue 5 6

def fifthDirectionValue (n : ℕ) : ℝ :=
  residueFraction 5 n - (6 / 5 : ℝ) * residueFraction 6 n

/-- A scalar family in the full legal dictionary, not a restriction on other
possible legal directions. -/
def additionalTrial (a : ℝ) : QHilbert := sixTrial + a • fifthDirection

def additionalResidual (a : ℝ) (n : ℕ) : ℝ :=
  sixResidual n - a * fifthDirectionValue n

theorem fifthDirection_sequence (n : ℕ) :
    qSequence fifthDirection n = fifthDirectionValue n := by
  simpa [fifthDirection, fifthDirectionValue] using compensatedResidue_sequence 5 6 n

theorem additionalTrial_sequence (a : ℝ) (n : ℕ) :
    qSequence (additionalTrial a) n =
      residueFraction 2 n + residueFraction 3 n + residueFraction 6 n +
        a * fifthDirectionValue n := by
  change qSequenceLinear ((qResidue 2 + qResidue 3 + qResidue 6) +
    a • fifthDirection) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change qSequence (qResidue 2) n + qSequence (qResidue 3) n +
    qSequence (qResidue 6) n + a * qSequence fifthDirection n = _
  rw [qSequence_qResidue, qSequence_qResidue, qSequence_qResidue,
    fifthDirection_sequence]

theorem additionalTrial_head_four (a : ℝ) (n : ℕ) (hn : 0 < n) (hn4 : n ≤ 4) :
    qSequence (additionalTrial a) n = 1 := by
  rw [additionalTrial_sequence]
  interval_cases n <;> norm_num [fifthDirectionValue, residueFraction]

/-- The rational choice a=1 also repairs the fifth coordinate exactly. -/
theorem additionalTrial_one_head_five (n : ℕ) (hn : 0 < n) (hn5 : n ≤ 5) :
    qSequence (additionalTrial 1) n = 1 := by
  rw [additionalTrial_sequence]
  interval_cases n <;> norm_num [fifthDirectionValue, residueFraction]

theorem additionalTrial_mem (V : Submodule ℝ QHilbert) (a : ℝ)
    (h2 : qResidue 2 ∈ V) (h3 : qResidue 3 ∈ V)
    (h5 : qResidue 5 ∈ V) (h6 : qResidue 6 ∈ V) :
    additionalTrial a ∈ V := by
  exact V.add_mem (V.add_mem (V.add_mem h2 h3) h6)
    (V.smul_mem a (V.sub_mem h5 (V.smul_mem _ h6)))

theorem additionalTrial_mem_squarefreeSpan (a : ℝ) :
    additionalTrial a ∈ qSquarefreeCRTSpan := by
  apply additionalTrial_mem
  · exact Submodule.subset_span ⟨⟨2, by decide, Nat.prime_two.squarefree⟩, rfl⟩
  · exact Submodule.subset_span ⟨⟨3, by decide, Nat.prime_three.squarefree⟩, rfl⟩
  · exact Submodule.subset_span ⟨⟨5, by decide, (by norm_num : Nat.Prime 5).squarefree⟩, rfl⟩
  · have h6 : Squarefree (6 : ℕ) := by
      change Squarefree ((2 : ℕ) * 3)
      exact Nat.squarefree_mul_iff.mpr
        ⟨by decide, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩
    exact Submodule.subset_span ⟨⟨6, by decide, h6⟩, rfl⟩

/-- Period thirty includes the zero class as positive representative thirty. -/
theorem additionalResidual_period (a : ℝ) (n : ℕ) :
    additionalResidual a (n + 30) = additionalResidual a n := by
  simp [additionalResidual, sixResidual, fifthDirectionValue, residueFraction,
    Nat.add_mod]

theorem fifthDirectionValue_abs_le_one (n : ℕ) : |fifthDirectionValue n| ≤ 1 := by
  have h5 : ((n % 5 : ℕ) : ℝ) ≤ 4 := by
    exact_mod_cast (show n % 5 ≤ 4 by omega)
  have h6 : ((n % 6 : ℕ) : ℝ) ≤ 5 := by
    exact_mod_cast (show n % 6 ≤ 5 by omega)
  have h50 : (0 : ℝ) ≤ (n % 5 : ℕ) := Nat.cast_nonneg _
  have h60 : (0 : ℝ) ≤ (n % 6 : ℕ) := Nat.cast_nonneg _
  have he : fifthDirectionValue n =
      (((n % 5 : ℕ) : ℝ) - ((n % 6 : ℕ) : ℝ)) / 5 := by
    unfold fifthDirectionValue residueFraction
    norm_num
    ring
  rw [he, abs_le]
  constructor <;> linarith

theorem additionalResidual_abs_le (a : ℝ) (n : ℕ) :
    |additionalResidual a n| ≤ 1 + |a| := by
  calc
    |additionalResidual a n| ≤ |sixResidual n| + |a * fifthDirectionValue n| :=
      by simpa [additionalResidual] using
        abs_sub_le (sixResidual n) 0 (a * fifthDirectionValue n)
    _ = |sixResidual n| + |a| * |fifthDirectionValue n| := by rw [abs_mul]
    _ ≤ 1 + |a| * 1 := add_le_add (sixResidual_abs_le_one n)
      (mul_le_mul_of_nonneg_left (fifthDirectionValue_abs_le_one n) (abs_nonneg a))
    _ = _ := by ring

theorem additionalTrial_residual_sequence (a : ℝ) (n : ℕ) :
    qSequence (qOne - additionalTrial a) (n + 1) = additionalResidual a (n + 1) := by
  change qSequenceLinear (qOne - additionalTrial a) (n + 1) = _
  simp only [map_sub, Pi.sub_apply]
  change qSequence qOne (n + 1) - qSequence (additionalTrial a) (n + 1) = _
  rw [qSequence_qOne, additionalTrial_sequence]
  simp only [qOneSequence, Nat.add_one_ne_zero, if_false, additionalResidual, sixResidual]
  ring

/-- Exact complete-Q error for every real coefficient a. -/
theorem additionalTrial_error_exact (a : ℝ) :
    ‖qOne - additionalTrial a‖ ^ 2 =
      ∑ r : Fin 30, residuePowerWeight 0 30 (r.val + 1) *
        additionalResidual a (r.val + 1) ^ 2 := by
  have he : ‖qOne - additionalTrial a‖ ^ 2 =
      inversePowerMean 0 (fun n => additionalResidual a n ^ 2) := by
    rw [← real_inner_self_eq_norm_sq, qInner_eq_inversePowerMean]
    unfold inversePowerMean
    apply tsum_congr
    intro n
    simp only [additionalTrial_residual_sequence]
    ring
  have hb : ∀ n, |additionalResidual a n ^ 2| ≤ (1 + |a|) ^ 2 := by
    intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    calc
      _ = |additionalResidual a n| ^ 2 := (sq_abs _).symm
      _ ≤ _ := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
        (additionalResidual_abs_le a n)
  rw [he]
  exact periodic_inversePowerMean 0 30 (by decide) _ hb
    (by intro n; rw [additionalResidual_period])

/-- Exact signed quadratic dependence; the mixed term is retained. -/
theorem additionalTrial_error_quadratic (a : ℝ) :
    ‖qOne - additionalTrial a‖ ^ 2 = ‖qOne - sixTrial‖ ^ 2 -
      2 * a * inner ℝ (qOne - sixTrial) fifthDirection +
      a ^ 2 * ‖fifthDirection‖ ^ 2 := by
  rw [additionalTrial, sub_add_eq_sub_sub, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem fifthDirection_ne_zero : fifthDirection ≠ 0 := by
  have h5 : qSequence fifthDirection 5 = -1 := by
    rw [fifthDirection_sequence]
    norm_num [fifthDirectionValue, residueFraction]
  intro hz
  have h0 : qSequence fifthDirection 5 = 0 := by
    rw [hz]
    change qSequenceLinear 0 5 = 0
    simp
  linarith

/-- The one-dimensional optimizer is exact and includes the full nonnegative
remainder, rather than discarding signed interactions. -/
theorem additionalTrial_error_completion (a : ℝ) :
    ‖qOne - additionalTrial a‖ ^ 2 =
      ‖qOne - sixTrial‖ ^ 2 -
        inner ℝ (qOne - sixTrial) fifthDirection ^ 2 / ‖fifthDirection‖ ^ 2 +
      ‖fifthDirection‖ ^ 2 *
        (a - inner ℝ (qOne - sixTrial) fifthDirection / ‖fifthDirection‖ ^ 2) ^ 2 := by
  rw [additionalTrial_error_quadratic]
  have hn : ‖fifthDirection‖ ≠ 0 := norm_ne_zero_iff.mpr fifthDirection_ne_zero
  field_simp [hn]
  ring

/-- A fully rational majorant for the complete infinite-Q error. -/
theorem additionalTrial_error_le_residue_majorant (a : ℝ) :
    ‖qOne - additionalTrial a‖ ^ 2 ≤
      ∑ r : Fin 30, additionalResidual a (r.val + 1) ^ 2 /
        (((r.val + 1 : ℕ) : ℝ) ^ 2) := by
  rw [additionalTrial_error_exact]
  apply Finset.sum_le_sum
  intro r hr
  have hw := residueWeight_le_inverse_square 30 (r.val + 1) (by omega) (by omega)
  have hm := mul_le_mul_of_nonneg_right hw (sq_nonneg (additionalResidual a (r.val + 1)))
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, div_eq_mul_inv,
    one_mul, mul_one, mul_comm] using hm

/-- An unconditional complete-Q bound, stronger than 61/900 for the six trial. -/
theorem additionalTrial_one_error_lt_one_twenty_fifth :
    ‖qOne - additionalTrial 1‖ ^ 2 < (1 / 25 : ℝ) := by
  apply lt_of_le_of_lt (additionalTrial_error_le_residue_majorant 1)
  norm_num [Fin.sum_univ_succ, additionalResidual, sixResidual,
    fifthDirectionValue, residueFraction]

open QParityProjectionDefect
open RiemannResearch.Analysis.ProjectionCompression

variable (V : Submodule ℝ QHilbert) [V.HasOrthogonalProjection]

/-- Every larger legal space inherits the stronger complete-Q upper bound. -/
theorem projection_error_lt_one_twenty_fifth
    (h2 : qResidue 2 ∈ V) (h3 : qResidue 3 ∈ V)
    (h5 : qResidue 5 ∈ V) (h6 : qResidue 6 ∈ V) :
    ‖qOne - V.starProjection qOne‖ ^ 2 < (1 / 25 : ℝ) := by
  have ht : additionalTrial 1 ∈ V := additionalTrial_mem V 1 h2 h3 h5 h6
  have he : (qOne - additionalTrial 1) - V.starProjection (qOne - additionalTrial 1) =
      qOne - V.starProjection qOne := by
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr ht]
    abel
  have hn := defect_norm_le V (qOne - additionalTrial 1)
  rw [he] at hn
  exact lt_of_le_of_lt ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn)
    additionalTrial_one_error_lt_one_twenty_fifth

/-- The extra squarefree conductor improves the parity-leakage comparison. -/
theorem additional_optimizer_parity_leakage_bounds
    (h2 : qResidue 2 ∈ V) (h3 : qResidue 3 ∈ V)
    (h5 : qResidue 5 ∈ V) (h6 : qResidue 6 ∈ V) :
    (21 / 25 : ℝ) * ‖qOne - V.starProjection qOne‖ ^ 2 ≤
      ‖V.starProjection qOne - paritySpace.starProjection (V.starProjection qOne)‖ ^ 2 ∧
      ‖V.starProjection qOne - paritySpace.starProjection (V.starProjection qOne)‖ ^ 2 ≤
        ‖qOne - V.starProjection qOne‖ ^ 2 := by
  rw [optimizer_parity_leakage_exact V h2]
  have hb := (projection_error_lt_one_twenty_fifth V h2 h3 h5 h6).le
  have hd : 0 ≤ ‖qOne - V.starProjection qOne‖ ^ 2 := sq_nonneg _
  have hm := mul_nonneg hd (sub_nonneg.mpr hb)
  constructor <;> nlinarith [sq_nonneg (‖qOne - V.starProjection qOne‖ ^ 2)]

end RiemannResearch.RH.QAdditionalLegalDirections
