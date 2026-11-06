/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.QCofinalDisplacementMoments
import RiemannResearch.RH.QSquarefreeDisplacementSignedTails
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.QSignedTailRigidity
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Cofinal signed harmonic rigidity of the full matched displacement

Source: Full_Conductor_RH_Projection_Machinery, 6 November 2026, task A4.
The all-conductor displacement from QFullDisplacement is retained throughout.
A full annihilator also annihilates the smaller squarefree dictionary, so the
already proved generic localized charge theorem applies to the full witness.
This is a one-way inclusion of annihilators, never an equality of projections.
No RH-to-approximation converse provider is required for the RH implication.
The harmonic growth bound in that implication is an open arithmetic premise.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QFullDisplacement
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal QSignedTailRigidity

/-- Inclusion of dictionaries, without identifying the corresponding fits. -/
theorem squarefree_closure_le_full :
    ZetaTwoOptimizerStage.closure ≤ QFullResidueProjection.closure := by
  have hs : Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom) ≤
      QFullResidueProjection.legalSpan := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    by_cases hi : Squarefree (i + 2)
    · rw [ZetaTwoOptimizerStage.squarefreeAtom, if_pos hi]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [ZetaTwoOptimizerStage.squarefreeAtom, if_neg hi]
      exact Submodule.zero_mem _
  exact Submodule.topologicalClosure_mono hs

theorem annihilator_mem_squarefree_orthogonal (u : QHilbert)
    (hu : u ∈ QFullResidueProjection.closureᗮ) :
    u ∈ ZetaTwoOptimizerStage.closureᗮ := by
  apply (ZetaTwoOptimizerStage.closure.mem_orthogonal _).mpr
  intro v hv
  exact Submodule.inner_right_of_mem_orthogonal (squarefree_closure_le_full hv) hu

/-- One signed physical harmonic prefix of the actual full displacement. -/
def harmonicSide (ε : ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (X + 1), max (ε * qSequence displacement n) 0 / (n : ℝ)

def minimumHarmonicPrefix (X : ℕ) : ℝ :=
  min (harmonicSide 1 X) (harmonicSide (-1) X)

def smoothingMoment : ℝ :=
  ∑' n : ℕ, |signedCoefficient (B pResidual) n| * (n : ℝ)

theorem smoothingMoment_nonneg : 0 ≤ smoothingMoment :=
  tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg n))

theorem harmonicSide_mono (ε : ℝ) : Monotone (harmonicSide ε) := by
  intro X Y h
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.add_le_add_right h 1))
  intro n _ _
  exact div_nonneg (le_max_right _ _) (Nat.cast_nonneg n)

theorem minimumHarmonicPrefix_mono : Monotone minimumHarmonicPrefix := by
  intro X Y h
  exact min_le_min (harmonicSide_mono 1 h) (harmonicSide_mono (-1) h)

theorem exists_best_sign (X : ℕ) :
    ∃ ε : ℝ, |ε| = 1 ∧ harmonicSide ε X = minimumHarmonicPrefix X := by
  rcases le_total (harmonicSide 1 X) (harmonicSide (-1) X) with h | h
  · exact ⟨1, abs_one, (min_eq_left h).symm⟩
  · exact ⟨-1, by norm_num, (min_eq_right h).symm⟩

theorem displacement_charge_prefix_eq (ε : ℝ) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1),
      max (ε * signedCoefficient displacement n) 0 * (n : ℝ)) =
      harmonicSide ε X / zetaTwo := by
  rw [harmonicSide, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  have hpos := positiveQWeight_nonneg n
  have hpart : max (ε * signedCoefficient displacement n) 0 =
      positiveQWeight n * max (ε * qSequence displacement n) 0 := by
    rw [signedCoefficient, mul_left_comm ε (positiveQWeight n)]
    rcases le_total 0 (ε * qSequence displacement n) with h | h
    · rw [max_eq_left h, max_eq_left (mul_nonneg hpos h)]
    · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hpos h), mul_zero]
  rw [hpart]
  by_cases h : n = 0
  · simp [h]
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h
    unfold positiveQWeight
    field_simp [hn, zetaTwo_pos.ne']

theorem witness_prefix_le (ε : ℝ) (hε : |ε| = 1) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1),
      max ((-ε) * signedCoefficient witness n) 0 * (n : ℝ)) ≤
      smoothingMoment + harmonicSide ε X / zetaTwo := by
  have hfirst : Summable (fun n : ℕ => |signedCoefficient (B pResidual) n| * (n : ℝ)) := by
    apply (signedCoefficient_B_firstMoment pResidual).abs.congr
    intro n
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), mul_comm]
  have hpoint (n : ℕ) : max ((-ε) * signedCoefficient witness n) 0 ≤
      |signedCoefficient (B pResidual) n| + max (ε * signedCoefficient displacement n) 0 := by
    apply max_le
    · have hb := neg_le_abs (ε * signedCoefficient (B pResidual) n)
      rw [abs_mul, hε, one_mul] at hb
      rw [witness, signedCoefficient_sub]
      linarith [le_max_left (ε * signedCoefficient displacement n) 0]
    · exact add_nonneg (abs_nonneg _) (le_max_right _ _)
  calc
    _ ≤ ∑ n ∈ Finset.range (X + 1),
        (|signedCoefficient (B pResidual) n| * (n : ℝ) +
          max (ε * signedCoefficient displacement n) 0 * (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n _
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (hpoint n) (Nat.cast_nonneg n)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, displacement_charge_prefix_eq]
      exact add_le_add (hfirst.sum_le_tsum _
        (fun n _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg n))) le_rfl

/-- An arbitrarily sparse cofinal polylog bound forces the full residual to zero.
The cheaper sign may vary separately at every cutoff. -/
theorem qResidual_zero_of_cofinal_harmonic_polylog (B C : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hgood : ∃ᶠ X : ℕ in atTop,
      minimumHarmonicPrefix X ≤ C * (Real.log (X : ℝ)) ^ B) :
    qResidual = 0 := by
  apply qResidual_eq_zero_of_witness_mean_zero
  apply QSquarefreeDisplacementRigidity.annihilator_mean_zero_of_cofinal_charge_polylog
    witness (annihilator_mem_squarefree_orthogonal witness witness_mem_orthogonal)
    smoothingMoment minimumHarmonicPrefix ?_
    smoothingMoment_nonneg minimumHarmonicPrefix_mono B C hB hC hgood
  intro X
  obtain ⟨ε, hε, he⟩ := exists_best_sign X
  exact ⟨ε, hε, by simpa only [he] using witness_prefix_le ε hε X⟩

/-- A checked full-conductor implication to Mathlib's RH. The harmonic budget
is the substantive, still-open hypothesis. -/
theorem riemannHypothesis_of_cofinal_harmonic_polylog (B C : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hgood : ∃ᶠ X : ℕ in atTop,
      minimumHarmonicPrefix X ≤ C * (Real.log (X : ℝ)) ^ B) :
    RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (qResidual_eq_zero_iff.mp
      (qResidual_zero_of_cofinal_harmonic_polylog B C hB hC hgood))

/-- Equality of the two full projections is rigid, not a generic two-metric fact. -/
theorem qResidual_eq_zero_iff_displacement_eq_zero :
    qResidual = 0 ↔ displacement = 0 := by
  refine ⟨displacement_eq_zero_of_qResidual_eq_zero, ?_⟩
  intro hd
  apply qResidual_zero_of_cofinal_harmonic_polylog 0 0 le_rfl le_rfl
  apply (Eventually.of_forall ?_).frequently
  intro X
  simp [minimumHarmonicPrefix, harmonicSide, hd,
    show qSequence (0 : QHilbert) = 0 from map_zero qSequenceLinear]

/-- Exact logical form of the cofinal signed harmonic test for the full residual. -/
theorem qResidual_zero_iff_cofinal_harmonic_polylog :
    qResidual = 0 ↔ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∃ᶠ X : ℕ in atTop,
        minimumHarmonicPrefix X ≤ C * (Real.log (X : ℝ)) ^ B := by
  constructor
  · intro hr
    refine ⟨0, 0, le_rfl, le_rfl, (Eventually.of_forall ?_).frequently⟩
    intro X
    simp [minimumHarmonicPrefix, harmonicSide,
      displacement_eq_zero_of_qResidual_eq_zero hr,
      show qSequence (0 : QHilbert) = 0 from map_zero qSequenceLinear]
  · rintro ⟨B, C, hB, hC, h⟩
    exact qResidual_zero_of_cofinal_harmonic_polylog B C hB hC h

/-- A nonzero full residual forces the cheaper harmonic sign to escape every
fixed logarithmic power eventually, not merely along some subsequence. -/
theorem minimumHarmonicPrefix_log_escape (hr : qResidual ≠ 0)
    (B : ℝ) (hB : 0 ≤ B) :
    Tendsto (fun X : ℕ => minimumHarmonicPrefix X / (Real.log (X : ℝ)) ^ B)
      atTop atTop := by
  apply tendsto_atTop.2
  intro b
  let C : ℝ := max b 0 + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hno : ¬ (∃ᶠ X : ℕ in atTop,
      minimumHarmonicPrefix X ≤ C * (Real.log (X : ℝ)) ^ B) := by
    intro h
    exact hr (qResidual_zero_of_cofinal_harmonic_polylog B C hB hC h)
  have hevent : ∀ᶠ X : ℕ in atTop,
      ¬ minimumHarmonicPrefix X ≤ C * (Real.log (X : ℝ)) ^ B := by
    classical
    change ¬¬ (∀ᶠ X : ℕ in atTop,
      ¬ minimumHarmonicPrefix X ≤ C * (Real.log (X : ℝ)) ^ B) at hno
    exact not_not.mp hno
  filter_upwards [hevent, eventually_ge_atTop (3 : ℕ)] with X hX h3
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hden : 0 < (Real.log (X : ℝ)) ^ B := Real.rpow_pos_of_pos hlog B
  have hh : C < minimumHarmonicPrefix X / (Real.log (X : ℝ)) ^ B :=
    (lt_div_iff₀ hden).mpr (lt_of_not_ge hX)
  have hb : b ≤ C := by dsimp [C]; linarith [le_max_left b 0]
  exact hb.trans hh.le

theorem riemannHypothesis_of_displacement_eq_zero (hd : displacement = 0) :
    RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (qResidual_eq_zero_iff.mp (qResidual_eq_zero_iff_displacement_eq_zero.mpr hd))

end RiemannResearch.RH.QFullDisplacement
