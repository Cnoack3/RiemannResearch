import RiemannResearch.Analysis.HilbertConstraintEnergy
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conductor-uniform reconstruction bounds for signed residue moments

Source: the Stage 3 atom/carry CRT handoff, §14.7.3, poses the finite Gram
gluing problem for independent arithmetic data. Here the prescribed datum
at d is the signed moment of g_d against coefficients a(n) with n a(n) in
square-summable sequence space. Both physical realizations and their exact
squared norms are computed. The constants bound every finite subdictionary.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ArithmeticResidueMomentEnergy

open ArithmeticCumulative Pareto ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis.HilbertConstraintReconstruction

/-- The signed moment is specified directly by the arithmetic residue function. -/
def residueMoment (a : ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑' n, a n * residueFraction d n

private def pInverseWeight (n : ℕ) : ℝ := (n : ℝ) * ((n : ℝ) + 1)
private def qInverseWeight (n : ℕ) : ℝ := zetaTwo * (n : ℝ) ^ 2

private theorem inverse_weight_energy (w x : ℝ) :
    1 / w * (w * x) ^ 2 = w * x ^ 2 := by
  by_cases hw : w = 0
  · simp [hw]
  · field_simp [hw]

private theorem pEnergy_summable (a : ℕ → ℝ)
    (ha : Summable (fun n : ℕ => ((n : ℝ) * a n) ^ 2)) :
    Summable (fun n => pInverseWeight n * a n ^ 2) := by
  apply Summable.of_nonneg_of_le _ _ (ha.mul_left 2)
  · intro n
    unfold pInverseWeight
    positivity
  · intro n
    cases n with
    | zero => simp [pInverseWeight]
    | succ n =>
      have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ n+1)
      have hn0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
      have hx := mul_nonneg (sub_nonneg.mpr hn) hn0
      have hw : ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1) ≤
          2 * ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith only [hx]
      have h := mul_le_mul_of_nonneg_right hw (sq_nonneg (a (n + 1)))
      simpa only [pInverseWeight, mul_pow, mul_assoc] using h

private theorem qEnergy_summable (a : ℕ → ℝ)
    (ha : Summable (fun n : ℕ => ((n : ℝ) * a n) ^ 2)) :
    Summable (fun n => qInverseWeight n * a n ^ 2) := by
  simpa only [qInverseWeight, mul_pow, mul_assoc] using ha.mul_left zetaTwo

/-- The Pareto representer has physical sequence n(n+1)a(n). -/
def pMomentVector (a : ℕ → ℝ) (ha : Summable (fun n : ℕ => ((n : ℝ) * a n) ^ 2)) :
    ThresholdHilbert :=
  sequenceHilbert (fun n => pInverseWeight n * a n)
    ((pEnergy_summable a ha).congr (fun n => (inverse_weight_energy (pInverseWeight n) (a n)).symm))

/-- The inverse-square representer has physical sequence ζ(2)n²a(n). -/
def qMomentVector (a : ℕ → ℝ) (ha : Summable (fun n : ℕ => ((n : ℝ) * a n) ^ 2)) :
    QHilbert :=
  encodeQ (fun n => qInverseWeight n * a n)
    ((qEnergy_summable a ha).congr (fun n => (inverse_weight_energy (qInverseWeight n) (a n)).symm))

variable (a : ℕ → ℝ) (ha : Summable (fun n : ℕ => ((n : ℝ) * a n) ^ 2))

theorem pMomentVector_sequence :
    hilbertSequence (pMomentVector a ha) = fun n : ℕ => (n : ℝ) * (n + 1) * a n :=
  hilbertSequence_sequenceHilbert (fun n => pInverseWeight n * a n) _ (by simp [pInverseWeight])

theorem qMomentVector_sequence :
    qSequence (qMomentVector a ha) = fun n : ℕ => zetaTwo * (n : ℝ) ^ 2 * a n :=
  qSequence_encodeQ (fun n => qInverseWeight n * a n) _ (by simp [qInverseWeight])

theorem pMomentVector_energy :
    ‖pMomentVector a ha‖ ^ 2 = ∑' n : ℕ, (n : ℝ) * (n + 1) * a n ^ 2 := by
  rw [hilbert_norm_weighted_sq, pMomentVector_sequence]
  exact tsum_congr (fun n => inverse_weight_energy _ _)

theorem qMomentVector_energy :
    ‖qMomentVector a ha‖ ^ 2 = zetaTwo * ∑' n : ℕ, ((n : ℝ) * a n) ^ 2 := by
  rw [qNorm_weighted_sq, qMomentVector_sequence, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simpa only [positiveQWeight, qInverseWeight, mul_pow, mul_assoc] using
    inverse_weight_energy (qInverseWeight n) (a n)

private theorem pMoment_integrand (d n : ℕ) :
    positiveWeight n * (residueFraction d n * ((n : ℝ) * (n + 1) * a n)) =
      a n * residueFraction d n := by
  by_cases hn : n = 0
  · subst n
    simp [residueFraction]
  · have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    unfold positiveWeight
    field_simp [ne_of_gt hp, show (n : ℝ) + 1 ≠ 0 by positivity]

private theorem qMoment_integrand (d n : ℕ) :
    positiveQWeight n * residueFraction d n * (zetaTwo * (n : ℝ)^2 * a n) =
      a n * residueFraction d n := by
  by_cases hn : n = 0
  · subst n
    simp [residueFraction]
  · have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    unfold positiveQWeight
    field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hp]

include ha in
/-- Every signed moment series for these data really converges. -/
theorem residueMoment_summable (d : ℕ) :
    Summable (fun n => a n * residueFraction d n) := by
  have h := qSequence_product_summable (qResidue d) (qMomentVector a ha)
  rw [qSequence_qResidue, qMomentVector_sequence] at h
  exact h.congr (qMoment_integrand a d)

theorem pMomentVector_observation (d : ℕ) (hd : 0 < d) :
    inner ℝ (normalizedResidueHilbert d hd) (pMomentVector a ha) = residueMoment a d := by
  rw [hilbert_inner_weighted, normalizedResidueHilbert_sequence, pMomentVector_sequence]
  exact tsum_congr (pMoment_integrand a d)

theorem qMomentVector_observation (d : ℕ) :
    inner ℝ (qResidue d) (qMomentVector a ha) = residueMoment a d := by
  rw [qInner_weighted, qSequence_qResidue, qMomentVector_sequence]
  exact tsum_congr (qMoment_integrand a d)

include ha in
/-- One pair of explicit constants works for all finite restrictions, even
when the conductor family repeats labels. -/
theorem residueMoment_dualBounds {ι : Type*} (d : ι → ℕ) (hd : ∀ i, 0 < d i) :
    DualBound (fun i => normalizedResidueHilbert (d i) (hd i)) (fun i => residueMoment a (d i))
        (∑' n : ℕ, (n : ℝ) * (n + 1) * a n ^ 2) ∧
    DualBound (fun i => qResidue (d i)) (fun i => residueMoment a (d i))
        (zetaTwo * ∑' n : ℕ, ((n : ℝ) * a n) ^ 2) := by
  rw [← pMomentVector_energy a ha, ← qMomentVector_energy a ha]
  exact ⟨(bounded_solution_iff_dualBound _ _ (sq_nonneg _)).mp
    ⟨pMomentVector a ha, le_rfl, fun i => pMomentVector_observation a ha _ _⟩,
    (bounded_solution_iff_dualBound _ _ (sq_nonneg _)).mp
      ⟨qMomentVector a ha, le_rfl, fun i => qMomentVector_observation a ha _⟩⟩

/-- At each physical site k the arithmetic target is simply g_d(k). -/
theorem residueEvaluation_dualBounds {ι : Type*} (d : ι → ℕ) (hd : ∀ i, 0 < d i) (k : ℕ) :
    DualBound (fun i => normalizedResidueHilbert (d i) (hd i))
        (fun i => residueFraction (d i) k) ((k : ℝ) * (k + 1)) ∧
    DualBound (fun i => qResidue (d i))
        (fun i => residueFraction (d i) k) (zetaTwo * (k : ℝ) ^ 2) := by
  let a (n : ℕ) : ℝ := if n = k then 1 else 0
  have ha : Summable (fun n : ℕ => ((n : ℝ) * a n) ^ 2) := by
    apply summable_of_ne_finset_zero (s := {k})
    intro n hn
    simp [a, show n ≠ k by simpa only [Finset.mem_singleton] using hn]
  have hb (m : ℕ) : residueMoment a m = residueFraction m k := by
    rw [residueMoment, tsum_eq_single k (fun n hn => by simp [a, hn])]
    simp [a]
  have hp : (∑' n : ℕ, (n : ℝ) * (n + 1) * a n ^ 2) = (k : ℝ) * (k + 1) := by
    rw [tsum_eq_single k (fun n hn => by simp [a, hn])]
    simp [a]
  have hq : (∑' n : ℕ, ((n : ℝ) * a n) ^ 2) = (k : ℝ) ^ 2 := by
    rw [tsum_eq_single k (fun n hn => by simp [a, hn])]
    simp [a]
  simpa only [hb, hp, hq] using residueMoment_dualBounds a ha d hd

/-- An arithmetic representation of data on any chosen conductor family. -/
def HasSignedMomentRepresentation {ι : Type*} (d : ι → ℕ) (b : ι → ℝ) : Prop :=
  ∃ a : ℕ → ℝ, Summable (fun n : ℕ => ((n : ℝ) * a n) ^ 2) ∧
    ∀ i, b i = residueMoment a (d i)

private theorem pMass_square_le (n : ℕ) (x : ℝ) :
    ((n : ℝ) * (positiveWeight n * x)) ^ 2 ≤ positiveWeight n * x ^ 2 := by
  have he : ((n : ℝ) * (positiveWeight n * x)) ^ 2 =
      (n : ℝ) / (n + 1) * (positiveWeight n * x ^ 2) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      unfold positiveWeight
      field_simp [ne_of_gt hp, show (n : ℝ) + 1 ≠ 0 by positivity] <;> ring
  rw [he]
  exact mul_le_of_le_one_left (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg x))
    ((div_le_one (by positivity : (0 : ℝ) < n+1)).mpr (by linarith))

private theorem qMass_square (n : ℕ) (x : ℝ) :
    ((n : ℝ) * (positiveQWeight n * x)) ^ 2 =
      zetaTwo⁻¹ * (positiveQWeight n * x ^ 2) := by
  by_cases hn : n = 0
  · simp [hn, positiveQWeight]
  · have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    unfold positiveQWeight
    field_simp [ne_of_gt hp, ne_of_gt zetaTwo_pos] <;> ring

/-- A solvable Pareto datum has an actual signed arithmetic representative.
The converse uses the computed density vector and works for arbitrary labels. -/
theorem pareto_solution_iff_signedMoment {ι : Type*} (d : ι → ℕ)
    (hd : ∀ i, 0 < d i) (b : ι → ℝ) :
    (∃ x : ThresholdHilbert, IsSolution (fun i => normalizedResidueHilbert (d i) (hd i)) b x) ↔
      HasSignedMomentRepresentation d b := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun n => positiveWeight n * hilbertSequence x n, ?_, ?_⟩
    · exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => pMass_square_le n _)
        (hilbertSequence_square_summable x)
    · intro i
      rw [← hx i, hilbert_inner_weighted, normalizedResidueHilbert_sequence]
      unfold paretoInner residueMoment
      apply tsum_congr
      intro n
      dsimp only
      ring
  · rintro ⟨a, ha, hb⟩
    exact ⟨pMomentVector a ha,
      fun i => (pMomentVector_observation a ha _ _).trans (hb i).symm⟩

/-- The same explicit signed-moment class characterizes Q solvability. -/
theorem q_solution_iff_signedMoment {ι : Type*} (d : ι → ℕ) (b : ι → ℝ) :
    (∃ x : QHilbert, IsSolution (fun i => qResidue (d i)) b x) ↔
      HasSignedMomentRepresentation d b := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun n => positiveQWeight n * qSequence x n, ?_, ?_⟩
    · exact ((qSequence_square_summable x).mul_left zetaTwo⁻¹).congr
        (fun n => (qMass_square n _).symm)
    · intro i
      rw [← hx i, qInner_weighted, qSequence_qResidue]
      unfold residueMoment
      apply tsum_congr
      intro n
      dsimp only
      ring
  · rintro ⟨a, ha, hb⟩
    exact ⟨qMomentVector a ha, fun i => (qMomentVector_observation a ha _).trans (hb i).symm⟩

end RiemannResearch.RH.ArithmeticResidueMomentEnergy
