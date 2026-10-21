/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimeValuationIndependence
import RiemannResearch.RH.FinitePrimeLikelihood
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.FinitePrimeCentered
import RiemannResearch.RH.QExpectationIntegral
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite prime coordinates in the actual Zipf-two Hilbert space

Source: user-directed orthonormal-basis program, 20 October 2026.
The existing actual finite Boolean pushforward law transfers every finite
observable and its Gram matrix into QHilbert. In particular, normalized
centered products become an actual orthonormal family. The complete residual
is retained in its finite expansion. This does not assert squarefree legality
or completeness for all prime valuations: divisibility records only whether
a valuation is positive.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal
namespace RiemannResearch.RH.QFinitePrimeBasis
open ZetaTwoProbability ZetaTwoHilbert FinitePrimeLikelihood FinitePrimeCentered

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A uniform finite-observable bound. -/
private def observableBound (F : (ι → Bool) → ℝ) : ℝ := ∑ b, |F b|

private theorem observableBound_nonneg (F : (ι → Bool) → ℝ) : 0 ≤ observableBound F :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem abs_le_observableBound (F : (ι → Bool) → ℝ) (b : ι → Bool) :
    |F b| ≤ observableBound F :=
  Finset.single_le_sum (fun c _ => abs_nonneg (F c)) (Finset.mem_univ b)

/-- The finite product expectation is the actual Q integral, for every observable. -/
theorem integral_boolean_observable (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (F : (ι → Bool) → ℝ) :
    (∫ k : ℕ+, F (fun i => divisibilityBool (p i) k) ∂Q) =
      tensorExpectation (fun i => primeParameter (p i : ℝ)) F := by
  let X : ℕ+ → (ι → Bool) := fun k i => divisibilityBool (p i) k
  have hX : Measurable X := measurable_of_countable X
  have hF : Integrable F (Measure.map X Q) := by
    apply memLp_one_iff_integrable.mp
    apply MemLp.of_bound StronglyMeasurable.of_discrete.aestronglyMeasurable
      (observableBound F)
    exact Filter.Eventually.of_forall (fun b => by
      simpa only [Real.norm_eq_abs] using abs_le_observableBound F b)
  change (∫ k, F (X k) ∂Q) = _
  rw [← integral_map hX.aemeasurable
    (measurable_of_countable F).aestronglyMeasurable, integral_fintype hF]
  unfold tensorExpectation
  apply Finset.sum_congr rfl
  intro b _
  rw [measureReal_def, Measure.map_apply hX (measurableSet_singleton b)]
  change (Q {k : ℕ+ | (fun i => divisibilityBool (p i) k) = b}).toReal * F b = _
  rw [measure_boolean_configuration p hp hinj]
  rw [ENNReal.toReal_ofReal]
  exact Finset.prod_nonneg fun i _ => bernoulliMass_nonneg
      (primeParameter_mem_unitInterval (by exact_mod_cast (hp i).one_le)).1
      (primeParameter_mem_unitInterval (by exact_mod_cast (hp i).one_le)).2 (b i)

/-- The finite observable on physical integers, anchored at zero. -/
def booleanSequence (p : ι → ℕ) (F : (ι → Bool) → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else F (fun i => decide (p i ∣ n))

private theorem booleanSequence_abs_le (p : ι → ℕ) (F : (ι → Bool) → ℝ) (n : ℕ) :
    |booleanSequence p F n| ≤ observableBound F := by
  unfold booleanSequence
  split_ifs
  · simpa using observableBound_nonneg F
  · exact abs_le_observableBound F _

/-- Actual QHilbert vector associated to an arbitrary finite prime observable. -/
def booleanLift (p : ι → ℕ) (F : (ι → Bool) → ℝ) : QHilbert :=
  encodeQ (booleanSequence p F) (boundedQ_square_summable _ _
    (observableBound_nonneg F) (booleanSequence_abs_le p F))

@[simp] theorem booleanLift_sequence (p : ι → ℕ) (F : (ι → Bool) → ℝ) :
    qSequence (booleanLift p F) = booleanSequence p F :=
  qSequence_encodeQ _ _ (by simp [booleanSequence])

/-- Exact transfer of the finite Gram form to the full integer Q inner product. -/
theorem booleanLift_inner (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (F G : (ι → Bool) → ℝ) :
    inner ℝ (booleanLift p F) (booleanLift p G) =
      tensorExpectation (fun i => primeParameter (p i : ℝ)) (fun b => F b * G b) := by
  rw [qInner_eq_inversePowerMean]
  have hb (n : ℕ) :
      |qSequence (booleanLift p F) n * qSequence (booleanLift p G) n| ≤
        observableBound F * observableBound G := by
    rw [abs_mul, booleanLift_sequence, booleanLift_sequence]
    exact mul_le_mul (booleanSequence_abs_le p F n) (booleanSequence_abs_le p G n)
      (abs_nonneg _) (observableBound_nonneg F)
  rw [inversePowerMean_zero_eq_integral _ hb]
  have he : (fun k : ℕ+ =>
      qSequence (booleanLift p F) (k : ℕ) * qSequence (booleanLift p G) (k : ℕ)) =
      fun k : ℕ+ => F (fun i => divisibilityBool (p i) k) *
        G (fun i => divisibilityBool (p i) k) := by
    funext k
    simp [booleanLift_sequence, booleanSequence, divisibilityBool, ne_of_gt k.pos]
  rw [he]
  exact integral_boolean_observable p hp hinj (fun b => F b * G b)

/-- A normalized centered product, now in the actual QHilbert space. -/
def primeUnitVector (p : ι → ℕ) (A : Finset ι) : QHilbert :=
  booleanLift p (unitMonomial (fun i => primeParameter (p i : ℝ)) A)

/-- All finite centered products are orthonormal under the actual integer law. -/
theorem primeUnitVector_orthonormal (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) : Orthonormal ℝ (primeUnitVector p) := by
  rw [orthonormal_iff_ite]
  intro A B
  rw [primeUnitVector, primeUnitVector, booleanLift_inner p hp hinj]
  apply unitMonomial_gram
  · intro i
    unfold primeParameter
    have hpos : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
    positivity
  · intro i
    unfold primeParameter
    have hgt : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    have hsq : (0 : ℝ) < (p i : ℝ) ^ 2 := by positivity
    rw [div_lt_one hsq]
    nlinarith

/-- Exact finite orthonormal expansion, without omitting the remaining Q energy. -/
theorem primeUnitVector_energy_exact (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (f : QHilbert) (S : Finset (Finset ι)) :
    ‖f‖ ^ 2 = (∑ A ∈ S, (inner ℝ f (primeUnitVector p A)) ^ 2) +
      ‖f - ∑ A ∈ S, (inner ℝ f (primeUnitVector p A)) • primeUnitVector p A‖ ^ 2 := by
  let c : Finset ι → ℝ := fun A => inner ℝ f (primeUnitVector p A)
  have hn : ‖∑ A ∈ S, c A • primeUnitVector p A‖ ^ 2 = ∑ A ∈ S, c A ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      (primeUnitVector_orthonormal p hp hinj).inner_sum c c S]
    simp [pow_two]
  have hi : inner ℝ f (∑ A ∈ S, c A • primeUnitVector p A) = ∑ A ∈ S, c A ^ 2 := by
    rw [inner_sum]
    simp only [real_inner_smul_right, c, pow_two]
  change ‖f‖ ^ 2 = (∑ A ∈ S, c A ^ 2) + ‖f - ∑ A ∈ S, c A • primeUnitVector p A‖ ^ 2
  rw [norm_sub_sq_real, hn, hi]
  ring

end RiemannResearch.RH.QFinitePrimeBasis
