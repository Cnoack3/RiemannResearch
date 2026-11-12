import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.NumberTheory.PrimeCRTSelectors
import RiemannResearch.RH.PrimeTreeConstants
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Inverse-Gram projection onto the physical Q prime atoms

Source: the user's finite-CRT and increasing-subspace argument, 2026-11-12.
For every d in QHilbert, the inverse-Gram finite sums are exactly the
orthogonal projections onto the first N prime atoms. They converge in Q norm
to the projection onto the closed prime-atom span, with the exact residual
energy identity.

The proof uses full Q inner products. Finite CRT proves linear independence;
Hilbert-space projection convergence supplies the infinite limit.
-/

noncomputable section
open Filter
open scoped BigOperators Topology Matrix
namespace RiemannResearch.RH.QPrimeGramProjection
open ZetaTwoHilbert ArithmeticCumulative
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.NumberTheory.PrimeCRTSelectors

/-- The literal physical prime atoms are independent, by positive CRT sites. -/
theorem primeResidue_linearIndependent {ι : Type*} [Finite ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    LinearIndependent ℝ (fun i => qResidue (p i)) := by
  classical
  letI := Fintype.ofFinite ι
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  obtain ⟨n, _hn, hres⟩ := exists_positive_prime_selector p hp hinj i
  have hatom (j : ι) : qSequence (qResidue (p j)) n =
      if j = i then 1 / (p i : ℝ) else 0 := by
    rw [qSequence_qResidue]
    unfold residueFraction
    rw [hres j]
    split_ifs with h
    · subst j
      simp
    · simp
  have hs : qSequence (∑ j, c j • qResidue (p j)) n =
      ∑ j, c j * qSequence (qResidue (p j)) n := by
    change qSequenceLinear (∑ j, c j • qResidue (p j)) n = _
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have he := congrArg (fun f : QHilbert => qSequence f n) hc
  rw [hs] at he
  have hz : qSequence (0 : QHilbert) n = 0 :=
    congrFun (map_zero qSequenceLinear) n
  rw [hz] at he
  have hi : c i * (1 / (p i : ℝ)) = 0 := by
    simpa [hatom] using he
  exact (mul_eq_zero.mp hi).resolve_right
    (one_div_ne_zero (by exact_mod_cast (hp i).ne_zero))

/-- Zero-based enumeration, so primeAt 0 is the first prime. -/
def primeAt (i : ℕ) : ℕ := Nat.nth Nat.Prime i

theorem primeAt_prime (i : ℕ) : (primeAt i).Prime :=
  Nat.nth_mem i (fun hf => (Nat.infinite_setOfPred_prime hf).elim)

theorem primeAt_injective : Function.Injective primeAt :=
  Nat.nth_injective Nat.infinite_setOfPred_prime

theorem primeAt_covers (p : ℕ) (hp : p.Prime) : ∃ i, primeAt i = p :=
  ⟨Nat.count Nat.Prime p, Nat.nth_count hp⟩

def atom (i : ℕ) : QHilbert := qResidue (primeAt i)
def family (N : ℕ) : Fin N → QHilbert := fun i => atom i.val

theorem family_linearIndependent (N : ℕ) : LinearIndependent ℝ (family N) :=
  primeResidue_linearIndependent (fun i : Fin N => primeAt i.val)
    (fun i => primeAt_prime i.val) (primeAt_injective.comp Fin.val_injective)

abbrev finiteSpace (N : ℕ) : Submodule ℝ QHilbert := walkSpan atom id N

theorem dictionaryClosure_eq_primeClosure :
    dictionaryClosure atom = primeAtomSpan.topologicalClosure := by
  have hr : Set.range atom = {x | ∃ p : ℕ, p.Prime ∧ x = qResidue p} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨primeAt i, primeAt_prime i, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨i, hi⟩ := primeAt_covers p hp
      exact ⟨i, by simp only [atom, hi]⟩
  simp only [dictionaryClosure, primeAtomSpan, hr]

def limitProjection (d : QHilbert) : QHilbert :=
  primeAtomSpan.topologicalClosure.starProjection d

def gram (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := gramMatrix (family N)
def rhs (d : QHilbert) (N : ℕ) : Fin N → ℝ := cross (family N) d
def coefficients (d : QHilbert) (N : ℕ) : Fin N → ℝ :=
  (gram N)⁻¹.mulVec (rhs d N)
def approximant (d : QHilbert) (N : ℕ) : QHilbert :=
  ∑ i : Fin N, coefficients d N i • family N i

theorem gram_apply (N : ℕ) (i j : Fin N) :
    gram N i j = inner ℝ (qResidue (primeAt i.val)) (qResidue (primeAt j.val)) := rfl

theorem rhs_apply (d : QHilbert) (N : ℕ) (i : Fin N) :
    rhs d N i = inner ℝ d (qResidue (primeAt i.val)) :=
  real_inner_comm _ _

theorem gram_posDef (N : ℕ) : (gram N).PosDef :=
  gramMatrix_posDef (family_linearIndependent N)

theorem gram_det_pos (N : ℕ) : 0 < (gram N).det :=
  gramMatrix_det_pos (family_linearIndependent N)

theorem gram_isUnit (N : ℕ) : IsUnit (gram N) := (gram_posDef N).isUnit

theorem gram_mul_inverse (N : ℕ) : gram N * (gram N)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ne_of_gt (gram_det_pos N)))

/-- Literal inverse-matrix coefficients give the actual Q projection. -/
theorem approximant_eq_projection (d : QHilbert) (N : ℕ) :
    approximant d N = (finiteSpace N).starProjection d := by
  change Fintype.linearCombination ℝ (family N)
    ((gramMatrix (family N))⁻¹.mulVec (cross (family N) d)) =
      (synthesisSpan (family N)).starProjection d
  rw [← inverseCoeff_eq_inv_mulVec (family_linearIndependent N) d]
  exact synthesis_inverseCoeff_eq_projection (family_linearIndependent N) d

theorem approximant_tendsto (d : QHilbert) :
    Tendsto (fun N => approximant d N) atTop (𝓝 (limitProjection d)) := by
  simp_rw [approximant_eq_projection]
  have h := walkProjection_tendsto atom id Function.surjective_id d
  simpa only [dictionaryClosure_eq_primeClosure, limitProjection] using h

theorem atom_mem_primeClosure (i : ℕ) : atom i ∈ primeAtomSpan.topologicalClosure :=
  primeAtomSpan.le_topologicalClosure
    (Submodule.subset_span ⟨primeAt i, primeAt_prime i, rfl⟩)

/-- The right-hand side b_N is unchanged when d is replaced by d_W. -/
theorem rhs_limitProjection (d : QHilbert) (N : ℕ) :
    rhs (limitProjection d) N = rhs d N := by
  funext i
  have h := Submodule.inner_right_of_mem_orthogonal (atom_mem_primeClosure i.val)
    (Submodule.sub_starProjection_mem_orthogonal
      (K := primeAtomSpan.topologicalClosure) d)
  rw [inner_sub_right] at h
  exact (sub_eq_zero.mp h).symm

theorem coefficients_limitProjection (d : QHilbert) (N : ℕ) :
    coefficients (limitProjection d) N = coefficients d N := by
  unfold coefficients
  rw [rhs_limitProjection]

theorem approximant_limitProjection (d : QHilbert) (N : ℕ) :
    approximant (limitProjection d) N = approximant d N := by
  simp only [approximant, coefficients_limitProjection]

/-- Exact energy identity requested by the user, with the full Q Gram matrix. -/
theorem energy_identity (d : QHilbert) (N : ℕ) :
    ‖limitProjection d - approximant d N‖ ^ 2 =
      ‖limitProjection d‖ ^ 2 - dotProduct (rhs d N) ((gram N)⁻¹.mulVec (rhs d N)) := by
  have h := residual_matrix_value (family_linearIndependent N) (limitProjection d)
  change ‖limitProjection d - approximant (limitProjection d) N‖ ^ 2 =
    ‖limitProjection d‖ ^ 2 -
      dotProduct (rhs (limitProjection d) N)
        ((gram N)⁻¹.mulVec (rhs (limitProjection d) N)) at h
  simpa only [approximant_limitProjection, rhs_limitProjection] using h

theorem squared_error_tendsto_zero (d : QHilbert) :
    Tendsto (fun N => ‖limitProjection d - approximant d N‖ ^ 2)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ => limitProjection d) atTop
      (𝓝 (limitProjection d)) := tendsto_const_nhds
  have h := (hc.sub (approximant_tendsto d)).norm.pow 2
  simpa using h

theorem energy_deficit_tendsto_zero (d : QHilbert) :
    Tendsto (fun N => ‖limitProjection d‖ ^ 2 -
      dotProduct (rhs d N) ((gram N)⁻¹.mulVec (rhs d N)))
      atTop (𝓝 0) := by
  simpa only [← energy_identity] using squared_error_tendsto_zero d

end RiemannResearch.RH.QPrimeGramProjection
