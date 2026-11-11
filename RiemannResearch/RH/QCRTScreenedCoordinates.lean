import RiemannResearch.Analysis.FiniteScreenedCollocation
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteAccretiveCollocation
import RiemannResearch.LinearAlgebra.ObliqueBlockElimination
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QCRTFiniteCollocation
import RiemannResearch.RH.QCRTNestedCutoffs
import RiemannResearch.RH.QPhysicalDifference
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-!
# Actual screened CRT coordinate assembly

Source: CanonicalPrimePowerUpdatesResearch20261107.md, Section 3.
Old columns are every divisor residue greater than one at L; new columns
are the remaining divisor residues at M. All physical Q Gram matrices,
difference-test blocks and sources are formed from these actual vectors.
No inverse bound, energy-growth estimate, or RH assumption is made.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTScreenedCoordinates
open ZetaTwoHilbert QCRTFiniteCollocation QCRTNestedCutoffs QPhysicalDifference
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteScreenedCollocation
open RiemannResearch.Analysis.FiniteAccretiveCollocation
open RiemannResearch.LinearAlgebra.ObliqueBlockElimination

abbrev Old (L : ℕ) := ↥(L.divisors.erase 1)
abbrev New (L M : ℕ) := ↥((M.divisors.erase 1) \ (L.divisors.erase 1))

def oldFamily (L : ℕ) (i : Old L) : QHilbert := qResidue i.val
def newFamily (L M : ℕ) (j : New L M) : QHilbert := qResidue j.val

theorem old_gt_one (L : ℕ) (i : Old L) : 1 < i.val := by
  have h := Finset.mem_erase.mp i.property
  have hp := Nat.pos_of_mem_divisors h.2
  omega

theorem new_gt_one (L M : ℕ) (j : New L M) : 1 < j.val :=
  old_gt_one M ⟨j.val, (Finset.mem_sdiff.mp j.property).1⟩

theorem old_independent (L : ℕ) : LinearIndependent ℝ (oldFamily L) :=
  QCovarianceInvertibility.qResidue_linearIndependent (fun i : Old L => i.val)
    (old_gt_one L) Subtype.val_injective

theorem raw_joined_independent (L M : ℕ) :
    LinearIndependent ℝ (Sum.elim (oldFamily L) (newFamily L M)) := by
  let d : Old L ⊕ New L M → ℕ := Sum.elim Subtype.val Subtype.val
  have hd : ∀ k, 1 < d k := by
    intro k
    cases k with
    | inl i => exact old_gt_one L i
    | inr j => exact new_gt_one L M j
  have hi : Function.Injective d := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl k => exact congrArg Sum.inl (Subtype.ext hab)
      | inr j =>
        change i.val = j.val at hab
        have hn := (Finset.mem_sdiff.mp j.property).2
        exact False.elim (hn (hab ▸ i.property))
    | inr j =>
      cases b with
      | inl i =>
        change j.val = i.val at hab
        have hn := (Finset.mem_sdiff.mp j.property).2
        exact False.elim (hn (hab.symm ▸ i.property))
      | inr k => exact congrArg Sum.inr (Subtype.ext hab)
  have hh := QCovarianceInvertibility.qResidue_linearIndependent d hd hi
  have he : (fun k => qResidue (d k)) = Sum.elim (oldFamily L) (newFamily L M) := by
    ext k
    cases k <;> rfl
  rwa [he] at hh

def screenedFamily (L M : ℕ) : New L M → QHilbert :=
  screened (old_independent L) (newFamily L M)

def joinedFamily (L M : ℕ) : Old L ⊕ New L M → QHilbert :=
  Sum.elim (oldFamily L) (screenedFamily L M)

theorem screened_independent (L M : ℕ) : LinearIndependent ℝ (screenedFamily L M) :=
  screened_linearIndependent (old_independent L) (newFamily L M) (raw_joined_independent L M)

theorem joined_independent (L M : ℕ) : LinearIndependent ℝ (joinedFamily L M) :=
  joined_screened_independent (old_independent L) (newFamily L M)
    (raw_joined_independent L M)

theorem old_screened_orthogonal (L M : ℕ) (i : Old L) (j : New L M) :
    inner ℝ (oldFamily L i) (screenedFamily L M j) = 0 :=
  inner_old_screened (old_independent L) (newFamily L M) i j

/-- Both physical Gram inverses exist for the complete Q inner product. -/
theorem physical_gram_det_pos (L M : ℕ) :
    0 < (gramMatrix (oldFamily L)).det ∧
      0 < (gramMatrix (screenedFamily L M)).det := by
  exact ⟨gramMatrix_det_pos (old_independent L),
    gramMatrix_det_pos (screened_independent L M)⟩

/-- Actual entries of H = V*V - B*G⁻¹B; no truncated-tail inner product occurs. -/
theorem screened_gram_exact (L M : ℕ) (i j : New L M) :
    inner ℝ (screenedFamily L M i) (screenedFamily L M j) =
      inner ℝ (newFamily L M i) (newFamily L M j) -
        ∑ k, inverseCoeff (old_independent L) (newFamily L M i) k *
          cross (oldFamily L) (newFamily L M j) k :=
  screened_gram_entry (old_independent L) (newFamily L M) i j

theorem old_span (L : ℕ) :
    Submodule.span ℝ (Set.range (oldFamily L)) = trialSpace L := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i.val, (Finset.mem_erase.mp i.property).2, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    by_cases he : d = 1
    · subst d
      rw [qResidue_one]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨d, Finset.mem_erase.mpr ⟨he, hd⟩⟩, rfl⟩

theorem joined_span (L M : ℕ) (hM : 0 < M) (hLM : L ∣ M) :
    Submodule.span ℝ (Set.range (joinedFamily L M)) = trialSpace M := by
  change Submodule.span ℝ (Set.range (Sum.elim (oldFamily L)
    (screened (old_independent L) (newFamily L M)))) = _
  rw [span_screened]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    cases k with
    | inl i =>
      exact residue_mem_trial M i.val hM
        ((Nat.dvd_of_mem_divisors (Finset.mem_erase.mp i.property).2).trans hLM)
    | inr j =>
      exact residue_mem_trial M j.val hM
        (Nat.dvd_of_mem_divisors
          (Finset.mem_erase.mp (Finset.mem_sdiff.mp j.property).1).2)
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    by_cases he : d = 1
    · subst d
      rw [qResidue_one]
      exact Submodule.zero_mem _
    · by_cases ho : d ∈ L.divisors.erase 1
      · exact Submodule.subset_span ⟨Sum.inl ⟨d, ho⟩, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inr ⟨d,
          Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨he, hd⟩, ho⟩⟩, rfl⟩

theorem difference_strict (f : QHilbert)
    (hf : inner ℝ f (differenceCLM f) = 0) : f = 0 :=
  eq_zero_of_difference_inner shiftCLM physicalShift_norm_le differenceCLM_injective f hf

/-- The actual full difference-test inverse. -/
def collocationInverse (L M : ℕ) :=
  collocationEquiv differenceCLM.toLinearMap difference_strict (joined_independent L M)

/-- Source is known before solving: target at M minus the old canonical vector. -/
def source (L M : ℕ) (hL : 2 ≤ L) : QHilbert := target M - canonical L hL

def coordinates (L M : ℕ) (hL : 2 ≤ L) : Old L ⊕ New L M → ℝ :=
  solution differenceCLM.toLinearMap difference_strict (joined_independent L M) (source L M hL)

def oldCoordinates (L M : ℕ) (hL : 2 ≤ L) (i : Old L) : ℝ :=
  coordinates L M hL (Sum.inl i)

def newCoordinates (L M : ℕ) (hL : 2 ≤ L) (j : New L M) : ℝ :=
  coordinates L M hL (Sum.inr j)

def A00 (L : ℕ) := block differenceCLM.toLinearMap (oldFamily L) (oldFamily L)
def A01 (L M : ℕ) := block differenceCLM.toLinearMap (oldFamily L) (screenedFamily L M)
def A10 (L M : ℕ) := block differenceCLM.toLinearMap (screenedFamily L M) (oldFamily L)
def A11 (L M : ℕ) := block differenceCLM.toLinearMap (screenedFamily L M) (screenedFamily L M)
def beta0 (L M : ℕ) (hL : 2 ≤ L) := observe differenceCLM.toLinearMap (oldFamily L) (source L M hL)
def beta1 (L M : ℕ) (hL : 2 ≤ L) := observe differenceCLM.toLinearMap (screenedFamily L M) (source L M hL)

def oldCollocationInverse (L : ℕ) :=
  collocationEquiv differenceCLM.toLinearMap difference_strict (old_independent L)

/-- The actual Schur inverse; all kernel hypotheses are discharged by physical D accretivity. -/
def schurInverse (L M : ℕ) :=
  schurEquiv (oldCollocationInverse L) (A01 L M) (A10 L M) (A11 L M)
    (fun x y h0 h1 => block_kernel differenceCLM.toLinearMap difference_strict
      (oldFamily L) (screenedFamily L M) (joined_independent L M) x y h0 h1)

theorem coordinate_equations (L M : ℕ) (hL : 2 ≤ L) :
    A00 L (oldCoordinates L M hL) + A01 L M (newCoordinates L M hL) = beta0 L M hL ∧
    A10 L M (oldCoordinates L M hL) + A11 L M (newCoordinates L M hL) = beta1 L M hL := by
  have hh := solution_match differenceCLM.toLinearMap difference_strict
    (joined_independent L M) (source L M hL)
  have hc : coordinates L M hL = Sum.elim (oldCoordinates L M hL) (newCoordinates L M hL) := by
    ext k
    cases k <;> rfl
  change block differenceCLM.toLinearMap (joinedFamily L M) (joinedFamily L M)
    (coordinates L M hL) = _ at hh
  rw [hc] at hh
  constructor
  · ext i
    have hi := congrFun hh (Sum.inl i)
    change inner ℝ (Fintype.linearCombination ℝ (Sum.elim (oldFamily L) (screenedFamily L M))
      (Sum.elim (oldCoordinates L M hL) (newCoordinates L M hL)))
      (differenceCLM (oldFamily L i)) = _ at hi
    rw [synthesis_join, inner_add_left] at hi
    exact hi
  · ext j
    have hj := congrFun hh (Sum.inr j)
    change inner ℝ (Fintype.linearCombination ℝ (Sum.elim (oldFamily L) (screenedFamily L M))
      (Sum.elim (oldCoordinates L M hL) (newCoordinates L M hL)))
      (differenceCLM (screenedFamily L M j)) = _ at hj
    rw [synthesis_join, inner_add_left] at hj
    exact hj

/-- The exact screened test source, retaining the signed old-source correction. -/
theorem beta1_exact (L M : ℕ) (hL : 2 ≤ L) (j : New L M) :
    beta1 L M hL j = observe differenceCLM.toLinearMap (newFamily L M) (source L M hL) j -
      ∑ i, inverseCoeff (old_independent L) (newFamily L M j) i * beta0 L M hL i :=
  screened_observe differenceCLM.toLinearMap (old_independent L) (newFamily L M) (source L M hL) j

/-- Actual oblique Schur coordinates. This source is not the physical Gram response. -/
theorem schur_coordinates (L M : ℕ) (hL : 2 ≤ L) :
    oldCoordinates L M hL = (oldCollocationInverse L).symm
      (beta0 L M hL - A01 L M (newCoordinates L M hL)) ∧
    newCoordinates L M hL = (schurInverse L M).symm
      (beta1 L M hL - A10 L M ((oldCollocationInverse L).symm (beta0 L M hL))) := by
  obtain ⟨h0, h1⟩ := coordinate_equations L M hL
  have he := block_elimination (A00 L) (oldCollocationInverse L).symm.toLinearMap
    (A01 L M) (A10 L M) (A11 L M)
    (fun u => (oldCollocationInverse L).symm_apply_apply u)
    (oldCoordinates L M hL) (beta0 L M hL) (newCoordinates L M hL) (beta1 L M hL) h0 h1
  constructor
  · apply (oldCollocationInverse L).injective
    rw [LinearEquiv.apply_symm_apply]
    exact eq_sub_of_add_eq h0
  · apply (schurInverse L M).injective
    rw [LinearEquiv.apply_symm_apply]
    exact he.2

/-- The computed coordinates synthesize exactly the repository's canonical update. -/
theorem canonical_assembly (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M) :
    Fintype.linearCombination ℝ (oldFamily L) (oldCoordinates L M hL) +
      Fintype.linearCombination ℝ (screenedFamily L M) (newCoordinates L M hL) =
        (canonical M hM : QHilbert) - canonical L hL := by
  have hf : (canonical M hM : QHilbert) - canonical L hL ∈
      Submodule.span ℝ (Set.range (joinedFamily L M)) := by
    rw [joined_span L M (by omega) hLM]
    exact (trialSpace M).sub_mem (canonical M hM).property
      (trialSpace_mono_of_dvd L M (by omega) hLM (canonical L hL).property)
  have hm : observe differenceCLM.toLinearMap (joinedFamily L M)
      ((canonical M hM : QHilbert) - canonical L hL) =
      observe differenceCLM.toLinearMap (joinedFamily L M) (source L M hL) := by
    ext k
    change inner ℝ ((canonical M hM : QHilbert) - canonical L hL)
      (differenceCLM (joinedFamily L M k)) =
      inner ℝ (target M - canonical L hL) (differenceCLM (joinedFamily L M k))
    rw [inner_sub_left, inner_sub_left]
    congr 1
    apply inner_eq_of_divisor_tests M _ _ (canonical_match M hM)
    apply difference_mem_cell M (by omega)
    rw [← joined_span L M (by omega) hLM]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hh := solution_synthesis_eq differenceCLM.toLinearMap difference_strict
    (joined_independent L M) (source L M hL) _ hf hm
  change Fintype.linearCombination ℝ (joinedFamily L M) (coordinates L M hL) = _ at hh
  have hc : coordinates L M hL = Sum.elim (oldCoordinates L M hL) (newCoordinates L M hL) := by
    ext k
    cases k <;> rfl
  rw [hc] at hh
  exact (synthesis_join (oldFamily L) (screenedFamily L M) _ _).symm.trans hh

def baseCoordinates (L : ℕ) : Old L → ℝ :=
  solution differenceCLM.toLinearMap difference_strict (old_independent L) (target L)

/-- The physical Gram right-hand side is the response pairing, not the Schur source. -/
theorem physical_response_exact (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M)
    (hLM : L ∣ M) (j : New L M) :
    gram (screenedFamily L M) (newCoordinates L M hL) j =
      inner ℝ (screenedFamily L M j) ((canonical M hM : QHilbert) - canonical L hL) := by
  rw [← canonical_assembly L M hL hM hLM, inner_add_right]
  have ho : inner ℝ (screenedFamily L M j)
      (Fintype.linearCombination ℝ (oldFamily L) (oldCoordinates L M hL)) = 0 := by
    rw [real_inner_comm, inner_synthesis_left]
    simp only [screenedFamily, inner_old_screened, mul_zero, Finset.sum_const_zero]
  rw [ho, zero_add]
  rfl

theorem base_synthesis (L : ℕ) (hL : 2 ≤ L) :
    Fintype.linearCombination ℝ (oldFamily L) (baseCoordinates L) = (canonical L hL : QHilbert) := by
  apply solution_synthesis_eq differenceCLM.toLinearMap difference_strict (old_independent L)
  · rw [old_span]
    exact (canonical L hL).property
  · ext i
    apply inner_eq_of_divisor_tests L _ _ (canonical_match L hL)
    apply difference_mem_cell L (by omega)
    rw [← old_span]
    exact Submodule.subset_span ⟨i, rfl⟩

/-- Exact signed physical coordinate energy of the canonical CRT update. -/
theorem canonical_energy_exact (L M : ℕ) (hL : 2 ≤ L) (hM : 2 ≤ M) (hLM : L ∣ M) :
    ‖(canonical M hM : QHilbert)‖ ^ 2 - ‖(canonical L hL : QHilbert)‖ ^ 2 =
      2 * (∑ i, baseCoordinates L i * gram (oldFamily L) (oldCoordinates L M hL) i) +
        (∑ i, oldCoordinates L M hL i * gram (oldFamily L) (oldCoordinates L M hL) i) +
        (∑ j, newCoordinates L M hL j * gram (screenedFamily L M) (newCoordinates L M hL) j) := by
  have ha := canonical_assembly L M hL hM hLM
  have he : (canonical M hM : QHilbert) =
      Fintype.linearCombination ℝ (oldFamily L) (baseCoordinates L) +
      Fintype.linearCombination ℝ (oldFamily L) (oldCoordinates L M hL) +
      Fintype.linearCombination ℝ (screenedFamily L M) (newCoordinates L M hL) := by
    rw [base_synthesis L hL, add_assoc, ha]
    abel
  rw [he, ← base_synthesis L hL]
  exact signed_energy (old_independent L) (newFamily L M)
    (baseCoordinates L) (oldCoordinates L M hL) (newCoordinates L M hL)

end RiemannResearch.RH.QCRTScreenedCoordinates
