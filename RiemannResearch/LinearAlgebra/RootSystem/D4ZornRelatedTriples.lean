/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.Tactic.FinCases
import RiemannResearch.LinearAlgebra.RootSystem.D4OrthogonalRelatedTriples
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornOctonion

/-!
# Correct outer S3 action on split-Zorn related triples

For the concrete split Zorn octonion, even diagram permutations relabel the
three related-triple components. Odd permutations also conjugate each
component by octonion conjugation. This file constructs the resulting literal
S3 action, restricts it to the tensor stabilizer, and proves every nonidentity
diagram symmetry is non-inner when minus one acts nontrivially.

The conjugation in the odd part is essential; pure relabeling is only the
cyclic A3 action. See Alsaody--Gille, Remark 3.2 and Lemma 3.3:
<https://arxiv.org/abs/1704.05229>.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality
namespace Zorn

universe u

noncomputable section

variable (K : Type u) [CommRing K]

abbrev Isometry :=
  quadraticIsometryGroup K (Octonion K) (normForm K)

abbrev Tuple := TrialityLabel → Isometry K

def conjugationIsometry : Isometry K :=
  ⟨conjugationLinearEquiv K, by
    intro x
    simp⟩

def conjugateIsometry (g : Isometry K) : Isometry K :=
  conjugationIsometry K * g * conjugationIsometry K

@[simp] theorem conjugateIsometry_apply (g : Isometry K) (x : Octonion K) :
    (conjugateIsometry K g).1 x =
      conjugate K (g.1 (conjugate K x)) :=
  rfl

@[simp] theorem conjugateIsometry_mul (g h : Isometry K) :
    conjugateIsometry K (g * h) =
      conjugateIsometry K g * conjugateIsometry K h := by
  apply Subtype.ext
  ext x
  simp [conjugateIsometry, conjugationIsometry]

@[simp] theorem conjugateIsometry_involutive (g : Isometry K) :
    conjugateIsometry K (conjugateIsometry K g) = g := by
  apply Subtype.ext
  ext x
  simp [conjugateIsometry, conjugationIsometry]

def tupleConjugation : MulAut (Tuple K) where
  toFun g l := conjugateIsometry K (g l)
  invFun g l := conjugateIsometry K (g l)
  left_inv g := by
    funext l
    simp
  right_inv g := by
    funext l
    simp
  map_mul' g h := by
    funext l
    simp

abbrev DiagramEven (σ : DiagramSymmetry) : Prop :=
  σ = 1 ∨ σ = trialityCycle ∨ σ = trialityCycle ^ 2

theorem diagramSymmetry_cases (σ : DiagramSymmetry) :
    σ = 1 ∨ σ = trialityCycle ∨ σ = trialityCycle ^ 2 ∨
      σ = halfSpinSwap ∨ σ = trialityCycle * halfSpinSwap ∨
      σ = trialityCycle ^ 2 * halfSpinSwap := by
  fin_cases σ <;> decide

theorem diagramEven_inv_iff (σ : DiagramSymmetry) :
    DiagramEven σ⁻¹ ↔ DiagramEven σ := by
  rcases diagramSymmetry_cases σ with
    rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem diagramEven_mul_iff (σ τ : DiagramSymmetry) :
    DiagramEven (σ * τ) ↔ (DiagramEven σ ↔ DiagramEven τ) := by
  rcases diagramSymmetry_cases σ with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases diagramSymmetry_cases τ with
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def pureTupleRelabel (σ : DiagramSymmetry) : MulAut (Tuple K) :=
  orthogonalTupleRelabel K (Octonion K) (normForm K) σ

def tupleTwistedRelabel (σ : DiagramSymmetry) : MulAut (Tuple K) :=
  if DiagramEven σ then pureTupleRelabel K σ
  else tupleConjugation K * pureTupleRelabel K σ

def tupleTwistedRelabelAction :
    DiagramSymmetry →* MulAut (Tuple K) where
  toFun := tupleTwistedRelabel K
  map_one' := by
    ext g l
    simp [tupleTwistedRelabel, pureTupleRelabel, DiagramEven,
      orthogonalTupleRelabel]
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    funext l
    by_cases hσ : DiagramEven σ <;> by_cases hτ : DiagramEven τ
    · have hm : DiagramEven (σ * τ) :=
        (diagramEven_mul_iff σ τ).2
          ⟨fun _ => hτ, fun _ => hσ⟩
      simp [tupleTwistedRelabel, hσ, hτ, hm, pureTupleRelabel,
        orthogonalTupleRelabel]
    · have hm : ¬DiagramEven (σ * τ) := by
        intro h
        exact hτ ((diagramEven_mul_iff σ τ).1 h |>.mp hσ)
      simp [tupleTwistedRelabel, hσ, hτ, hm, pureTupleRelabel,
        tupleConjugation, orthogonalTupleRelabel]
    · have hm : ¬DiagramEven (σ * τ) := by
        intro h
        exact hσ ((diagramEven_mul_iff σ τ).1 h |>.mpr hτ)
      simp [tupleTwistedRelabel, hσ, hτ, hm, pureTupleRelabel,
        orthogonalTupleRelabel]
    · have hm : DiagramEven (σ * τ) :=
        (diagramEven_mul_iff σ τ).2
          ⟨fun hs => (hσ hs).elim, fun ht => (hτ ht).elim⟩
      simp [tupleTwistedRelabel, hσ, hτ, hm, pureTupleRelabel,
        tupleConjugation, orthogonalTupleRelabel]

def trialityEval (x : TrialityLabel → Octonion K) : K :=
  trialityTensor K (x .vector) (x .halfSpinPlus) (x .halfSpinMinus)

def valueTwistedRelabel (σ : DiagramSymmetry)
    (x : TrialityLabel → Octonion K) :
    TrialityLabel → Octonion K :=
  fun l =>
    if DiagramEven σ then x (σ⁻¹ l)
    else conjugate K (x (σ⁻¹ l))

theorem trialityEval_valueTwistedRelabel
    (σ : DiagramSymmetry) (x : TrialityLabel → Octonion K) :
    trialityEval K (valueTwistedRelabel K σ x) = trialityEval K x := by
  rcases diagramSymmetry_cases σ with
    rfl | rfl | rfl | rfl | rfl | rfl
  · simp [valueTwistedRelabel, DiagramEven, trialityEval]
  · change
      trialityTensor K (x .halfSpinMinus) (x .vector)
          (x .halfSpinPlus) =
        trialityTensor K (x .vector) (x .halfSpinPlus)
          (x .halfSpinMinus)
    exact (trialityTensor_cycle_two K _ _ _).symm
  · change
      trialityTensor K (x .halfSpinPlus) (x .halfSpinMinus)
          (x .vector) =
        trialityTensor K (x .vector) (x .halfSpinPlus)
          (x .halfSpinMinus)
    exact (trialityTensor_cycle K _ _ _).symm
  · change
      trialityTensor K (conjugate K (x .vector))
          (conjugate K (x .halfSpinMinus))
          (conjugate K (x .halfSpinPlus)) =
        trialityTensor K (x .vector) (x .halfSpinPlus)
          (x .halfSpinMinus)
    exact trialityTensor_conjugate_reflection K _ _ _
  · change
      trialityTensor K (conjugate K (x .halfSpinPlus))
          (conjugate K (x .vector))
          (conjugate K (x .halfSpinMinus)) =
        trialityTensor K (x .vector) (x .halfSpinPlus)
          (x .halfSpinMinus)
    rw [trialityTensor_conjugate_reflection]
    exact (trialityTensor_cycle K _ _ _).symm
  · change
      trialityTensor K (conjugate K (x .halfSpinMinus))
          (conjugate K (x .halfSpinPlus))
          (conjugate K (x .vector)) =
        trialityTensor K (x .vector) (x .halfSpinPlus)
          (x .halfSpinMinus)
    rw [trialityTensor_conjugate_reflection]
    exact (trialityTensor_cycle_two K _ _ _).symm

def relatedTripleGroup : Subgroup (Tuple K) where
  carrier := {g | ∀ x,
    trialityEval K (fun l => (g l).1 (x l)) = trialityEval K x}
  one_mem' := by
    intro x
    rfl
  mul_mem' := by
    intro g h hg hh x
    calc
      trialityEval K (fun l => ((g * h) l).1 (x l)) =
          trialityEval K (fun l => (g l).1 ((h l).1 (x l))) := by
            rfl
      _ = trialityEval K (fun l => (h l).1 (x l)) := hg _
      _ = trialityEval K x := hh x
  inv_mem' := by
    intro g hg x
    have h := hg (fun l => ((g l)⁻¹).1 (x l))
    have hc :
        (fun l => (g l).1 (((g l)⁻¹).1 (x l))) = x := by
      funext l
      exact (g l).1.apply_symm_apply (x l)
    rw [hc] at h
    exact h.symm

theorem tupleTwistedRelabel_apply
    (σ : DiagramSymmetry) (g : Tuple K)
    (x : TrialityLabel → Octonion K) (l : TrialityLabel) :
    ((tupleTwistedRelabel K σ g) l).1 (x l) =
      valueTwistedRelabel K σ
        (fun k => (g k).1 (valueTwistedRelabel K σ⁻¹ x k)) l := by
  by_cases hσ : DiagramEven σ
  · have hi : DiagramEven σ⁻¹ := (diagramEven_inv_iff σ).2 hσ
    simp [tupleTwistedRelabel, pureTupleRelabel, valueTwistedRelabel,
      orthogonalTupleRelabel, hσ, hi]
  · have hi : ¬DiagramEven σ⁻¹ := by
      intro h
      exact hσ ((diagramEven_inv_iff σ).1 h)
    simp [tupleTwistedRelabel, pureTupleRelabel, tupleConjugation,
      valueTwistedRelabel, orthogonalTupleRelabel, conjugateIsometry,
      conjugationIsometry, hσ, hi]

theorem tupleTwistedRelabel_mem_related
    (σ : DiagramSymmetry) (g : relatedTripleGroup K) :
    tupleTwistedRelabel K σ g.1 ∈ relatedTripleGroup K := by
  intro x
  rw [show
    (fun l => ((tupleTwistedRelabel K σ g.1) l).1 (x l)) =
      valueTwistedRelabel K σ
        (fun k => (g.1 k).1 (valueTwistedRelabel K σ⁻¹ x k)) by
          funext l
          exact tupleTwistedRelabel_apply K σ g.1 x l]
  rw [trialityEval_valueTwistedRelabel]
  rw [g.2]
  exact trialityEval_valueTwistedRelabel K σ⁻¹ x

def relatedTripleRelabel (σ : DiagramSymmetry) :
    MulAut (relatedTripleGroup K) where
  toFun g :=
    ⟨tupleTwistedRelabel K σ g.1,
      tupleTwistedRelabel_mem_related K σ g⟩
  invFun g :=
    ⟨tupleTwistedRelabel K σ⁻¹ g.1,
      tupleTwistedRelabel_mem_related K σ⁻¹ g⟩
  left_inv g := by
    apply Subtype.ext
    have h := congrArg
      (fun a : MulAut (Tuple K) => a g.1)
      ((tupleTwistedRelabelAction K).map_mul σ⁻¹ σ)
    change tupleTwistedRelabel K σ⁻¹
      (tupleTwistedRelabel K σ g.1) = g.1
    calc
      _ = ((tupleTwistedRelabelAction K σ⁻¹) *
          (tupleTwistedRelabelAction K σ)) g.1 := rfl
      _ = tupleTwistedRelabelAction K (σ⁻¹ * σ) g.1 := h.symm
      _ = g.1 := by simp
  right_inv g := by
    apply Subtype.ext
    have h := congrArg
      (fun a : MulAut (Tuple K) => a g.1)
      ((tupleTwistedRelabelAction K).map_mul σ σ⁻¹)
    change tupleTwistedRelabel K σ
      (tupleTwistedRelabel K σ⁻¹ g.1) = g.1
    calc
      _ = ((tupleTwistedRelabelAction K σ) *
          (tupleTwistedRelabelAction K σ⁻¹)) g.1 := rfl
      _ = tupleTwistedRelabelAction K (σ * σ⁻¹) g.1 := h.symm
      _ = g.1 := by simp
  map_mul' g h := by
    apply Subtype.ext
    exact (tupleTwistedRelabel K σ).map_mul g.1 h.1

def relatedTripleOuterAction :
    DiagramSymmetry →* MulAut (relatedTripleGroup K) where
  toFun := relatedTripleRelabel K
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    exact DFunLike.congr_fun (tupleTwistedRelabelAction K).map_one g.1
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    exact DFunLike.congr_fun
      ((tupleTwistedRelabelAction K).map_mul σ τ) g.1

def centralSignMarker (i : TrialityLabel) :
    relatedTripleGroup K :=
  ⟨fun l => if l = i then 1 else negQuadraticIsometry K
      (Octonion K) (normForm K), by
    intro x
    cases i <;>
      simp [trialityEval, trialityTensor, normPolar, paraMul, mul,
        conjugate, norm, negQuadraticIsometry] <;> ring⟩

theorem centralSignMarker_mem_center (i : TrialityLabel) :
    centralSignMarker K i ∈ Subgroup.center (relatedTripleGroup K) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  funext l
  apply Subtype.ext
  ext x
  by_cases hli : l = i
  · subst l
    simp [centralSignMarker]
  · simp [centralSignMarker, hli, negQuadraticIsometry]

theorem relatedTripleRelabel_centralSignMarker
    (σ : DiagramSymmetry) (i : TrialityLabel) :
    relatedTripleOuterAction K σ (centralSignMarker K i) =
      centralSignMarker K (σ i) := by
  apply Subtype.ext
  funext l
  apply Subtype.ext
  ext x
  by_cases hσ : DiagramEven σ
  · by_cases hli : σ⁻¹ l = i
    · have hl : l = σ i := by
        simpa using congrArg σ hli
      simp [relatedTripleOuterAction, relatedTripleRelabel,
        tupleTwistedRelabel, pureTupleRelabel, orthogonalTupleRelabel,
        centralSignMarker, hσ, hl]
    · have hl : l ≠ σ i := by
        intro hl
        apply hli
        simp [hl]
      have hli' : (Equiv.symm σ) l ≠ i := hli
      simp [relatedTripleOuterAction, relatedTripleRelabel,
        tupleTwistedRelabel, pureTupleRelabel, orthogonalTupleRelabel,
        centralSignMarker, negQuadraticIsometry, hσ, hli', hl]
  · by_cases hli : σ⁻¹ l = i
    · have hl : l = σ i := by
        simpa using congrArg σ hli
      simp [relatedTripleOuterAction, relatedTripleRelabel,
        tupleTwistedRelabel, pureTupleRelabel, tupleConjugation,
        orthogonalTupleRelabel, centralSignMarker, conjugateIsometry,
        conjugationIsometry, hσ, hl]
    · have hl : l ≠ σ i := by
        intro hl
        apply hli
        simp [hl]
      have hli' : (Equiv.symm σ) l ≠ i := hli
      simp [relatedTripleOuterAction, relatedTripleRelabel,
        tupleTwistedRelabel, pureTupleRelabel, tupleConjugation,
        orthogonalTupleRelabel, centralSignMarker, conjugateIsometry,
        conjugationIsometry, negQuadraticIsometry, hσ, hli', hl]

theorem centralSignMarker_injective
    (v : Octonion K) (hv : -v ≠ v) :
    Function.Injective (centralSignMarker K) := by
  intro i j hij
  by_contra hne
  have hc := congrArg
    (fun g : relatedTripleGroup K => ((g.1 i).1 v)) hij
  simp [centralSignMarker, hne, negQuadraticIsometry] at hc
  exact hv hc.symm

theorem relatedTripleRelabel_not_inner_of_ne_one
    (v : Octonion K) (hv : -v ≠ v)
    (σ : DiagramSymmetry) (hσ : σ ≠ 1) :
    ¬IsInnerAutomorphism (relatedTripleOuterAction K σ) := by
  intro hinner
  have hex : ∃ i : TrialityLabel, σ i ≠ i := by
    by_contra h
    push Not at h
    apply hσ
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hex
  have hfix := hinner.fix_of_mem_center
    (centralSignMarker_mem_center K i)
  rw [relatedTripleRelabel_centralSignMarker K σ i] at hfix
  exact hi (centralSignMarker_injective K v hv hfix)

theorem relatedTripleOuterAction_injective
    (v : Octonion K) (hv : -v ≠ v) :
    Function.Injective (relatedTripleOuterAction K) :=
  action_injective_of_nontrivial_not_inner
    (relatedTripleOuterAction K)
    (relatedTripleRelabel_not_inner_of_ne_one K v hv)

/-- A coordinate vector detecting the three central sign markers. -/
def standardSignWitness : Octonion K :=
  ![1, 0, 0, 0, 0, 0, 0, 0]

/-- When two is invertible, negation moves the standard sign witness. -/
theorem standardSignWitness_neg_ne [Nontrivial K] [Invertible (2 : K)] :
    -standardSignWitness K ≠ standardSignWitness K := by
  intro h
  have hc := congrArg (fun x : Octonion K => x 0) h
  simp [standardSignWitness] at hc
  have htwo : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  apply htwo
  calc
    (2 : K) = 1 + 1 := by ring
    _ = (-1 : K) + 1 :=
      congrArg (fun z : K => z + 1) hc.symm
    _ = 0 := neg_add_cancel 1

/-- Every nonidentity concrete split-Zorn diagram symmetry is outer when two
is invertible. -/
theorem relatedTripleOuterAction_not_inner
    [Nontrivial K] [Invertible (2 : K)] (σ : DiagramSymmetry) (hσ : σ ≠ 1) :
    ¬IsInnerAutomorphism (relatedTripleOuterAction K σ) :=
  relatedTripleRelabel_not_inner_of_ne_one K
    (standardSignWitness K) (standardSignWitness_neg_ne K) σ hσ

/-- The concrete split-Zorn outer diagram action is faithful when two is
invertible. -/
theorem relatedTripleOuterAction_injective_of_invertible_two
    [Nontrivial K] [Invertible (2 : K)] :
    Function.Injective (relatedTripleOuterAction K) :=
  relatedTripleOuterAction_injective K
    (standardSignWitness K) (standardSignWitness_neg_ne K)

end

end Zorn
end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
