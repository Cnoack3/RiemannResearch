/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.LinearAlgebra.QuadraticForm.Basic
import RiemannResearch.LinearAlgebra.RootSystem.D4RelatedTriples

/-!
# Orthogonal related triples and genuine outer D4 triality

For a quadratic module with a symmetric trilinear tensor, this file constructs
the group of tensor-preserving triples of quadratic isometries. Permuting the
three components gives a literal S3 action. Central sign markers prove that
every nonidentity relabeling is non-inner.

This is an orthogonal related-triples group over a ring. It is not identified
here with a split Spin(8) group scheme or with Mathlib's pointwise spin group.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open RiemannResearch.LinearAlgebra

universe uK uV

section RelatedTriples

variable (K : Type uK) [CommRing K]
variable (V : Type uV) [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

/-- A trilinear tensor on one common triality space. -/
abbrev OrthogonalTrialityTensor := V →ₗ[K] V →ₗ[K] V →ₗ[K] K

/-- Evaluate a triality tensor in the fixed order `V, S+, S-`. -/
def orthogonalTrialityTensorEval (t : OrthogonalTrialityTensor K V)
    (x : TrialityLabel → V) : K :=
  t (x .vector) (x .halfSpinPlus) (x .halfSpinMinus)

/-- Full invariance under permutation of the three tensor slots. -/
def OrthogonalTrialityTensor.IsSymmetric (t : OrthogonalTrialityTensor K V) : Prop :=
  ∀ (σ : DiagramSymmetry) (x : TrialityLabel → V),
    orthogonalTrialityTensorEval K V t (fun l => x (σ l)) =
      orthogonalTrialityTensorEval K V t x

/-- The pointwise group of linear automorphisms preserving `Q`. -/
def quadraticIsometryGroup : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x, Q (g x) = Q x}
  one_mem' := by
    intro x
    rfl
  mul_mem' := by
    intro g h hg hh x
    exact (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have h := hg (g.symm x)
    rw [g.apply_symm_apply] at h
    exact h.symm

/-- Three componentwise quadratic isometries, indexed by the triality labels. -/
abbrev OrthogonalTrialityTuple :=
  TrialityLabel → quadraticIsometryGroup K V Q

/-- Orthogonal triples preserving the symmetric trilinear tensor. -/
def orthogonalRelatedTripleGroup (t : OrthogonalTrialityTensor K V) :
    Subgroup (OrthogonalTrialityTuple K V Q) where
  carrier := {g | ∀ x,
    orthogonalTrialityTensorEval K V t (fun l => (g l).1 (x l)) =
      orthogonalTrialityTensorEval K V t x}
  one_mem' := by
    intro x
    rfl
  mul_mem' := by
    intro g h hg hh x
    calc
      orthogonalTrialityTensorEval K V t (fun l => ((g * h) l).1 (x l)) =
          orthogonalTrialityTensorEval K V t
            (fun l => (g l).1 ((h l).1 (x l))) := by rfl
      _ = orthogonalTrialityTensorEval K V t (fun l => (h l).1 (x l)) := hg _
      _ = orthogonalTrialityTensorEval K V t x := hh x
  inv_mem' := by
    intro g hg x
    have h := hg (fun l => ((g l)⁻¹).1 (x l))
    have hc : (fun l => (g l).1 (((g l)⁻¹).1 (x l))) = x := by
      funext l
      exact (g l).1.apply_symm_apply (x l)
    rw [hc] at h
    exact h.symm

/-- Relabel the three components of an orthogonal tuple. -/
def orthogonalTupleRelabel (σ : DiagramSymmetry) :
    MulAut (OrthogonalTrialityTuple K V Q) where
  toFun g l := g (σ⁻¹ l)
  invFun g l := g (σ l)
  left_inv g := by
    funext l
    simp
  right_inv g := by
    funext l
    simp
  map_mul' g h := by
    rfl

theorem orthogonalTupleRelabel_mem_related
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V)
    (σ : DiagramSymmetry)
    (g : orthogonalRelatedTripleGroup K V Q t) :
    orthogonalTupleRelabel K V Q σ g ∈
      orthogonalRelatedTripleGroup K V Q t := by
  intro x
  let z : TrialityLabel → V := fun l => (g.1 (σ⁻¹ l)).1 (x l)
  calc
    orthogonalTrialityTensorEval K V t
        (fun l => ((orthogonalTupleRelabel K V Q σ g.1) l).1 (x l)) =
      orthogonalTrialityTensorEval K V t z := rfl
    _ = orthogonalTrialityTensorEval K V t (fun l => z (σ l)) := (ht σ z).symm
    _ = orthogonalTrialityTensorEval K V t
        (fun l => (g.1 l).1 (x (σ l))) := by
      congr 1
      funext l
      simp [z]
    _ = orthogonalTrialityTensorEval K V t (fun l => x (σ l)) := g.2 _
    _ = orthogonalTrialityTensorEval K V t x := ht σ x

/-- Relabeling restricted to the related-triples group. -/
def orthogonalRelatedTripleRelabel
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V)
    (σ : DiagramSymmetry) :
    MulAut (orthogonalRelatedTripleGroup K V Q t) where
  toFun g :=
    ⟨orthogonalTupleRelabel K V Q σ g.1,
      orthogonalTupleRelabel_mem_related K V Q t ht σ g⟩
  invFun g :=
    ⟨orthogonalTupleRelabel K V Q σ⁻¹ g.1,
      orthogonalTupleRelabel_mem_related K V Q t ht σ⁻¹ g⟩
  left_inv g := by
    apply Subtype.ext
    funext l
    simp [orthogonalTupleRelabel]
  right_inv g := by
    apply Subtype.ext
    funext l
    simp [orthogonalTupleRelabel]
  map_mul' g h := by
    apply Subtype.ext
    funext l
    rfl

/-- The constructed `S3` action by component relabeling. -/
def orthogonalRelatedTripleRelabelAction
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V) :
    DiagramSymmetry →* MulAut (orthogonalRelatedTripleGroup K V Q t) where
  toFun := orthogonalRelatedTripleRelabel K V Q t ht
  map_one' := by
    ext g l x
    rfl
  map_mul' σ τ := by
    ext g l x
    rfl

@[simp]
theorem orthogonalRelatedTripleRelabelAction_component
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V)
    (σ : DiagramSymmetry)
    (g : orthogonalRelatedTripleGroup K V Q t)
    (l : TrialityLabel) :
    (orthogonalRelatedTripleRelabelAction K V Q t ht σ g).1 l =
      g.1 (σ⁻¹ l) :=
  rfl

theorem orthogonalRelatedTriple_trialityCycle_cubed
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V) :
    (orthogonalRelatedTripleRelabelAction K V Q t ht trialityCycle) ^ 3 =
      1 := by
  rw [← map_pow, trialityCycle_cubed, map_one]

theorem orthogonalRelatedTriple_halfSpinSwap_squared
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V) :
    (orthogonalRelatedTripleRelabelAction K V Q t ht halfSpinSwap) ^ 2 =
      1 := by
  rw [← map_pow, halfSpinSwap_squared, map_one]

theorem orthogonalRelatedTriple_halfSpinSwap_conj_trialityCycle
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V) :
    orthogonalRelatedTripleRelabelAction K V Q t ht halfSpinSwap *
        orthogonalRelatedTripleRelabelAction K V Q t ht trialityCycle *
        orthogonalRelatedTripleRelabelAction K V Q t ht halfSpinSwap =
      (orthogonalRelatedTripleRelabelAction K V Q t ht trialityCycle)⁻¹ := by
  rw [← map_mul, ← map_mul, halfSpinSwap_conj_trialityCycle]
  exact map_inv _ _

/-- Negation as a quadratic isometry. -/
def negQuadraticIsometry : quadraticIsometryGroup K V Q :=
  ⟨LinearEquiv.neg K, by
    intro x
    simp⟩

/-- The central sign marker with `+1` in slot `i` and `-1` in the other two. -/
def centralSignMarker (t : OrthogonalTrialityTensor K V) (i : TrialityLabel) :
    orthogonalRelatedTripleGroup K V Q t :=
  ⟨fun l => if l = i then 1 else negQuadraticIsometry K V Q, by
    intro x
    cases i <;> simp [orthogonalTrialityTensorEval, negQuadraticIsometry]⟩

@[simp]
theorem centralSignMarker_component_self
    (t : OrthogonalTrialityTensor K V) (i : TrialityLabel) :
    (centralSignMarker K V Q t i).1 i = 1 := by
  simp [centralSignMarker]

theorem centralSignMarker_component_of_ne
    (t : OrthogonalTrialityTensor K V) {i l : TrialityLabel} (h : l ≠ i) :
    (centralSignMarker K V Q t i).1 l = negQuadraticIsometry K V Q := by
  simp [centralSignMarker, h]

theorem centralSignMarker_mem_center
    (t : OrthogonalTrialityTensor K V) (i : TrialityLabel) :
    centralSignMarker K V Q t i ∈
      Subgroup.center (orthogonalRelatedTripleGroup K V Q t) := by
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

theorem orthogonalRelatedTripleRelabel_centralSignMarker
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V)
    (σ : DiagramSymmetry) (i : TrialityLabel) :
    orthogonalRelatedTripleRelabelAction K V Q t ht σ
        (centralSignMarker K V Q t i) =
      centralSignMarker K V Q t (σ i) := by
  apply Subtype.ext
  funext l
  simp only [orthogonalRelatedTripleRelabelAction_component]
  by_cases h : σ⁻¹ l = i
  · have hl : l = σ i := by
      simpa using congrArg σ h
    rw [h, hl]
    simp
  · have hl : l ≠ σ i := by
      intro hl
      apply h
      simpa [hl]
    rw [centralSignMarker_component_of_ne K V Q t h,
      centralSignMarker_component_of_ne K V Q t hl]

theorem centralSignMarker_injective
    (t : OrthogonalTrialityTensor K V) (v : V) (hv : -v ≠ v) :
    Function.Injective (centralSignMarker K V Q t) := by
  intro i j hij
  by_contra hne
  have hc := congrArg
    (fun g : orthogonalRelatedTripleGroup K V Q t => ((g.1 i).1 v)) hij
  simp [centralSignMarker, hne, negQuadraticIsometry] at hc
  exact hv hc.symm

/-- Every nonidentity relabeling is outer when the sign markers are distinct. -/
theorem orthogonalRelatedTripleRelabel_not_inner_of_ne_one
    (t : OrthogonalTrialityTensor K V) (ht : t.IsSymmetric K V)
    (v : V) (hv : -v ≠ v)
    (σ : DiagramSymmetry) (hσ : σ ≠ 1) :
    ¬ IsInnerAutomorphism
      (orthogonalRelatedTripleRelabelAction K V Q t ht σ) := by
  intro hinner
  have hex : ∃ i : TrialityLabel, σ i ≠ i := by
    by_contra h
    push Not at h
    apply hσ
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hex
  have hfix := hinner.fix_of_mem_center
    (centralSignMarker_mem_center K V Q t i)
  rw [orthogonalRelatedTripleRelabel_centralSignMarker
    K V Q t ht σ i] at hfix
  exact hi (centralSignMarker_injective K V Q t v hv hfix)

end RelatedTriples

section Transport

universe uG uH uS

/-- Transport a group automorphism through a group equivalence. -/
def transportMulAut {G : Type uG} {H : Type uH} [Group G] [Group H]
    (e : G ≃* H) (a : MulAut H) : MulAut G where
  toFun x := e.symm (a (e x))
  invFun x := e.symm (a⁻¹ (e x))
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp

/-- Transport a whole automorphism action through a group equivalence. -/
def transportMulAutAction
    {G : Type uG} {H : Type uH} {S : Type uS}
    [Group G] [Group H] [Group S]
    (e : G ≃* H) (A : S →* MulAut H) : S →* MulAut G where
  toFun s := transportMulAut e (A s)
  map_one' := by
    ext x
    simp [transportMulAut]
  map_mul' s t := by
    ext x
    simp [transportMulAut]

theorem isInner_transportMulAut_iff
    {G : Type uG} {H : Type uH} [Group G] [Group H]
    (e : G ≃* H) (a : MulAut H) :
    IsInnerAutomorphism (transportMulAut e a) ↔
      IsInnerAutomorphism a := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨e g, ?_⟩
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    apply e.symm.injective
    have hx := DFunLike.congr_fun hg x
    simpa [transportMulAut, MulAut.conj_apply] using hx
  · rintro ⟨h, hh⟩
    refine ⟨e.symm h, ?_⟩
    ext x
    have hx := DFunLike.congr_fun hh (e x)
    simpa [transportMulAut, MulAut.conj_apply] using congrArg e.symm hx

theorem action_injective_of_nontrivial_not_inner
    {G : Type uG} {S : Type uS} [Group G] [Group S]
    (A : S →* MulAut G)
    (houter : ∀ s : S, s ≠ 1 → ¬ IsInnerAutomorphism (A s)) :
    Function.Injective A := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro s hs
    rw [Subgroup.mem_bot]
    by_contra hs1
    apply houter s hs1
    refine ⟨1, ?_⟩
    change A s = 1 at hs
    rw [hs]
    ext x
    simp
  · exact bot_le

end Transport

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
