/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.RootSystem.D4ZornFockPreservation

/-!
# Extensionality and the half-spin lifting boundary for Zorn related triples

The Zorn triality tensor is nondegenerate in its vector argument. Consequently,
a related triple is determined by its two half-spin components. This gives an
exact reformulation of surjectivity of the representation-defined
Spin-to-related-triples map: it is enough, and necessary, to lift the two
half-spin components simultaneously.

For the explicit Fock/Zorn chart, the reconstructed even-Clifford unit is
proved unitary. Its membership in Mathlib's generated-by-vectors `spinGroup`
is then proved equivalent to membership of the associated Clifford unit in
`lipschitzGroup`. Thus the exact remaining pointwise assertion is the latter
subgroup-closure membership for every related triple; evenness and unitarity
are no longer open.

This isolates the remaining pointwise content of the classical
Spin-related-triples comparison. The group-scheme version and its constructive
proof via the two even-Clifford blocks are Theorem 3.12 of Alsaody--Gille,
*Isotopes of Octonion Algebras, G2-Torsors and Triality*:
<https://arxiv.org/abs/1704.05229>. The reference supports the target
comparison and proof strategy; the coordinate nondegeneracy lemma below is
proved directly for this project's Zorn convention.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality
namespace Zorn

universe u

noncomputable section

variable {K : Type u} [CommRing K]

/-- The concrete Zorn triality tensor is nondegenerate in its first argument.

The eight pairs of standard-basis probes used below read off, in order, the
eight coordinates of the first argument. -/
theorem trialityTensor_left_injective
    {w w' : Octonion K}
    (h : ∀ x y, trialityTensor K w x y =
      trialityTensor K w' x y) :
    w = w' := by
  let e : Fin 8 → Octonion K := fun i j => if i = j then 1 else 0
  have h0 := h (e 0) (e 0)
  have h1 := h (e 0) (e 4)
  have h2 := h (e 0) (e 5)
  have h3 := h (e 0) (e 6)
  have h4 := h (e 1) (e 0)
  have h5 := h (e 2) (e 0)
  have h6 := h (e 3) (e 0)
  have h7 := h (e 1) (e 4)
  simp [trialityTensor, normPolar, paraMul, norm, mul, conjugate, e] at h0 h1 h2 h3 h4 h5 h6 h7
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

/-- Two Zorn related triples with the same two half-spin components are equal.

The tensor invariance laws first identify the vector components after probing
against arbitrary values in the two half-spin slots; tensor nondegeneracy then
finishes the vector component. -/
theorem relatedTriple_ext_halfSpin
    {g h : relatedTripleGroup K}
    (hplus : g.1 .halfSpinPlus = h.1 .halfSpinPlus)
    (hminus : g.1 .halfSpinMinus = h.1 .halfSpinMinus) :
    g = h := by
  apply Subtype.ext
  funext l
  cases l with
  | halfSpinPlus => exact hplus
  | halfSpinMinus => exact hminus
  | vector =>
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      apply trialityTensor_left_injective
      intro x y
      let input : TrialityLabel → Octonion K
        | .vector => w
        | .halfSpinPlus => (g.1 .halfSpinPlus).1.symm x
        | .halfSpinMinus => (g.1 .halfSpinMinus).1.symm y
      have hg := g.2 input
      have hh := h.2 input
      change
        trialityTensor K ((g.1 .vector).1 w)
            ((g.1 .halfSpinPlus).1
              ((g.1 .halfSpinPlus).1.symm x))
            ((g.1 .halfSpinMinus).1
              ((g.1 .halfSpinMinus).1.symm y)) =
          trialityTensor K w
            ((g.1 .halfSpinPlus).1.symm x)
            ((g.1 .halfSpinMinus).1.symm y) at hg
      change
        trialityTensor K ((h.1 .vector).1 w)
            ((h.1 .halfSpinPlus).1
              ((g.1 .halfSpinPlus).1.symm x))
            ((h.1 .halfSpinMinus).1
              ((g.1 .halfSpinMinus).1.symm y)) =
          trialityTensor K w
            ((g.1 .halfSpinPlus).1.symm x)
            ((g.1 .halfSpinMinus).1.symm y) at hh
      rw [LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply] at hg
      rw [← hplus, ← hminus, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply] at hh
      exact hg.trans hh.symm

end
end Zorn

universe u

noncomputable section

variable (K : Type u) [Field K] [Invertible (2 : K)]

/-- The exact simultaneous half-spin lifting obligation for the concrete
Spin-to-Zorn comparison. -/
def SplitZornHalfSpinPairLifting
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart) : Prop :=
  ∀ t : Zorn.relatedTripleGroup K,
    ∃ g : CliffordEven.SpinPoint (splitD4Form K),
      ((splitSpinToZornRelatedTriples K chart hQ ht g).1
          .halfSpinPlus) =
        t.1 .halfSpinPlus ∧
      ((splitSpinToZornRelatedTriples K chart hQ ht g).1
          .halfSpinMinus) =
        t.1 .halfSpinMinus

/-- Surjectivity of the concrete comparison is equivalent to simultaneous
lifting of the two half-spin components. -/
theorem splitSpinToZornRelatedTriples_surjective_iff_halfSpinPairLifting
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart) :
    Function.Surjective
        (splitSpinToZornRelatedTriples K chart hQ ht) ↔
      SplitZornHalfSpinPairLifting K chart hQ ht := by
  constructor
  · intro hsurj t
    rcases hsurj t with ⟨g, rfl⟩
    exact ⟨g, rfl, rfl⟩
  · intro hlift t
    rcases hlift t with ⟨g, hplus, hminus⟩
    exact ⟨g, Zorn.relatedTriple_ext_halfSpin hplus hminus⟩

variable {K}

/-- Regard a linear automorphism as a unit of its endomorphism ring. -/
def linearEquivEndUnit {M : Type*}
    [AddCommGroup M] [Module K M]
    (e : M ≃ₗ[K] M) : (Module.End K M)ˣ where
  val := e.toLinearMap
  inv := e.symm.toLinearMap
  val_inv := by
    ext x
    exact e.apply_symm_apply x
  inv_val := by
    ext x
    exact e.symm_apply_apply x

/-- Pull the positive half-spin component of a Zorn related triple back through
the chosen Fock--Zorn chart. -/
def zornHalfSpinPlusPullback
    (chart : SplitZornChart K)
    (t : Zorn.relatedTripleGroup K) :
    SplitHalfSpinPlus K ≃ₗ[K] SplitHalfSpinPlus K :=
  (chart .halfSpinPlus).trans
    ((t.1 .halfSpinPlus).1.trans (chart .halfSpinPlus).symm)

/-- Pull the negative half-spin component of a Zorn related triple back through
the chosen Fock--Zorn chart. -/
def zornHalfSpinMinusPullback
    (chart : SplitZornChart K)
    (t : Zorn.relatedTripleGroup K) :
    SplitHalfSpinMinus K ≃ₗ[K] SplitHalfSpinMinus K :=
  (chart .halfSpinMinus).trans
    ((t.1 .halfSpinMinus).1.trans (chart .halfSpinMinus).symm)

/-- The pair of invertible half-spin blocks attached to a Zorn related triple. -/
def zornHalfSpinPairUnit
    (chart : SplitZornChart K)
    (t : Zorn.relatedTripleGroup K) :
    (Module.End K (SplitHalfSpinPlus K) ×
      Module.End K (SplitHalfSpinMinus K))ˣ where
  val := (linearEquivEndUnit (zornHalfSpinPlusPullback chart t),
    linearEquivEndUnit (zornHalfSpinMinusPullback chart t))
  inv := (↑((linearEquivEndUnit (zornHalfSpinPlusPullback chart t))⁻¹),
    ↑((linearEquivEndUnit (zornHalfSpinMinusPullback chart t))⁻¹))
  val_inv := by
    ext <;> simp
  inv_val := by
    ext <;> simp

/-- Reconstruct an even-Clifford unit from the two half-spin blocks of a Zorn
related triple.

This is the literal inverse-block construction used in the surjectivity part of
Alsaody--Gille, Theorem 3.12. Membership of this unit in Mathlib's
generated-by-vectors `spinGroup` is isolated below rather than assumed. -/
def zornRelatedTripleEvenUnit
    (chart : SplitZornChart K)
    (t : Zorn.relatedTripleGroup K) :
    (CliffordAlgebra.even (splitD4Form K))ˣ :=
  Units.map
    ((splitHalfSpinBlockEquiv (K := K)).symm.toRingEquiv.toMonoidHom)
    (zornHalfSpinPairUnit chart t)

/-- Applying the even-Clifford block equivalence to the reconstructed unit
recovers the two chart-pulled related-triple components. -/
theorem splitHalfSpinBlockEquiv_zornRelatedTripleEvenUnit
    (chart : SplitZornChart K)
    (t : Zorn.relatedTripleGroup K) :
    splitHalfSpinBlockEquiv (K := K)
        (((zornRelatedTripleEvenUnit chart t :
          (CliffordAlgebra.even (splitD4Form K))ˣ) :
            CliffordAlgebra.even (splitD4Form K))) =
      ((zornHalfSpinPlusPullback chart t).toLinearMap,
        (zornHalfSpinMinusPullback chart t).toLinearMap) := by
  change splitHalfSpinBlockEquiv (K := K)
      ((splitHalfSpinBlockEquiv (K := K)).symm
        ((zornHalfSpinPairUnit chart t : _) : _)) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem splitFockEvenAction_zornRelatedTripleEvenUnit
    (chart : SplitZornChart K)
    (t : Zorn.relatedTripleGroup K) :
    splitFockEvenAction K
        (((zornRelatedTripleEvenUnit chart t :
          (CliffordAlgebra.even (splitD4Form K))ˣ) :
            CliffordAlgebra.even (splitD4Form K))) =
      (zornHalfSpinPlusPullback chart t).toLinearMap :=
  congrArg Prod.fst
    (splitHalfSpinBlockEquiv_zornRelatedTripleEvenUnit chart t)

theorem splitFockOddAction_zornRelatedTripleEvenUnit
    (chart : SplitZornChart K)
    (t : Zorn.relatedTripleGroup K) :
    splitFockOddAction K
        (((zornRelatedTripleEvenUnit chart t :
          (CliffordAlgebra.even (splitD4Form K))ˣ) :
            CliffordAlgebra.even (splitD4Form K))) =
      (zornHalfSpinMinusPullback chart t).toLinearMap :=
  congrArg Prod.snd
    (splitHalfSpinBlockEquiv_zornRelatedTripleEvenUnit chart t)

namespace Zorn

omit [Invertible (2 : K)] in
/-- The Zorn norm polar form is nondegenerate in its right argument over a
field.

The eight standard-basis probes read off the eight coordinates in the order
dictated by the concrete Zorn norm convention. -/
theorem normPolar_right_injective
    {y z : Octonion K}
    (h : ∀ x, normPolar K x y = normPolar K x z) :
    y = z := by
  let e : Fin 8 → Octonion K := fun i j => if i = j then 1 else 0
  have h0 := h (e 0)
  have h1 := h (e 1)
  have h2 := h (e 2)
  have h3 := h (e 3)
  have h4 := h (e 4)
  have h5 := h (e 5)
  have h6 := h (e 6)
  have h7 := h (e 7)
  simp [normPolar, norm, e] at h0 h1 h2 h3 h4 h5 h6 h7
  ring_nf at h0 h1 h2 h3 h4 h5 h6 h7
  funext i
  fin_cases i
  · exact h7
  · exact neg_inj.mp h4
  · exact neg_inj.mp h5
  · exact neg_inj.mp h6
  · exact neg_inj.mp h1
  · exact neg_inj.mp h2
  · exact neg_inj.mp h3
  · exact h0

end Zorn

omit [Invertible (2 : K)] in
/-- The transported positive-parity Zorn polar form is nondegenerate in its
right argument. -/
theorem splitFockEvenNormPolar_right_injective
    {y z : SplitFockEven K}
    (h : ∀ x, splitFockEvenNormPolar K x y =
      splitFockEvenNormPolar K x z) :
    y = z := by
  apply (splitFockEvenZornEquiv K).injective
  apply Zorn.normPolar_right_injective
  intro x
  have hx := h ((splitFockEvenZornEquiv K).symm x)
  change Zorn.normPolar K
      (splitFockEvenZornEquiv K
        ((splitFockEvenZornEquiv K).symm x))
      (splitFockEvenZornEquiv K y) =
    Zorn.normPolar K
      (splitFockEvenZornEquiv K
        ((splitFockEvenZornEquiv K).symm x))
      (splitFockEvenZornEquiv K z) at hx
  rw [LinearEquiv.apply_symm_apply] at hx
  exact hx

omit [Invertible (2 : K)] in
/-- The transported negative-parity Zorn polar form is nondegenerate in its
right argument. -/
theorem splitFockOddNormPolar_right_injective
    {y z : SplitFockOdd K}
    (h : ∀ x, splitFockOddNormPolar K x y =
      splitFockOddNormPolar K x z) :
    y = z := by
  apply (splitFockOddZornEquiv K).injective
  apply Zorn.normPolar_right_injective
  intro x
  have hx := h ((splitFockOddZornEquiv K).symm x)
  change Zorn.normPolar K
      (splitFockOddZornEquiv K
        ((splitFockOddZornEquiv K).symm x))
      (splitFockOddZornEquiv K y) =
    Zorn.normPolar K
      (splitFockOddZornEquiv K
        ((splitFockOddZornEquiv K).symm x))
      (splitFockOddZornEquiv K z) at hx
  rw [LinearEquiv.apply_symm_apply] at hx
  exact hx

omit [Invertible (2 : K)] in
/-- The positive half-spin block of a Zorn related triple preserves the
transported polar form. -/
theorem zornHalfSpinPlusPullback_preserves_normPolar
    (t : Zorn.relatedTripleGroup K)
    (p q : SplitFockEven K) :
    splitFockEvenNormPolar K
      (zornHalfSpinPlusPullback (splitZornFockChart K) t p)
      (zornHalfSpinPlusPullback (splitZornFockChart K) t q) =
    splitFockEvenNormPolar K p q := by
  have hp :
      splitFockEvenZornEquiv K
          (zornHalfSpinPlusPullback (splitZornFockChart K) t p) =
        (t.1 .halfSpinPlus).1 (splitFockEvenZornEquiv K p) := by
    change splitFockEvenZornEquiv K
        ((splitFockEvenZornEquiv K).symm
          ((t.1 .halfSpinPlus).1 (splitFockEvenZornEquiv K p))) = _
    rw [LinearEquiv.apply_symm_apply]
  have hq :
      splitFockEvenZornEquiv K
          (zornHalfSpinPlusPullback (splitZornFockChart K) t q) =
        (t.1 .halfSpinPlus).1 (splitFockEvenZornEquiv K q) := by
    change splitFockEvenZornEquiv K
        ((splitFockEvenZornEquiv K).symm
          ((t.1 .halfSpinPlus).1 (splitFockEvenZornEquiv K q))) = _
    rw [LinearEquiv.apply_symm_apply]
  have hsum := (t.1 .halfSpinPlus).2
    (splitFockEvenZornEquiv K p + splitFockEvenZornEquiv K q)
  have hpN := (t.1 .halfSpinPlus).2 (splitFockEvenZornEquiv K p)
  have hqN := (t.1 .halfSpinPlus).2 (splitFockEvenZornEquiv K q)
  change Zorn.norm K
      ((t.1 .halfSpinPlus).1
        (splitFockEvenZornEquiv K p + splitFockEvenZornEquiv K q)) =
    Zorn.norm K
      (splitFockEvenZornEquiv K p + splitFockEvenZornEquiv K q) at hsum
  change Zorn.norm K
      ((t.1 .halfSpinPlus).1 (splitFockEvenZornEquiv K p)) =
    Zorn.norm K (splitFockEvenZornEquiv K p) at hpN
  change Zorn.norm K
      ((t.1 .halfSpinPlus).1 (splitFockEvenZornEquiv K q)) =
    Zorn.norm K (splitFockEvenZornEquiv K q) at hqN
  simp only [splitFockEvenNormPolar, LinearMap.BilinForm.comp_apply,
    Zorn.normPolarBilinear_apply]
  change Zorn.normPolar K
      (splitFockEvenZornEquiv K
        (zornHalfSpinPlusPullback (splitZornFockChart K) t p))
      (splitFockEvenZornEquiv K
        (zornHalfSpinPlusPullback (splitZornFockChart K) t q)) =
    Zorn.normPolar K
      (splitFockEvenZornEquiv K p)
      (splitFockEvenZornEquiv K q)
  rw [hp, hq]
  simp only [Zorn.normPolar]
  rw [← map_add, hsum, hpN, hqN]

omit [Invertible (2 : K)] in
/-- The negative half-spin block of a Zorn related triple preserves the
transported polar form. -/
theorem zornHalfSpinMinusPullback_preserves_normPolar
    (t : Zorn.relatedTripleGroup K)
    (p q : SplitFockOdd K) :
    splitFockOddNormPolar K
      (zornHalfSpinMinusPullback (splitZornFockChart K) t p)
      (zornHalfSpinMinusPullback (splitZornFockChart K) t q) =
    splitFockOddNormPolar K p q := by
  have hp :
      splitFockOddZornEquiv K
          (zornHalfSpinMinusPullback (splitZornFockChart K) t p) =
        (t.1 .halfSpinMinus).1 (splitFockOddZornEquiv K p) := by
    change splitFockOddZornEquiv K
        ((splitFockOddZornEquiv K).symm
          ((t.1 .halfSpinMinus).1 (splitFockOddZornEquiv K p))) = _
    rw [LinearEquiv.apply_symm_apply]
  have hq :
      splitFockOddZornEquiv K
          (zornHalfSpinMinusPullback (splitZornFockChart K) t q) =
        (t.1 .halfSpinMinus).1 (splitFockOddZornEquiv K q) := by
    change splitFockOddZornEquiv K
        ((splitFockOddZornEquiv K).symm
          ((t.1 .halfSpinMinus).1 (splitFockOddZornEquiv K q))) = _
    rw [LinearEquiv.apply_symm_apply]
  have hsum := (t.1 .halfSpinMinus).2
    (splitFockOddZornEquiv K p + splitFockOddZornEquiv K q)
  have hpN := (t.1 .halfSpinMinus).2 (splitFockOddZornEquiv K p)
  have hqN := (t.1 .halfSpinMinus).2 (splitFockOddZornEquiv K q)
  change Zorn.norm K
      ((t.1 .halfSpinMinus).1
        (splitFockOddZornEquiv K p + splitFockOddZornEquiv K q)) =
    Zorn.norm K
      (splitFockOddZornEquiv K p + splitFockOddZornEquiv K q) at hsum
  change Zorn.norm K
      ((t.1 .halfSpinMinus).1 (splitFockOddZornEquiv K p)) =
    Zorn.norm K (splitFockOddZornEquiv K p) at hpN
  change Zorn.norm K
      ((t.1 .halfSpinMinus).1 (splitFockOddZornEquiv K q)) =
    Zorn.norm K (splitFockOddZornEquiv K q) at hqN
  simp only [splitFockOddNormPolar, LinearMap.BilinForm.comp_apply,
    Zorn.normPolarBilinear_apply]
  change Zorn.normPolar K
      (splitFockOddZornEquiv K
        (zornHalfSpinMinusPullback (splitZornFockChart K) t p))
      (splitFockOddZornEquiv K
        (zornHalfSpinMinusPullback (splitZornFockChart K) t q)) =
    Zorn.normPolar K
      (splitFockOddZornEquiv K p)
      (splitFockOddZornEquiv K q)
  rw [hp, hq]
  simp only [Zorn.normPolar]
  rw [← map_add, hsum, hpN, hqN]

/-- The even-Clifford unit reconstructed from a Fock/Zorn related triple is
unitary.

On each faithful half-spin block, adjointness of reversion and preservation of
the Zorn polar form identify reversion with the inverse block. The block
equivalence then gives both Clifford norm-one equations. -/
theorem splitFockZornRelatedTripleEvenUnit_mem_unitary
    (t : Zorn.relatedTripleGroup K) :
    ((((zornRelatedTripleEvenUnit (splitZornFockChart K) t :
      (CliffordAlgebra.even (splitD4Form K))ˣ) :
        CliffordAlgebra.even (splitD4Form K)) :
          CliffordAlgebra (splitD4Form K))) ∈
      unitary (CliffordAlgebra (splitD4Form K)) := by
  let u0 := zornRelatedTripleEvenUnit (splitZornFockChart K) t
  let a : CliffordAlgebra.even (splitD4Form K) :=
    (u0 : CliffordAlgebra.even (splitD4Form K))
  have haeven :
      (a : CliffordAlgebra (splitD4Form K)) ∈
        CliffordAlgebra.evenOdd (splitD4Form K) 0 := by
    rw [← CliffordAlgebra.even_toSubmodule]
    exact a.property
  let ar : CliffordAlgebra.even (splitD4Form K) :=
    ⟨CliffordAlgebra.reverse
        (a : CliffordAlgebra (splitD4Form K)), by
      change CliffordAlgebra.reverse
          (a : CliffordAlgebra (splitD4Form K)) ∈
        (CliffordAlgebra.even (splitD4Form K)).toSubmodule
      rw [CliffordAlgebra.even_toSubmodule]
      exact (CliffordAlgebra.reverse_mem_evenOdd_iff
        (splitD4Form K)).2 haeven⟩
  let fplus :=
    zornHalfSpinPlusPullback (splitZornFockChart K) t
  let fminus :=
    zornHalfSpinMinusPullback (splitZornFockChart K) t
  have hadjPlus0 :=
    splitFockEvenAction_reverse_isAdjointPair K
      (a : CliffordAlgebra (splitD4Form K)) haeven
  have hadjPlus :
      (splitFockEvenNormPolar K).IsAdjointPair
        (splitFockEvenNormPolar K)
        (splitFockEvenAction K a)
        (splitFockEvenAction K ar) := by
    intro p q
    exact hadjPlus0 p q
  have haPlus :
      splitFockEvenAction K a = fplus.toLinearMap :=
    splitFockEvenAction_zornRelatedTripleEvenUnit
      (splitZornFockChart K) t
  have harPlus :
      splitFockEvenAction K ar = fplus.symm.toLinearMap := by
    apply LinearMap.ext
    intro q
    apply splitFockEvenNormPolar_right_injective
    intro p
    calc
      splitFockEvenNormPolar K p (splitFockEvenAction K ar q) =
          splitFockEvenNormPolar K
            (splitFockEvenAction K a p) q :=
        (hadjPlus p q).symm
      _ = splitFockEvenNormPolar K
          (fplus p) (fplus (fplus.symm q)) := by
        rw [haPlus]
        change splitFockEvenNormPolar K (fplus p) q =
          splitFockEvenNormPolar K
            (fplus p) (fplus (fplus.symm q))
        rw [LinearEquiv.apply_symm_apply]
      _ = splitFockEvenNormPolar K p (fplus.symm q) :=
        zornHalfSpinPlusPullback_preserves_normPolar
          t p (fplus.symm q)
  have hadjMinus0 :=
    splitFockOddAction_reverse_isAdjointPair K
      (a : CliffordAlgebra (splitD4Form K)) haeven
  have hadjMinus :
      (splitFockOddNormPolar K).IsAdjointPair
        (splitFockOddNormPolar K)
        (splitFockOddAction K a)
        (splitFockOddAction K ar) := by
    intro p q
    exact hadjMinus0 p q
  have haMinus :
      splitFockOddAction K a = fminus.toLinearMap :=
    splitFockOddAction_zornRelatedTripleEvenUnit
      (splitZornFockChart K) t
  have harMinus :
      splitFockOddAction K ar = fminus.symm.toLinearMap := by
    apply LinearMap.ext
    intro q
    apply splitFockOddNormPolar_right_injective
    intro p
    calc
      splitFockOddNormPolar K p (splitFockOddAction K ar q) =
          splitFockOddNormPolar K
            (splitFockOddAction K a p) q :=
        (hadjMinus p q).symm
      _ = splitFockOddNormPolar K
          (fminus p) (fminus (fminus.symm q)) := by
        rw [haMinus]
        change splitFockOddNormPolar K (fminus p) q =
          splitFockOddNormPolar K
            (fminus p) (fminus (fminus.symm q))
        rw [LinearEquiv.apply_symm_apply]
      _ = splitFockOddNormPolar K p (fminus.symm q) :=
        zornHalfSpinMinusPullback_preserves_normPolar
          t p (fminus.symm q)
  have hrev_mul : ar * a = 1 := by
    apply (splitHalfSpinBlockEquiv (K := K)).injective
    rw [map_mul, map_one,
      splitHalfSpinBlockEquiv_zornRelatedTripleEvenUnit
        (splitZornFockChart K) t]
    change
      (splitFockEvenAction K ar * fplus.toLinearMap,
        splitFockOddAction K ar * fminus.toLinearMap) = (1, 1)
    rw [harPlus, harMinus]
    apply Prod.ext
    · apply LinearMap.ext
      intro x
      simp [Module.End.mul_apply]
    · apply LinearMap.ext
      intro x
      simp [Module.End.mul_apply]
  have hu_inv_right :
      a * ((u0⁻¹ : (CliffordAlgebra.even (splitD4Form K))ˣ) :
        CliffordAlgebra.even (splitD4Form K)) = 1 := by
    change ((u0 : CliffordAlgebra.even (splitD4Form K)) *
      ((u0⁻¹ : (CliffordAlgebra.even (splitD4Form K))ˣ) :
        CliffordAlgebra.even (splitD4Form K))) = 1
    exact Units.val_inv u0
  have har_inv :
      ar = ((u0⁻¹ : (CliffordAlgebra.even (splitD4Form K))ˣ) :
        CliffordAlgebra.even (splitD4Form K)) := by
    calc
      ar = ar * 1 := (mul_one ar).symm
      _ = ar * (a * ((u0⁻¹ :
          (CliffordAlgebra.even (splitD4Form K))ˣ) :
            CliffordAlgebra.even (splitD4Form K))) := by
        rw [hu_inv_right]
      _ = (ar * a) * ((u0⁻¹ :
          (CliffordAlgebra.even (splitD4Form K))ˣ) :
            CliffordAlgebra.even (splitD4Form K)) := by
        rw [mul_assoc]
      _ = ((u0⁻¹ : (CliffordAlgebra.even (splitD4Form K))ˣ) :
          CliffordAlgebra.even (splitD4Form K)) := by
        rw [hrev_mul, one_mul]
  have hmul_rev : a * ar = 1 := by
    rw [har_inv]
    exact hu_inv_right
  have hrev_mulC := congrArg
    (fun x : CliffordAlgebra.even (splitD4Form K) =>
      ((x : CliffordAlgebra.even (splitD4Form K)) :
        CliffordAlgebra (splitD4Form K))) hrev_mul
  change CliffordAlgebra.reverse
      (a : CliffordAlgebra (splitD4Form K)) *
      (a : CliffordAlgebra (splitD4Form K)) = 1 at hrev_mulC
  have hmul_revC := congrArg
    (fun x : CliffordAlgebra.even (splitD4Form K) =>
      ((x : CliffordAlgebra.even (splitD4Form K)) :
        CliffordAlgebra (splitD4Form K))) hmul_rev
  change (a : CliffordAlgebra (splitD4Form K)) *
      CliffordAlgebra.reverse
        (a : CliffordAlgebra (splitD4Form K)) = 1 at hmul_revC
  have hstar :
      star (a : CliffordAlgebra (splitD4Form K)) =
        CliffordAlgebra.reverse
          (a : CliffordAlgebra (splitD4Form K)) := by
    rw [CliffordAlgebra.star_def,
      CliffordAlgebra.involute_eq_of_mem_even haeven]
  change star (a : CliffordAlgebra (splitD4Form K)) *
      (a : CliffordAlgebra (splitD4Form K)) = 1 ∧
    (a : CliffordAlgebra (splitD4Form K)) *
      star (a : CliffordAlgebra (splitD4Form K)) = 1
  rw [hstar]
  exact ⟨hrev_mulC, hmul_revC⟩

/-- The exact remaining membership bridge after inverse-block reconstruction:
every reconstructed even-Clifford unit is in the image of Mathlib's spin
points. -/
def SplitZornRelatedTripleEvenUnitLifting
    (chart : SplitZornChart K) : Prop :=
  ∀ t : Zorn.relatedTripleGroup K,
    ∃ g : CliffordEven.SpinPoint (splitD4Form K),
      CliffordEven.spinPointToEvenUnits (splitD4Form K) g =
        zornRelatedTripleEvenUnit chart t

theorem splitTrialityLinearTupleHom_halfSpinPlus_of_evenUnitLift
    (chart : SplitZornChart K)
    (t : Zorn.relatedTripleGroup K)
    (g : CliffordEven.SpinPoint (splitD4Form K))
    (hg : CliffordEven.spinPointToEvenUnits (splitD4Form K) g =
      zornRelatedTripleEvenUnit chart t) :
    splitTrialityLinearTupleHom K (Zorn.Octonion K) chart g
        .halfSpinPlus =
      (t.1 .halfSpinPlus).1 := by
  apply LinearEquiv.ext
  intro x
  change chart .halfSpinPlus
      (splitEvenFockSpinRepresentation K g
        ((chart .halfSpinPlus).symm x)) =
    (t.1 .halfSpinPlus).1 x
  rw [splitEvenFockSpinRepresentation_apply]
  have hval := congrArg
    (fun u : (CliffordAlgebra.even (splitD4Form K))ˣ =>
      (u : CliffordAlgebra.even (splitD4Form K))) hg
  rw [hval, splitFockEvenAction_zornRelatedTripleEvenUnit]
  change chart .halfSpinPlus
      ((chart .halfSpinPlus).symm
        ((t.1 .halfSpinPlus).1
          (chart .halfSpinPlus ((chart .halfSpinPlus).symm x)))) =
    (t.1 .halfSpinPlus).1 x
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem splitTrialityLinearTupleHom_halfSpinMinus_of_evenUnitLift
    (chart : SplitZornChart K)
    (t : Zorn.relatedTripleGroup K)
    (g : CliffordEven.SpinPoint (splitD4Form K))
    (hg : CliffordEven.spinPointToEvenUnits (splitD4Form K) g =
      zornRelatedTripleEvenUnit chart t) :
    splitTrialityLinearTupleHom K (Zorn.Octonion K) chart g
        .halfSpinMinus =
      (t.1 .halfSpinMinus).1 := by
  apply LinearEquiv.ext
  intro x
  change chart .halfSpinMinus
      (splitOddFockSpinRepresentation K g
        ((chart .halfSpinMinus).symm x)) =
    (t.1 .halfSpinMinus).1 x
  rw [splitOddFockSpinRepresentation_apply]
  have hval := congrArg
    (fun u : (CliffordAlgebra.even (splitD4Form K))ˣ =>
      (u : CliffordAlgebra.even (splitD4Form K))) hg
  rw [hval, splitFockOddAction_zornRelatedTripleEvenUnit]
  change chart .halfSpinMinus
      ((chart .halfSpinMinus).symm
        ((t.1 .halfSpinMinus).1
          (chart .halfSpinMinus ((chart .halfSpinMinus).symm x)))) =
    (t.1 .halfSpinMinus).1 x
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The inverse-block membership bridge implies the exact simultaneous
half-spin lifting obligation. -/
theorem splitZornHalfSpinPairLifting_of_evenUnitLifting
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart)
    (hlift :
      SplitZornRelatedTripleEvenUnitLifting (K := K) chart) :
    SplitZornHalfSpinPairLifting K chart hQ ht := by
  intro t
  rcases hlift t with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · apply Subtype.ext
    exact splitTrialityLinearTupleHom_halfSpinPlus_of_evenUnitLift
      chart t g hg
  · apply Subtype.ext
    exact splitTrialityLinearTupleHom_halfSpinMinus_of_evenUnitLift
      chart t g hg

/-- Once every inverse-block reconstruction lifts to a Mathlib spin point, the
concrete Spin-to-Zorn comparison is surjective. -/
theorem splitSpinToZornRelatedTriples_surjective_of_evenUnitLifting
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart)
    (hlift :
      SplitZornRelatedTripleEvenUnitLifting (K := K) chart) :
    Function.Surjective
      (splitSpinToZornRelatedTriples K chart hQ ht) :=
  (splitSpinToZornRelatedTriples_surjective_iff_halfSpinPairLifting
    K chart hQ ht).2
      (splitZornHalfSpinPairLifting_of_evenUnitLifting
        (K := K) chart hQ ht hlift)

/-- The sharp remaining pointwise comparison obligation: every even-Clifford
unit reconstructed from a Zorn related triple belongs to Mathlib's
generated-by-vectors spin group. -/
def SplitZornRelatedTripleEvenUnitSpinMembership
    (chart : SplitZornChart K) : Prop :=
  ∀ t : Zorn.relatedTripleGroup K,
    ((((zornRelatedTripleEvenUnit chart t :
      (CliffordAlgebra.even (splitD4Form K))ˣ) :
        CliffordAlgebra.even (splitD4Form K)) :
          CliffordAlgebra (splitD4Form K))) ∈
      spinGroup (splitD4Form K)

/-- Spin-group membership of every reconstructed unit supplies the exact
even-unit lifting interface. -/
theorem splitZornRelatedTripleEvenUnitLifting_of_spinMembership
    (chart : SplitZornChart K)
    (hmem :
      SplitZornRelatedTripleEvenUnitSpinMembership (K := K) chart) :
    SplitZornRelatedTripleEvenUnitLifting (K := K) chart := by
  intro t
  let g : CliffordEven.SpinPoint (splitD4Form K) :=
    ⟨(((zornRelatedTripleEvenUnit chart t :
      (CliffordAlgebra.even (splitD4Form K))ˣ) :
        CliffordAlgebra.even (splitD4Form K)) :
          CliffordAlgebra (splitD4Form K)), hmem t⟩
  refine ⟨g, ?_⟩
  apply Units.ext
  rfl

/-- The sharp spin-membership theorem immediately closes pointwise
surjectivity of the concrete comparison. -/
theorem splitSpinToZornRelatedTriples_surjective_of_spinMembership
    (chart : SplitZornChart K)
    (hQ : SplitZornTuplePreservesNorm K chart)
    (ht : SplitZornTuplePreservesTensor K chart)
    (hmem :
      SplitZornRelatedTripleEvenUnitSpinMembership (K := K) chart) :
    Function.Surjective
      (splitSpinToZornRelatedTriples K chart hQ ht) :=
  splitSpinToZornRelatedTriples_surjective_of_evenUnitLifting
    (K := K) chart hQ ht
      (splitZornRelatedTripleEvenUnitLifting_of_spinMembership
        (K := K) chart hmem)

/-- The single remaining membership statement for the explicit Fock/Zorn
chart. -/
abbrev SplitFockZornRelatedTripleEvenUnitSpinMembership
    (F : Type u) [Field F] [Invertible (2 : F)] : Prop :=
  SplitZornRelatedTripleEvenUnitSpinMembership
    (K := F) (splitZornFockChart F)

/-- For each reconstructed Fock/Zorn unit, spin-group membership is equivalent
to the one remaining condition: membership of its associated Clifford unit in
Mathlib's subgroup generated by invertible vectors.

Evenness is automatic from the construction, and unitarity is supplied by the
preceding unitary theorem. -/
theorem splitFockZornRelatedTripleEvenUnit_mem_spinGroup_iff_mem_lipschitzGroup
    (t : Zorn.relatedTripleGroup K) :
    ((((zornRelatedTripleEvenUnit (splitZornFockChart K) t :
      (CliffordAlgebra.even (splitD4Form K))ˣ) :
        CliffordAlgebra.even (splitD4Form K)) :
          CliffordAlgebra (splitD4Form K))) ∈
        spinGroup (splitD4Form K) ↔
      CliffordEven.evenUnitsInClifford (splitD4Form K)
          (zornRelatedTripleEvenUnit (splitZornFockChart K) t) ∈
        lipschitzGroup (splitD4Form K) := by
  let u0 := zornRelatedTripleEvenUnit (splitZornFockChart K) t
  let cu := CliffordEven.evenUnitsInClifford (splitD4Form K) u0
  change (↑cu : CliffordAlgebra (splitD4Form K)) ∈
      spinGroup (splitD4Form K) ↔
    cu ∈ lipschitzGroup (splitD4Form K)
  constructor
  · intro hspin
    have hpin : (↑cu : CliffordAlgebra (splitD4Form K)) ∈
        pinGroup (splitD4Form K) :=
      (spinGroup.mem_iff.mp hspin).1
    exact (pinGroup.units_mem_iff.mp hpin).1
  · intro hlip
    apply spinGroup.mem_iff.mpr
    refine ⟨pinGroup.units_mem_iff.mpr ⟨hlip, ?_⟩, ?_⟩
    · exact splitFockZornRelatedTripleEvenUnit_mem_unitary t
    · change ((u0 : CliffordAlgebra.even (splitD4Form K)) :
        CliffordAlgebra (splitD4Form K)) ∈
          CliffordAlgebra.even (splitD4Form K)
      exact (u0 : CliffordAlgebra.even (splitD4Form K)).property

/-- The advertised Fock/Zorn spin-membership predicate has exactly one
unresolved field: every associated Clifford unit must lie in Mathlib's
lipschitz group, the subgroup closure of invertible vectors. -/
theorem splitFockZornRelatedTripleEvenUnitSpinMembership_iff_lipschitzGroup :
    SplitFockZornRelatedTripleEvenUnitSpinMembership K ↔
      ∀ t : Zorn.relatedTripleGroup K,
        CliffordEven.evenUnitsInClifford (splitD4Form K)
            (zornRelatedTripleEvenUnit (splitZornFockChart K) t) ∈
          lipschitzGroup (splitD4Form K) := by
  constructor
  · intro h t
    exact
      (splitFockZornRelatedTripleEvenUnit_mem_spinGroup_iff_mem_lipschitzGroup
        t).mp (h t)
  · intro h t
    exact
      (splitFockZornRelatedTripleEvenUnit_mem_spinGroup_iff_mem_lipschitzGroup
        t).mpr (h t)

/-- Membership of every reconstructed Fock/Zorn even-Clifford unit in
Mathlib's generated-by-vectors spin group closes surjectivity of the explicit
comparison map. -/
theorem splitFockSpinToZornRelatedTriples_surjective_of_spinMembership
    (hmem : SplitFockZornRelatedTripleEvenUnitSpinMembership K) :
    Function.Surjective (splitFockSpinToZornRelatedTriples K) := by
  exact splitSpinToZornRelatedTriples_surjective_of_spinMembership
    (K := K) (splitZornFockChart K)
      (splitZornFockChart_preservesNorm K)
      (splitZornFockChart_preservesTensor K) hmem

end

end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
