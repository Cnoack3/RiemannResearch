import RiemannResearch.E7.E7IndexEightBoundary

/-!
# Excluding degree-four unitary quadratic extensions on the hard E7 boundary

This module isolates the numerical incompatibility behind a published-involution-theoretic
no-go result for the index-eight trialitarian packet.

The mathematical interpretation uses two external results, neither of which is formalized here.

* Bıngöl--Quéguiner-Mathieu, `Triality over fields with I_q^3 = 0`, Lemma 3.7:
  the Clifford invariant of a quadratic extension of an even-degree unitary involution is
  represented, modulo the underlying Brauer class, by the unitary discriminant algebra.
* Becher--Grenier-Boley--Tignol, `The discriminant Pfister form of an algebra with
  involution of capacity four`, Proposition 8.2: the discriminant algebra of a unitary
  involution of capacity four is Brauer-equivalent to a quaternion algebra, hence has
  Schur index at most two.

Thus a degree-eight quadratic pair obtained as a quadratic extension of a degree-four unitary
involution must have an index-at-most-two representative among its two labelled Clifford
classes.  The hard E7 packet has both labelled Clifford indices equal to four, so it cannot
arise by that construction.

The Lean theorem below proves exactly this last numerical implication.  It does not formalize
unitary involutions or quadratic extensions, and it does not prove effectivity of the E7 packet.
-/

namespace RiemannResearch.E7.QuaternionTrialityPacket

universe u

variable {A : Type u} [AddCommGroup A]

/-- The index signature forced by the cited degree-four-unitary quadratic-extension results:
at least one labelled Clifford class has index at most two. -/
def HasDegreeFourUnitaryQuadraticExtensionIndexSignature
    (I : BrauerIndexModel A) (P : BrauerPacket A) : Prop :=
  I.index P.cliffordPlus ≤ 2 ∨ I.index P.cliffordMinus ≤ 2

/-- An index-eight quaternion target packet cannot have the index signature forced by a
degree-four-unitary quadratic-extension construction. -/
theorem indexEightTargetPacket_excludes_degreeFourUnitaryQuadraticExtensionIndexSignature
    (I : BrauerIndexModel A)
    (IsQuaternionClass : A → Prop)
    (hQuaternion : QuaternionClassesHaveIndexAtMostTwo I IsQuaternionClass)
    (P : BrauerPacket A)
    (hP : IsIndexEightQuaternionTargetPacket I IsQuaternionClass P) :
    ¬ HasDegreeFourUnitaryQuadraticExtensionIndexSignature I P := by
  intro hSmall
  rcases indexEightTargetPacket_has_index_four
      I IsQuaternionClass hQuaternion P hP with
    ⟨_hUnderlying, hPlus, hMinus⟩
  rcases hSmall with hSmall | hSmall
  · omega
  · omega

end RiemannResearch.E7.QuaternionTrialityPacket
