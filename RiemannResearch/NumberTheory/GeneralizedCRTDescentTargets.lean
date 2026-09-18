import Mathlib.Algebra.Ring.Prod
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Interfaces for generalized CRT and descent claims

Source: the user-provided generalized-CRT discussion, September 2026.

Mathlib currently supplies the ordinary finite CRT used by the RH modules.
The two declarations below record the additional interfaces mentioned in the
chat without postulating an instance:

* a candidate ring equivalence is a topological-ring CRT equivalence exactly
  when it and its inverse are continuous;
* a restriction map has effective descent exactly when compatible local data
  have a unique global lift.

The names `Zhat`, `PrimeAdicProduct`, `Global`, and `LocalData` are
parameters deliberately. Instantiating them with the inverse limit of
`Z/nZ`, the product of the `p`-adic integers, or an Amitsur totalization
is the remaining formalization work. Consequently these definitions do not
claim the profinite CRT or derived Amitsur descent theorem.
-/

namespace RiemannResearch.NumberTheory.GeneralizedCRT

/-- Interface for the topological ring isomorphism
`Zhat ≅ ∏ p, Z_p` once both concrete sides and the canonical map exist. -/
def IsTopologicalRingCRT
    {Zhat PrimeAdicProduct : Type*}
    [TopologicalSpace Zhat] [TopologicalSpace PrimeAdicProduct]
    [NonAssocSemiring Zhat] [NonAssocSemiring PrimeAdicProduct]
    (e : Zhat ≃+* PrimeAdicProduct) : Prop :=
  Continuous e ∧ Continuous e.symm

/-- Effective descent interface: compatible local data are precisely those
having a unique global reconstruction. The higher-overlap/totalization
content is carried by the predicate `compatible`. -/
def IsEffectiveDescent
    {Global LocalData : Type*}
    (restrict : Global → LocalData) (compatible : LocalData → Prop) : Prop :=
  ∀ d, compatible d ↔ ∃! x, restrict x = d

end RiemannResearch.NumberTheory.GeneralizedCRT
