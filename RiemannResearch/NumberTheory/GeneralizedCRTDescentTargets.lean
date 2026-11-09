import Mathlib.Algebra.Ring.Prod
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Interfaces for generalized CRT and descent claims

These predicates record two interfaces from the generalized CRT discussion
in September 2026. A ring equivalence satisfies the topological CRT interface
when both directions are continuous. A restriction map has effective descent
when compatible local data have a unique global lift.

`ProfiniteCRT` proves the topological CRT interface for the inverse limit of
`Z/nZ` and the product of the `p`-adic integers. The effective descent
interface leaves the local compatibility relation as a parameter.
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
