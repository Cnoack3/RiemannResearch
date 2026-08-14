/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GaloisCohomology.NonabelianH1

/-!
# Gauge reduction through a subgroup filtration

This module isolates the logically valid part of a Borel/unipotent reduction
for nonabelian one-cocycles. A first gauge may put the cocycle in a subgroup
'B'; a second, 'B'-valued gauge must remove the residual quotient obstruction
and put it in 'U'; only then may a vanishing theorem for 'U' finish the proof.

In the E8 application, 'B' is intended to be a Galois-stable Borel and 'U' its
unipotent radical. The second stage is the residual torus obstruction. The
theorem below deliberately keeps that stage as a separate hypothesis: an
additive Hilbert-90 argument for 'U' does not supply it.

Source: user-provided Research Target 7.1 analysis (14 August 2026); the source
supports the proof strategy and the separation of the torus and unipotent
obligations.
-/

namespace RiemannResearch.GaloisCohomology

universe u v w

variable {Γ : Type u} {G : Type v}
variable [Group Γ] [Group G] [MulDistribMulAction Γ G]

/-- A nonabelian cocycle has all its values in the specified subgroup. -/
def NonabelianCocycle.ValuesIn
    (a : NonabelianCocycle Γ G) (S : Subgroup G) : Prop :=
  ∀ σ, a σ ∈ S

/-- Some gauge of the cocycle has all its values in the specified subgroup. -/
def NonabelianCocycle.CanGaugeInto
    (a : NonabelianCocycle Γ G) (S : Subgroup G) : Prop :=
  ∃ g : G, (a.gauge g).ValuesIn S

/-- Exact neutral-image criterion for a change of coefficient group.

For an equivariant inclusion of a torus into a reductive group, the witness
'g' is the boundary lift represented geometrically by a rational point in the
appropriate homogeneous-space fiber.  In particular, the image of a torus
class may be neutral even when the torus class itself is not. -/
theorem NonabelianCocycle.map_isCoboundary_iff_exists_boundaryLift
    {T : Type w} [Group T] [MulDistribMulAction Γ T]
    (a : NonabelianCocycle Γ T) (φ : T →* G)
    (hφ : ∀ (σ : Γ) (t : T), φ (σ • t) = σ • φ t) :
    (a.map φ hφ).IsCoboundary ↔
      ∃ g : G, ∀ σ, φ (a σ) = g⁻¹ * σ • g := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    intro σ
    have h := congrArg (fun z : NonabelianCocycle Γ G => z σ) hg
    simpa [NonabelianCocycle.map, NonabelianCocycle.trivial,
      NonabelianCocycle.gauge] using h
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    ext σ
    simpa [NonabelianCocycle.map, NonabelianCocycle.trivial,
      NonabelianCocycle.gauge] using hg σ

/-- Coboundary status is invariant under gauging. -/
theorem NonabelianCocycle.isCoboundary_gauge_iff
    (a : NonabelianCocycle Γ G) (g : G) :
    (a.gauge g).IsCoboundary ↔ a.IsCoboundary := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q * g⁻¹, ?_⟩
    have h :=
      congrArg (fun z : NonabelianCocycle Γ G => z.gauge g⁻¹) hq
    rw [NonabelianCocycle.gauge_gauge,
      mul_inv_cancel, NonabelianCocycle.gauge_one] at h
    rw [NonabelianCocycle.gauge_gauge] at h
    exact h
  · rintro ⟨q, hq⟩
    refine ⟨q * g, ?_⟩
    rw [hq]
    exact NonabelianCocycle.gauge_gauge g q
      (NonabelianCocycle.trivial : NonabelianCocycle Γ G)

/-- A two-stage subgroup reduction.

The hypotheses have distinct mathematical roles:

* 'hB' is the simultaneous field-valued cell-to-'B' reduction;
* 'hT' is the residual quotient (torus in the Borel application) correction;
* 'hU' is the terminal vanishing theorem (unipotent Hilbert 90 in the
  application).

Thus finite Bruhat contraction plus unipotent factorization proves neutrality
only after the middle hypothesis has also been supplied. -/
theorem NonabelianCocycle.isCoboundary_of_subgroup_filtration
    (a : NonabelianCocycle Γ G) (B U : Subgroup G)
    (hB : a.CanGaugeInto B)
    (hT :
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn B →
        ∃ q : B, (z.gauge (q : G)).ValuesIn U)
    (hU :
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn U → z.IsCoboundary) :
    a.IsCoboundary := by
  obtain ⟨r, hr⟩ := hB
  obtain ⟨q, hq⟩ := hT (a.gauge r) hr
  have hz : ((a.gauge r).gauge (q : G)).IsCoboundary :=
    hU _ hq
  have hr' : (a.gauge r).IsCoboundary :=
    ((a.gauge r).isCoboundary_gauge_iff (q : G)).1 hz
  exact (a.isCoboundary_gauge_iff r).1 hr'

end RiemannResearch.GaloisCohomology
