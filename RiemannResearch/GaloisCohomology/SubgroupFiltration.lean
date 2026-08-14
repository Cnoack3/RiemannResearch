/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.GroupTheory.QuotientGroup.Defs
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

/-- A quotient cocycle is neutral exactly when a gauge of the original
cocycle takes values in the normal subgroup.

The action on the quotient and the equivariance of the quotient map are kept
explicit. In the Borel application, `B` is the stable Borel, `N` is its
unipotent radical, and `B ⧸ N` is the residual torus. Thus this theorem is
the concrete quotient-group form of the middle correction required by
`isCoboundary_of_subgroup_filtration`. -/
theorem NonabelianCocycle.map_quotient_isCoboundary_iff_exists_gauge_valuesIn
    {B : Type w} [Group B] [MulDistribMulAction Γ B]
    (N : Subgroup B) [N.Normal]
    [MulDistribMulAction Γ (B ⧸ N)]
    (hquot : ∀ (σ : Γ) (b : B),
      QuotientGroup.mk' N (σ • b) =
        σ • QuotientGroup.mk' N b)
    (a : NonabelianCocycle Γ B) :
    (a.map (QuotientGroup.mk' N) hquot).IsCoboundary ↔
      ∃ q : B, (a.gauge q).ValuesIn N := by
  rw [a.map_isCoboundary_iff_exists_boundaryLift]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective N g
    refine ⟨r⁻¹, ?_⟩
    intro σ
    apply (QuotientGroup.eq_one_iff ((a.gauge r⁻¹) σ)).mp
    change QuotientGroup.mk' N
      ((r⁻¹)⁻¹ * a σ * σ • r⁻¹) = 1
    simp only [map_mul, map_inv, hquot]
    simp [hr, hg]
  · rintro ⟨q, hq⟩
    refine ⟨QuotientGroup.mk' N q⁻¹, ?_⟩
    intro σ
    have hmem := hq σ
    have hone :
        QuotientGroup.mk' N ((a.gauge q) σ) = 1 :=
      (QuotientGroup.eq_one_iff ((a.gauge q) σ)).mpr hmem
    change QuotientGroup.mk' N
      (q⁻¹ * a σ * σ • q) = 1 at hone
    simp only [map_mul, map_inv, hquot] at hone
    have hsolve :
        QuotientGroup.mk' N (a σ) =
          QuotientGroup.mk' N q *
            (σ • QuotientGroup.mk' N q)⁻¹ := by
      calc
        QuotientGroup.mk' N (a σ) =
            QuotientGroup.mk' N q *
              ((QuotientGroup.mk' N q)⁻¹ *
                QuotientGroup.mk' N (a σ) *
                  (σ • QuotientGroup.mk' N q)) *
                    (σ • QuotientGroup.mk' N q)⁻¹ := by
                      simp [mul_assoc]
        _ = QuotientGroup.mk' N q * 1 *
              (σ • QuotientGroup.mk' N q)⁻¹ := by rw [hone]
        _ = QuotientGroup.mk' N q *
              (σ • QuotientGroup.mk' N q)⁻¹ := by simp
    rw [hsolve]
    simp

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
