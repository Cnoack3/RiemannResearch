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

/-- Regard a cocycle whose values lie in a stable subgroup as a cocycle with
that subgroup as its coefficient group.

The compatibility hypothesis identifies the supplied action on the subtype
with the ambient action. -/
def NonabelianCocycle.subgroupValued
    (a : NonabelianCocycle Γ G) (U : Subgroup G)
    [MulDistribMulAction Γ U]
    (hU : ∀ (σ : Γ) (u : U),
      ((σ • u : U) : G) = σ • (u : G))
    (ha : a.ValuesIn U) :
    NonabelianCocycle Γ U where
  toFun := fun σ => ⟨a σ, ha σ⟩
  map_mul' := by
    intro σ τ
    apply Subtype.ext
    change a (σ * τ) =
      a σ * ((↑(σ • (⟨a τ, ha τ⟩ : U)) : G))
    rw [hU]
    exact a.map_mul' σ τ

/-- Gauging a subgroup-valued cocycle by a subgroup element agrees, after
coercion, with gauging the original cocycle in the ambient group. -/
@[simp] theorem NonabelianCocycle.coe_subgroupValued_gauge_apply
    (a : NonabelianCocycle Γ G) (U : Subgroup G)
    [MulDistribMulAction Γ U]
    (hU : ∀ (σ : Γ) (u : U),
      ((σ • u : U) : G) = σ • (u : G))
    (ha : a.ValuesIn U) (q : U) (σ : Γ) :
    ((((a.subgroupValued U hU ha).gauge q) σ : U) : G) =
      (a.gauge (q : G)) σ := by
  simp [NonabelianCocycle.subgroupValued,
    NonabelianCocycle.gauge, hU]

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

/-- If all cocycles on a quotient coefficient group are coboundaries, then an
ambient cocycle valued in the numerator subgroup can be gauged into the
ambient subgroup represented by the quotient kernel.

The subgroup N is normal only inside U; neither U nor the target subgroup V
is required to be normal in the ambient group. The membership equivalence hN
records how the abstract kernel inside U is realized by V inside G.

Source: user-provided quotient-H¹ gauge-filtration argument (25 August 2026);
the source supports the statement and proof strategy. -/
theorem NonabelianCocycle.exists_subgroupGauge_valuesIn_of_quotient_h1
    (a : NonabelianCocycle Γ G) (U V : Subgroup G)
    [MulDistribMulAction Γ U]
    (hU : ∀ (σ : Γ) (u : U),
      ((σ • u : U) : G) = σ • (u : G))
    (N : Subgroup U) [N.Normal]
    [MulDistribMulAction Γ (U ⧸ N)]
    (hquot : ∀ (σ : Γ) (u : U),
      QuotientGroup.mk' N (σ • u) =
        σ • QuotientGroup.mk' N u)
    (hN : ∀ u : U, u ∈ N ↔ (u : G) ∈ V)
    (hH1 : ∀ b : NonabelianCocycle Γ (U ⧸ N),
      b.IsCoboundary)
    (ha : a.ValuesIn U) :
    ∃ q : U, (a.gauge (q : G)).ValuesIn V := by
  let aU : NonabelianCocycle Γ U :=
    a.subgroupValued U hU ha
  have hquotient :
      (aU.map (QuotientGroup.mk' N) hquot).IsCoboundary :=
    hH1 _
  obtain ⟨q, hq⟩ :=
    (aU.map_quotient_isCoboundary_iff_exists_gauge_valuesIn
      N hquot).mp hquotient
  refine ⟨q, ?_⟩
  intro σ
  have hv : (((aU.gauge q) σ : U) : G) ∈ V :=
    (hN ((aU.gauge q) σ)).mp (hq σ)
  simpa [aU] using hv

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

/-- Gauging into a coefficient subgroup with trivial nonabelian H¹ is
equivalent to global neutrality.

This is the abstract cocycle form of the common-Borel warning in the E8
application. It does not assert that a split Borel reduction exists, nor
does it construct the algebraic-group/flag-variety comparison. -/
theorem NonabelianCocycle.isCoboundary_iff_canGaugeInto_of_valuesIn_isCoboundary
    (a : NonabelianCocycle Γ G) (B : Subgroup G)
    (hB :
      ∀ z : NonabelianCocycle Γ G, z.ValuesIn B → z.IsCoboundary) :
    a.IsCoboundary ↔ a.CanGaugeInto B := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    rw [NonabelianCocycle.gauge_gauge, mul_inv_cancel,
      NonabelianCocycle.gauge_one]
    intro σ
    simp [NonabelianCocycle.trivial]
  · rintro ⟨g, hg⟩
    exact (a.isCoboundary_gauge_iff g).1 (hB _ hg)

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
