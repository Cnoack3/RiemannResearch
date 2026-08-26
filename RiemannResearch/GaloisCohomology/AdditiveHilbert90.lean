/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.FieldTheory.Finite.Trace
import RiemannResearch.GaloisCohomology.AdditiveH1Bridge

/-!
# Additive Hilbert 90

This module proves additive Hilbert 90 in Mathlib's degree-one group-cohomology
model. For a finite Galois extension L/K, every class in H¹(Gal(L/K), L) is
zero. The proof chooses an element c of trace one and sends an additive
one-cocycle z to the explicit potential

  -∑ τ, z(τ) * τ(c).

It then packages the result as a constructor for a subgroup gauge-filtration
layer whose quotient is equivariantly the additive group of L.

Source:
* Mathlib, FieldTheory.Finite.Trace, for trace surjectivity and the expression
  of the field trace as a sum over Galois automorphisms:
  https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/FieldTheory/Finite/Trace.lean
* User-provided quotient-H¹ gauge-filtration continuation handoff
  (25 August 2026), for the intended filtration application.
-/

open scoped BigOperators

noncomputable section

namespace RiemannResearch.GaloisCohomology

/-- Additive Hilbert 90 in Mathlib's degree-one group-cohomology model. -/
theorem additiveHilbert90_h1_eq_zero
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ∀ x : groupCohomology.H1 (Rep.ofDistribMulAction K Gal(L/K) L), x = 0 := by
  let A : Rep K Gal(L/K) := Rep.ofDistribMulAction K Gal(L/K) L
  intro x
  induction x using groupCohomology.H1_induction_on with
  | h z =>
      rw [groupCohomology.H1π_eq_zero_iff]
      obtain ⟨c, hc⟩ := Algebra.trace_surjective K L 1
      let zL : Gal(L/K) → L := fun τ => z τ
      let S : L := ∑ τ : Gal(L/K), zL τ * (τ • c)
      have htrace : (∑ τ : Gal(L/K), τ • c) = 1 := by
        simpa [hc, AlgEquiv.smul_def] using
          (trace_eq_sum_automorphisms (K := K) c).symm
      have hσS (σ : Gal(L/K)) : σ • S = S - zL σ := by
        have hcocycle (τ : Gal(L/K)) :
            zL (σ * τ) = σ • zL τ + zL σ := by
          have hz :=
            (groupCohomology.mem_cocycles₁_iff (A := A) z).mp z.property σ τ
          change zL (σ * τ) = σ • zL τ + zL σ at hz
          exact hz
        have hreindex :
            (∑ τ : Gal(L/K), zL (σ * τ) * ((σ * τ) • c)) = S := by
          simpa [S] using
            (Equiv.sum_comp (Equiv.mulLeft σ)
              (fun τ : Gal(L/K) => zL τ * (τ • c)))
        have hreindex_c :
            (∑ τ : Gal(L/K), (σ * τ) • c) =
              ∑ τ : Gal(L/K), τ • c := by
          simpa using
            (Equiv.sum_comp (Equiv.mulLeft σ)
              (fun τ : Gal(L/K) => τ • c))
        calc
          σ • S =
              ∑ τ : Gal(L/K), (σ • zL τ) * ((σ * τ) • c) := by
                simp only [S, AlgEquiv.smul_def, map_sum, map_mul, mul_smul]
          _ = ∑ τ : Gal(L/K),
                (zL (σ * τ) - zL σ) * ((σ * τ) • c) := by
                apply Finset.sum_congr rfl
                intro τ hτ
                rw [hcocycle]
                ring
          _ = (∑ τ : Gal(L/K), zL (σ * τ) * ((σ * τ) • c)) -
                zL σ * (∑ τ : Gal(L/K), (σ * τ) • c) := by
                simp_rw [sub_mul]
                rw [Finset.sum_sub_distrib, Finset.mul_sum]
          _ = S - zL σ := by rw [hreindex, hreindex_c, htrace, mul_one]
      refine ⟨(show A from (-S : L)), ?_⟩
      funext σ
      change (σ • (-S) - (-S) : L) = zL σ
      rw [smul_neg, hσS]
      ring

/-- Extend a subgroup gauge filtration across a quotient identified
equivariantly with the additive group of a finite Galois extension. -/
def SubgroupGaugeFiltration.stepOfGaloisAdditiveQuotient
    {K L : Type u} {G : Type v}
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Group G] [MulDistribMulAction Gal(L/K) G]
    {U V : Subgroup G} [MulDistribMulAction Gal(L/K) U]
    (hU : ∀ (σ : Gal(L/K)) (u : U),
      ((σ • u : U) : G) = σ • (u : G))
    (N : Subgroup U) [N.Normal]
    [MulDistribMulAction Gal(L/K) (U ⧸ N)]
    (hquot : ∀ (σ : Gal(L/K)) (u : U),
      QuotientGroup.mk' N (σ • u) = σ • QuotientGroup.mk' N u)
    (hN : ∀ u : U, u ∈ N ↔ (u : G) ∈ V)
    (e : (U ⧸ N) ≃* Multiplicative L)
    (hρ : ∀ (σ : Gal(L/K)) (q : U ⧸ N),
      (e (σ • q)).toAdd = σ • (e q).toAdd)
    (tail : SubgroupGaugeFiltration Gal(L/K) G V) :
    SubgroupGaugeFiltration Gal(L/K) G U :=
  SubgroupGaugeFiltration.stepOfAdditiveQuotientH1
    hU N hquot hN
    (Rep.ofDistribMulAction K Gal(L/K) L) e
    (by
      intro σ q
      change (e (σ • q)).toAdd = σ • (e q).toAdd
      exact hρ σ q)
    additiveHilbert90_h1_eq_zero tail

end RiemannResearch.GaloisCohomology
