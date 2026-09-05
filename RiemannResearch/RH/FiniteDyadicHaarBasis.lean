/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteDyadicHaarSlope
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.Cardinality

/-!
# The finite Haar basis and its curvature coordinates

The dyadic atoms form a basis of the entire finite mean-zero slope space.
Cardinality and dimension agree, including m=0. The exact Gram formula
gives coefficients and Parseval with counting squared norm 2 ^ (m-level).
Transport through curvatureMeanZeroSlopeEquiv yields a sparse curvature basis.

Source: user-provided argument, RH_Proof_First_Continuation_2026-09-04.md,
Section 5, and the dyadic continuation queue in the canonical handoff v14.
The sources support the coordinate construction and research direction.
These finite basis results do not assert analytic density or positivity
of a concrete arithmetic kernel.
-/

namespace RiemannResearch.RH.PrimeGapCurvature

noncomputable section

open scoped BigOperators

abbrev FiniteDyadicHaarIndex (m : ℕ) := Σ l : Fin m, Fin (2 ^ l.val)

def finiteDyadicHaarSlope (m : ℕ) (i : FiniteDyadicHaarIndex m) :
    meanZeroSlopeSubmodule (2 ^ m - 1) :=
  ⟨fun j => finiteDyadicHaarAtom m i.1.val i.2 (Fin.cast (dyadicDimension_eq m) j),
    finiteDyadicHaarAtom_mem_meanZeroSlopeSubmodule m i.1.val i.1.isLt i.2⟩

theorem card_finiteDyadicHaarIndex (m : ℕ) :
    Fintype.card (FiniteDyadicHaarIndex m) = 2 ^ m - 1 := by
  change Fintype.card (Σ l : Fin m, Fin (2 ^ l.val)) = _
  simp only [Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun l => 2 ^ l) m]
  have hg := geom_sum_mul_add (1 : ℕ) m
  norm_num at hg
  omega

theorem finiteDyadicHaarSlope_inner (m : ℕ) (i k : FiniteDyadicHaarIndex m) :
    (∑ j, (finiteDyadicHaarSlope m i).1 j * (finiteDyadicHaarSlope m k).1 j) =
      if i = k then ((2 ^ (m - i.1.val) : ℕ) : ℝ) else 0 := by
  classical
  change (∑ j : Fin (2 ^ m - 1 + 1),
    finiteDyadicHaarAtom m i.1.val i.2 (Fin.cast (dyadicDimension_eq m) j) *
    finiteDyadicHaarAtom m k.1.val k.2 (Fin.cast (dyadicDimension_eq m) j)) = _
  have hs :
      (∑ j : Fin (2 ^ m - 1 + 1),
        finiteDyadicHaarAtom m i.1.val i.2 (Fin.cast (dyadicDimension_eq m) j) *
        finiteDyadicHaarAtom m k.1.val k.2 (Fin.cast (dyadicDimension_eq m) j)) =
      ∑ j : Fin (2 ^ m),
        finiteDyadicHaarAtom m i.1.val i.2 j * finiteDyadicHaarAtom m k.1.val k.2 j :=
    Fintype.sum_equiv (Fin.castOrderIso (dyadicDimension_eq m)).toEquiv
      (fun j => finiteDyadicHaarAtom m i.1.val i.2 (Fin.cast (dyadicDimension_eq m) j) *
        finiteDyadicHaarAtom m k.1.val k.2 (Fin.cast (dyadicDimension_eq m) j))
      (fun j => finiteDyadicHaarAtom m i.1.val i.2 j * finiteDyadicHaarAtom m k.1.val k.2 j)
      (fun j => rfl)
  rw [hs]
  by_cases hik : i = k
  · subst k
    simp only [← sq]
    exact finiteDyadicHaarAtom_sum_sq m i.1.val i.1.isLt i.2
  · rw [if_neg hik]
    apply finiteDyadicHaarAtom_inner_zero m i.1.val k.1.val i.1.isLt k.1.isLt i.2 k.2
    by_contra hh
    push Not at hh
    apply hik
    rcases i with ⟨i, q⟩
    rcases k with ⟨k, r⟩
    have hik' : i = k := Fin.ext hh.1
    subst k
    have hqr : q = r := Fin.ext hh.2
    subst r
    rfl

private lemma realVector_independent_of_orthogonal
    {ι J : Type*} [Finite ι] [Fintype J] [DecidableEq ι]
    (v : ι → J → ℝ) (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (hinner : ∀ i k, (∑ j, v i j * v k j) = if i = k then d i else 0) :
    LinearIndependent ℝ v := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have hcoord : ∀ j, ∑ i, g i * v i j = 0 := by
    intro j
    have he := congr_fun hg j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using he
  have he : g k * d k = 0 := by
    calc
      g k * d k = ∑ i, g i * (∑ j, v i j * v k j) := by
        simp_rw [hinner]
        simp
      _ = ∑ i, ∑ j, g i * (v i j * v k j) := by simp_rw [Finset.mul_sum]
      _ = ∑ j, ∑ i, g i * (v i j * v k j) := Finset.sum_comm
      _ = ∑ j, (∑ i, g i * v i j) * v k j := by
        simp_rw [Finset.sum_mul, mul_assoc]
      _ = 0 := by simp_rw [hcoord]; simp
  exact (mul_eq_zero.mp he).resolve_right (hd k)

theorem finiteDyadicHaarSlope_linearIndependent (m : ℕ) :
    LinearIndependent ℝ (finiteDyadicHaarSlope m) := by
  apply LinearIndependent.of_comp (meanZeroSlopeSubmodule (2 ^ m - 1)).subtype
  apply realVector_independent_of_orthogonal
    (fun i => (finiteDyadicHaarSlope m i).1)
    (fun i => ((2 ^ (m - i.1.val) : ℕ) : ℝ))
  · intro i
    positivity
  · exact finiteDyadicHaarSlope_inner m

theorem finrank_meanZeroSlopeSubmodule (n : ℕ) :
    Module.finrank ℝ (meanZeroSlopeSubmodule n) = n := by
  rw [← (curvatureMeanZeroSlopeEquiv n).finrank_eq]
  exact Module.finrank_fin_fun ℝ

theorem finiteDyadicHaarSlope_span (m : ℕ) :
    Submodule.span ℝ (Set.range (finiteDyadicHaarSlope m)) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card (finiteDyadicHaarSlope_linearIndependent m),
    card_finiteDyadicHaarIndex, finrank_meanZeroSlopeSubmodule]

def finiteDyadicHaarBasis (m : ℕ) :
    Module.Basis (FiniteDyadicHaarIndex m) ℝ (meanZeroSlopeSubmodule (2 ^ m - 1)) :=
  Module.Basis.mk (finiteDyadicHaarSlope_linearIndependent m)
    (by rw [finiteDyadicHaarSlope_span])

@[simp] theorem finiteDyadicHaarBasis_apply (m : ℕ) (i : FiniteDyadicHaarIndex m) :
    finiteDyadicHaarBasis m i = finiteDyadicHaarSlope m i :=
  Module.Basis.mk_apply _ _ _


/-- The Haar basis transported to adjacent-curvature coordinates. -/
def finiteDyadicHaarCurvatureBasis (m : ℕ) :
    Module.Basis (FiniteDyadicHaarIndex m) ℝ (Fin (2 ^ m - 1) → ℝ) :=
  (finiteDyadicHaarBasis m).map (curvatureMeanZeroSlopeEquiv (2 ^ m - 1)).symm

@[simp] theorem finiteDyadicHaarCurvatureBasis_apply
    (m : ℕ) (i : FiniteDyadicHaarIndex m) :
    finiteDyadicHaarCurvatureBasis m i =
      finiteSlopeDifferenceMap (2 ^ m - 1) (finiteDyadicHaarSlope m i).1 := by
  rw [finiteDyadicHaarCurvatureBasis, Module.Basis.map_apply, finiteDyadicHaarBasis_apply]
  rfl

/-- Each curvature basis vector is the exact three-jump pattern of its atom. -/
theorem finiteDyadicHaarCurvatureBasis_apply_jump
    (m : ℕ) (i : FiniteDyadicHaarIndex m) (r : Fin (2 ^ m - 1)) :
    finiteDyadicHaarCurvatureBasis m i r =
      let h := 2 ^ (m - i.1.val - 1)
      let a := 2 * i.2.val * h
      (if r.val + 1 = a then 1 else 0) -
        2 * (if r.val + 1 = a + h then 1 else 0) +
        (if r.val + 1 = a + 2 * h then 1 else 0) := by
  rw [finiteDyadicHaarCurvatureBasis_apply]
  exact finiteDyadicHaarAtom_slopeDifference m i.1.val i.2 r



private theorem finiteDyadicHaarBasis_sum_repr_apply (m : ℕ)
    (s : meanZeroSlopeSubmodule (2 ^ m - 1)) (j : Fin (2 ^ m - 1 + 1)) :
    (∑ k, ((finiteDyadicHaarBasis m).repr s) k *
      (finiteDyadicHaarSlope m k).1 j) = s.1 j := by
  have h := congrArg (fun t : meanZeroSlopeSubmodule (2 ^ m - 1) => t.1 j)
    ((finiteDyadicHaarBasis m).sum_repr s)
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, finiteDyadicHaarBasis_apply] using h

private theorem finiteDyadicHaarBasis_inner_repr (m : ℕ)
    (s : meanZeroSlopeSubmodule (2 ^ m - 1)) (i : FiniteDyadicHaarIndex m) :
    (∑ j, s.1 j * (finiteDyadicHaarSlope m i).1 j) =
      ((finiteDyadicHaarBasis m).repr s) i * ((2 ^ (m - i.1.val) : ℕ) : ℝ) := by
  classical
  calc
    _ = ∑ j, (∑ k, ((finiteDyadicHaarBasis m).repr s) k *
        (finiteDyadicHaarSlope m k).1 j) * (finiteDyadicHaarSlope m i).1 j := by
      simp_rw [finiteDyadicHaarBasis_sum_repr_apply]
    _ = ∑ k, ((finiteDyadicHaarBasis m).repr s) k *
        (∑ j, (finiteDyadicHaarSlope m k).1 j *
          (finiteDyadicHaarSlope m i).1 j) := by
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = _ := by
      simp_rw [finiteDyadicHaarSlope_inner]
      simp

/-- Haar coefficients are the counting inner products divided by the exact
squared norms of the unnormalized atoms. -/
theorem finiteDyadicHaarBasis_repr (m : ℕ)
    (s : meanZeroSlopeSubmodule (2 ^ m - 1)) (i : FiniteDyadicHaarIndex m) :
    ((finiteDyadicHaarBasis m).repr s) i =
      (∑ j, s.1 j * (finiteDyadicHaarSlope m i).1 j) /
        ((2 ^ (m - i.1.val) : ℕ) : ℝ) := by
  apply (eq_div_iff (by positivity)).mpr
  exact (finiteDyadicHaarBasis_inner_repr m s i).symm

/-- Exact finite Parseval identity for the unnormalized dyadic Haar basis
and the counting inner product on slope vectors. -/
theorem finiteDyadicHaarBasis_parseval (m : ℕ)
    (s : meanZeroSlopeSubmodule (2 ^ m - 1)) :
    (∑ j, s.1 j ^ 2) =
      ∑ i, (((finiteDyadicHaarBasis m).repr s) i) ^ 2 *
        ((2 ^ (m - i.1.val) : ℕ) : ℝ) := by
  classical
  calc
    _ = ∑ j, s.1 j *
        (∑ i, ((finiteDyadicHaarBasis m).repr s) i *
          (finiteDyadicHaarSlope m i).1 j) := by
      simp_rw [finiteDyadicHaarBasis_sum_repr_apply, pow_two]
    _ = ∑ i, ((finiteDyadicHaarBasis m).repr s) i *
        (∑ j, s.1 j * (finiteDyadicHaarSlope m i).1 j) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp_rw [finiteDyadicHaarBasis_inner_repr]
      apply Finset.sum_congr rfl
      intro i hi
      ring


end

end RiemannResearch.RH.PrimeGapCurvature
