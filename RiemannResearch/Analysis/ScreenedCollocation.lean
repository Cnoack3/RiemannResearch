/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import RiemannResearch.LinearAlgebra.ObliqueBlockElimination
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Physical screening and nonsymmetric collocation coordinates

Source: `CanonicalPrimePowerUpdatesResearch20261107.md`, Section 3.
The Gram inverse, test maps and their inverses are explicit finite-system
data. No bound on an inverse or canonical response is postulated.

The application uses finite-dimensional coordinate Hilbert spaces. The
identities are valid for arbitrary real Hilbert spaces whenever the displayed
inverse equations hold. The source Gram and collocation Schur operators
remain different objects.
-/

noncomputable section

namespace ContinuousLinearMap
variable {H X Y : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- An independent physical synthesis has an injective physical Gram map.
This is a finite-stage existence fact and gives no inverse-norm bound. -/
theorem synthesisGram_injective (U : X →L[ℝ] H) (hU : Function.Injective U) :
    Function.Injective (U.adjoint.comp U) := by
  intro x y hxy
  have hz : (U.adjoint.comp U) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hi := congrArg (fun z : X => inner ℝ (x - y) z) hz
  simp only [ContinuousLinearMap.comp_apply, adjoint_inner_right,
    inner_zero_right, real_inner_self_eq_norm_sq] at hi
  have hzero : U (x - y) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  apply sub_eq_zero.mp
  exact hU (by simpa only [map_zero] using hzero)

/-- The actual physical Gram inverse exists for every independent finite
synthesis; no quantitative coercivity hypothesis is assumed. -/
def synthesisGramEquiv [FiniteDimensional ℝ X]
    (U : X →L[ℝ] H) (hU : Function.Injective U) : X ≃ₗ[ℝ] X :=
  LinearEquiv.ofInjectiveEndo (U.adjoint.comp U).toLinearMap
    (synthesisGram_injective U hU)

def synthesisGramInverse [FiniteDimensional ℝ X]
    (U : X →L[ℝ] H) (hU : Function.Injective U) : X →L[ℝ] X :=
  (synthesisGramEquiv U hU).symm.toLinearMap.toContinuousLinearMap

theorem synthesisGramInverse_right [FiniteDimensional ℝ X]
    (U : X →L[ℝ] H) (hU : Function.Injective U) (x : X) :
    U.adjoint (U (synthesisGramInverse U hU x)) = x := by
  change synthesisGramEquiv U hU ((synthesisGramEquiv U hU).symm x) = x
  exact (synthesisGramEquiv U hU).apply_symm_apply x

/-- New physical synthesis with its projection onto the old synthesis removed.
Here `I` represents the inverse of the old physical Gram operator. -/
def screenedSynthesis (U : X →L[ℝ] H) (V : Y →L[ℝ] H) (I : X →L[ℝ] X) :
    Y →L[ℝ] H :=
  V - U.comp (I.comp (U.adjoint.comp V))

theorem screenedSynthesis_apply (U : X →L[ℝ] H) (V : Y →L[ℝ] H)
    (I : X →L[ℝ] X) (y : Y) :
    screenedSynthesis U V I y = V y - U (I (U.adjoint (V y))) := rfl

/-- Screening is an invertible triangular coordinate change, hence preserves
independence of the complete old/new synthesis family. No Gram bound is used. -/
theorem screenedSynthesis_joint_injective (U : X →L[ℝ] H) (V : Y →L[ℝ] H)
    (I : X →L[ℝ] X)
    (hUV : Function.Injective (fun p : X × Y => U p.1 + V p.2)) :
    Function.Injective (fun p : X × Y => U p.1 + screenedSynthesis U V I p.2) := by
  intro p q hpq
  have he : U (p.1 - I (U.adjoint (V p.2))) + V p.2 =
      U (q.1 - I (U.adjoint (V q.2))) + V q.2 := by
    calc
      _ = U p.1 + screenedSynthesis U V I p.2 := by
        rw [map_sub, screenedSynthesis_apply]
        abel
      _ = U q.1 + screenedSynthesis U V I q.2 := hpq
      _ = _ := by
        rw [map_sub, screenedSynthesis_apply]
        abel
  have hc : (p.1 - I (U.adjoint (V p.2)), p.2) =
      (q.1 - I (U.adjoint (V q.2)), q.2) := hUV he
  have hparts := Prod.mk.inj hc
  have hy : p.2 = q.2 := hparts.2
  have hx : p.1 - I (U.adjoint (V p.2)) =
      q.1 - I (U.adjoint (V q.2)) := hparts.1
  rw [hy] at hx
  refine Prod.ext ?_ hy
  simpa only [sub_add_cancel] using
    congrArg (fun x => x + I (U.adjoint (V q.2))) hx

/-- Exact screening from the old Gram right-inverse equation. -/
theorem adjoint_screenedSynthesis_eq_zero (U : X →L[ℝ] H) (V : Y →L[ℝ] H)
    (I : X →L[ℝ] X) (hI : ∀ x, U.adjoint (U (I x)) = x) (y : Y) :
    U.adjoint (screenedSynthesis U V I y) = 0 := by
  rw [screenedSynthesis_apply, map_sub, hI, sub_self]

theorem inner_old_screenedSynthesis (U : X →L[ℝ] H) (V : Y →L[ℝ] H)
    (I : X →L[ℝ] X) (hI : ∀ x, U.adjoint (U (I x)) = x) (x : X) (y : Y) :
    inner ℝ (U x) (screenedSynthesis U V I y) = 0 := by
  rw [← adjoint_inner_right, adjoint_screenedSynthesis_eq_zero U V I hI]
  simp

/-- The physical Gram Schur identity, as an exact sesquilinear equality.
Its right side is `V*V - B* I B`, where `B = U* V`. -/
theorem screenedSynthesis_inner (U : X →L[ℝ] H) (V : Y →L[ℝ] H)
    (I : X →L[ℝ] X) (hI : ∀ x, U.adjoint (U (I x)) = x) (x y : Y) :
    inner ℝ (screenedSynthesis U V I x) (screenedSynthesis U V I y) =
      inner ℝ (V x) (V y) -
        inner ℝ (U.adjoint (V x)) (I (U.adjoint (V y))) := by
  change inner ℝ (V x - U (I (U.adjoint (V x))))
    (screenedSynthesis U V I y) = _
  rw [inner_sub_left, inner_old_screenedSynthesis U V I hI, sub_zero,
    screenedSynthesis_apply, inner_sub_right,
    ← adjoint_inner_left U (I (U.adjoint (V y))) (V x)]

/-- The screened Gram right-hand side is a response pairing. This theorem
does not equate it to a difference-test source. -/
theorem screened_response_gram (U : X →L[ℝ] H) (V : Y →L[ℝ] H)
    (I : X →L[ℝ] X) (hI : ∀ x, U.adjoint (U (I x)) = x)
    (δ : H) (x : X) (y z : Y)
    (hδ : δ = U x + screenedSynthesis U V I y) :
    inner ℝ δ (screenedSynthesis U V I z) =
      inner ℝ (screenedSynthesis U V I y) (screenedSynthesis U V I z) := by
  rw [hδ, inner_add_left, inner_old_screenedSynthesis U V I hI, zero_add]

/-- Full signed physical energy increase. The old refit cross term is kept. -/
theorem screened_energy_update (U : X →L[ℝ] H) (V : Y →L[ℝ] H)
    (I : X →L[ℝ] X) (hI : ∀ x, U.adjoint (U (I x)) = x)
    (c x : X) (y : Y) :
    ‖U c + (U x + screenedSynthesis U V I y)‖ ^ 2 - ‖U c‖ ^ 2 =
      2 * inner ℝ (U c) (U x) + ‖U x‖ ^ 2 +
        ‖screenedSynthesis U V I y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_add_sq_real, inner_add_right,
    inner_old_screenedSynthesis U V I hI x y,
    inner_old_screenedSynthesis U V I hI c y]
  ring

/-- Exact nonsymmetric Schur assembly for the screened coordinate systems.
The old and new test maps are unrelated adjoints in general; no symmetry
between the two cross blocks is assumed. -/
theorem screened_collocation_schur
    (U : X →L[ℝ] H) (V : Y →L[ℝ] H) (I : X →L[ℝ] X)
    (T₀ : H →L[ℝ] X) (T₁ : H →L[ℝ] Y)
    (J₀ : X →ₗ[ℝ] X) (J₁ : Y →ₗ[ℝ] Y)
    (hJ₀ : ∀ x, J₀ (T₀ (U x)) = x)
    (hJ₁ : ∀ y, J₁ (T₁ (screenedSynthesis U V I y) -
      T₁ (U (J₀ (T₀ (screenedSynthesis U V I y))))) = y)
    (x : X) (y : Y) (b : H)
    (h₀ : T₀ (U x + screenedSynthesis U V I y) = T₀ b)
    (h₁ : T₁ (U x + screenedSynthesis U V I y) = T₁ b) :
    y = J₁ (T₁ b - T₁ (U (J₀ (T₀ b)))) ∧
      x = J₀ (T₀ b) - J₀ (T₀ (screenedSynthesis U V I y)) ∧
      T₁ (screenedSynthesis U V I y) -
        T₁ (U (J₀ (T₀ (screenedSynthesis U V I y)))) =
        T₁ b - T₁ (U (J₀ (T₀ b))) := by
  let W := screenedSynthesis U V I
  let A : X →ₗ[ℝ] X := T₀.toLinearMap.comp U.toLinearMap
  let B : Y →ₗ[ℝ] X := T₀.toLinearMap.comp W.toLinearMap
  let C : X →ₗ[ℝ] Y := T₁.toLinearMap.comp U.toLinearMap
  let D : Y →ₗ[ℝ] Y := T₁.toLinearMap.comp W.toLinearMap
  have hA : ∀ x, J₀ (A x) = x := hJ₀
  have h₀' : A x + B y = T₀ b := by
    change T₀ (U x) + T₀ (W y) = T₀ b
    rw [← map_add]
    exact h₀
  have h₁' : C x + D y = T₁ b := by
    change T₁ (U x) + T₁ (W y) = T₁ b
    rw [← map_add]
    exact h₁
  have he := RiemannResearch.LinearAlgebra.ObliqueBlockElimination.block_elimination
    A J₀ B C D hA x (T₀ b) y (T₁ b) h₀' h₁'
  have hx : x = J₀ (T₀ b) - J₀ (T₀ (W y)) := he.1
  have hs : T₁ (W y) - T₁ (U (J₀ (T₀ (W y)))) =
      T₁ b - T₁ (U (J₀ (T₀ b))) := he.2
  have hy : y = J₁ (T₁ b - T₁ (U (J₀ (T₀ b)))) := by
    calc
      y = J₁ (T₁ (W y) - T₁ (U (J₀ (T₀ (W y))))) := (hJ₁ y).symm
      _ = _ := congrArg J₁ hs
  exact ⟨hy, hx, hs⟩

end ContinuousLinearMap
