import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Prod

/-!
# Completing a projection by an orthogonal reflected copy

Source: user-provided reciprocal Mellin construction (2026-09-20).
The star-semiring calculation exposes the zero cross term required for
idempotence. The relative product criterion preserves the original density
obligation; it does not supply an RH density theorem.
-/

namespace RiemannResearch.Analysis.ReflectedProjection

section Algebra
variable {A : Type*} [Semiring A]

/-- Complete an operator by its reflected copy. -/
def completion (P J : A) : A := P + J * P * J

theorem conjugate_idempotent (P J : A) (hP : P * P = P)
    (hJ : J * J = 1) :
    (J * P * J) * (J * P * J) = J * P * J := by
  calc
    (J * P * J) * (J * P * J) = J * P * (J * J) * P * J := by
      simp only [mul_assoc]
    _ = J * (P * P) * J := by
      rw [hJ]
      simp only [mul_one, mul_assoc]
    _ = J * P * J := by rw [hP]

theorem completion_idempotent (P J : A) (hP : P * P = P)
    (hJ : J * J = 1) (hOrth : P * J * P = 0) :
    completion P J * completion P J = completion P J := by
  have hPR : P * (J * P * J) = 0 := by
    calc
      P * (J * P * J) = (P * J * P) * J := by simp only [mul_assoc]
      _ = 0 := by rw [hOrth, zero_mul]
  have hRP : (J * P * J) * P = 0 := by
    calc
      (J * P * J) * P = J * (P * J * P) := by simp only [mul_assoc]
      _ = 0 := by rw [hOrth, mul_zero]
  have hRR := conjugate_idempotent P J hP hJ
  simp only [completion, add_mul, mul_add, hP, hPR, hRP, hRR,
    add_zero, zero_add]

theorem completion_commutes (P J : A) (hJ : J * J = 1) :
    completion P J * J = J * completion P J := by
  have hright : (J * P * J) * J = J * P := by
    calc
      (J * P * J) * J = (J * P) * (J * J) := by rw [mul_assoc]
      _ = J * P := by rw [hJ, mul_one]
  have hleft : J * (J * P * J) = P * J := by
    calc
      J * (J * P * J) = (J * J) * P * J := by simp only [mul_assoc]
      _ = P * J := by rw [hJ, one_mul]
  change (P + J * P * J) * J = J * (P + J * P * J)
  rw [add_mul, mul_add, hright, hleft]
  exact add_comm _ _


/-- Any additional symmetry commuting with the original projection and
reflection also commutes with the completed projection. For conjugation,
apply this to the operators on the underlying real space. -/
theorem completion_commutes_with (P J C : A)
    (hPC : P * C = C * P) (hJC : J * C = C * J) :
    completion P J * C = C * completion P J := by
  have hR : (J * P * J) * C = C * (J * P * J) := by
    calc
      (J * P * J) * C = J * P * (J * C) := by simp only [mul_assoc]
      _ = J * P * (C * J) := by rw [hJC]
      _ = J * (P * C) * J := by simp only [mul_assoc]
      _ = J * (C * P) * J := by rw [hPC]
      _ = (J * C) * P * J := by simp only [mul_assoc]
      _ = (C * J) * P * J := by rw [hJC]
      _ = C * (J * P * J) := by simp only [mul_assoc]
  simp only [completion, add_mul, mul_add, hPC, hR]

variable [StarRing A]

theorem completion_selfAdjoint (P J : A) (hP : star P = P)
    (hJ : star J = J) : star (completion P J) = completion P J := by
  simp only [completion, star_add, star_mul, hP, hJ, mul_assoc]

end Algebra

section Product
variable {R E : Type*} [Semiring R] [AddCommMonoid E] [Module R E]

/-- Doubling the relative ambient preserves the full-space criterion. -/
theorem prod_eq_top_iff (S : Submodule R E) :
    S.prod S = (⊤ : Submodule R (E × E)) ↔ S = ⊤ := by
  constructor
  · intro h
    apply le_antisymm le_top
    intro x _
    have hp : (x, (0 : E)) ∈ S.prod S := by
      rw [h]
      trivial
    exact hp.1
  · intro h
    apply le_antisymm le_top
    intro x _
    change x.1 ∈ S ∧ x.2 ∈ S
    constructor <;> rw [h] <;> trivial

theorem swap_mem_prod_iff (S : Submodule R E) (x : E × E) :
    Prod.swap x ∈ S.prod S ↔ x ∈ S.prod S := by
  change (x.2 ∈ S ∧ x.1 ∈ S) ↔ (x.1 ∈ S ∧ x.2 ∈ S)
  exact and_comm

end Product

/-- The completed operator in the two relative coordinates. -/
def doubled {E : Type*} (P : E → E) (x : E × E) : E × E :=
  (P x.1, P x.2)

theorem doubled_swap {E : Type*} (P : E → E) (x : E × E) :
    doubled P (Prod.swap x) = Prod.swap (doubled P x) := rfl

theorem doubled_idempotent {E : Type*} (P : E → E)
    (hP : ∀ x, P (P x) = P x) :
    ∀ x, doubled P (doubled P x) = doubled P x := by
  intro x
  exact Prod.ext (hP x.1) (hP x.2)

theorem doubled_eq_id_iff {E : Type*} (P : E → E) :
    doubled P = id ↔ P = id := by
  constructor
  · intro h
    funext x
    exact congrArg (fun f : E × E → E × E => (f (x, x)).1) h
  · intro h
    subst P
    rfl

end RiemannResearch.Analysis.ReflectedProjection
