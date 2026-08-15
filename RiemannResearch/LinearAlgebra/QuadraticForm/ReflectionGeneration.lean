/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.Reflection

/-!
# Reflection reduction for quadratic isometries over fields

This file develops the algebraic reflection step needed to compare normalizers
of the Clifford generators with Mathlib's `lipschitzGroup`.  The development
is over an arbitrary field; no order, topology, or positivity is used.

For a vector `x` of nonzero quadratic value, `quadraticReflection` is the
usual reflection
`y ↦ y - polar(x,y) / Q(x) • x`.  Its Clifford lift is an explicit unit in
the Lipschitz group, and left multiplication by that unit composes a
normalizer action with the reflection while toggling the Clifford sign.
-/

namespace RiemannResearch.LinearAlgebra.QuadraticForm

universe u v w

noncomputable section

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The coroot functional used to define reflection in an anisotropic vector. -/
def reflectionFunctional (Q : QuadraticForm K V) (x : V) :
    Module.Dual K V :=
  (Q x)⁻¹ • Q.polarBilin x

theorem reflectionFunctional_self
    (Q : QuadraticForm K V) {x : V} (hx : Q x ≠ 0) :
    reflectionFunctional Q x x = 2 := by
  change (Q x)⁻¹ * QuadraticMap.polar Q x x = 2
  rw [QuadraticMap.polar_self]
  simp only [nsmul_eq_mul]
  field_simp
  norm_num

/-- Reflection in a vector of nonzero quadratic value. -/
def quadraticReflection
    (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0) :
    V ≃ₗ[K] V :=
  Module.reflection (reflectionFunctional_self Q hx)

theorem quadraticReflection_apply
    (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0) (y : V) :
    quadraticReflection Q x hx y =
      y - ((Q x)⁻¹ * QuadraticMap.polar Q x y) • x := by
  rw [quadraticReflection, Module.reflection_apply]
  simp [reflectionFunctional]

theorem quadraticReflection_map
    (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0) (y : V) :
    Q (quadraticReflection Q x hx y) = Q y := by
  rw [quadraticReflection_apply]
  let a := (Q x)⁻¹ * QuadraticMap.polar Q x y
  change Q (y - a • x) = Q y
  rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q,
    QuadraticMap.map_smul, QuadraticMap.polar_smul_right]
  simp only [neg_mul, smul_eq_mul]
  rw [QuadraticMap.polar_comm Q y x]
  dsimp [a]
  field_simp
  ring

/-- Reflection as a quadratic self-isometry. -/
def quadraticReflectionIsometry
    (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0) :
    Q.IsometryEquiv Q :=
  QuadraticMap.IsometryEquiv.mk
    (quadraticReflection Q x hx)
    (quadraticReflection_map Q x hx)

theorem isometry_polar
    (Q : QuadraticForm K V) (h : Q.IsometryEquiv Q) (x y : V) :
    QuadraticMap.polar Q (h x) (h y) =
      QuadraticMap.polar Q x y := by
  simp only [QuadraticMap.polar]
  have hadd : h x + h y = h (x + y) :=
    (h.toLinearEquiv.map_add x y).symm
  rw [hadd, h.map_app, h.map_app, h.map_app]

theorem quadraticReflection_eq_self_of_polar_eq_zero
    (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0)
    (y : V) (hxy : QuadraticMap.polar Q x y = 0) :
    quadraticReflection Q x hx y = y := by
  rw [quadraticReflection_apply, hxy, mul_zero, zero_smul, sub_zero]

theorem polar_sub_left_eq_self
    (Q : QuadraticForm K V) {x y : V} (hQ : Q y = Q x) :
    QuadraticMap.polar Q (y - x) y = Q (y - x) := by
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_self]
  conv_rhs => rw [sub_eq_add_neg]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_neg,
    QuadraticMap.polar_neg_right]
  rw [QuadraticMap.polar_comm Q y x]
  simp only [nsmul_eq_mul]
  rw [hQ]
  ring

theorem quadraticReflection_sub_apply
    (Q : QuadraticForm K V) {x y : V}
    (hQ : Q y = Q x) (hdiff : Q (y - x) ≠ 0) :
    quadraticReflection Q (y - x) hdiff y = x := by
  rw [quadraticReflection_apply, polar_sub_left_eq_self Q hQ]
  field_simp
  simp

theorem map_add_eq_four_mul
    (Q : QuadraticForm K V) {x y : V}
    (hQ : Q y = Q x) (hdiff : Q (y - x) = 0) :
    Q (y + x) = 4 * Q x := by
  have hdiff' := hdiff
  conv_lhs at hdiff' => rw [sub_eq_add_neg]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_neg,
    QuadraticMap.polar_neg_right] at hdiff'
  rw [QuadraticMap.map_add Q]
  rw [hQ] at hdiff' ⊢
  linear_combination -hdiff'

theorem polar_add_left_eq_self
    (Q : QuadraticForm K V) {x y : V}
    (hQ : Q y = Q x) (hdiff : Q (y - x) = 0) :
    QuadraticMap.polar Q (y + x) y = Q (y + x) := by
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_self,
    QuadraticMap.map_add Q]
  have hdiff' := hdiff
  conv_lhs at hdiff' => rw [sub_eq_add_neg]
  rw [QuadraticMap.map_add Q, QuadraticMap.map_neg,
    QuadraticMap.polar_neg_right] at hdiff'
  rw [hQ] at hdiff' ⊢
  rw [QuadraticMap.polar_comm Q x y]
  simp only [nsmul_eq_mul] at *
  ring_nf at hdiff' ⊢

theorem quadraticReflection_add_apply
    (Q : QuadraticForm K V) {x y : V}
    (hQ : Q y = Q x) (hdiff : Q (y - x) = 0)
    (hadd : Q (y + x) ≠ 0) :
    quadraticReflection Q (y + x) hadd y = -x := by
  rw [quadraticReflection_apply,
    polar_add_left_eq_self Q hQ hdiff]
  field_simp
  simp

theorem quadraticReflection_neg_self
    (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0) :
    quadraticReflection Q x hx (-x) = x := by
  rw [map_neg, quadraticReflection]
  rw [Module.reflection_apply_self]
  simp

/-- The Clifford unit represented by an anisotropic vector. -/
def cliffordVectorUnit
    (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0) :
    (CliffordAlgebra Q)ˣ :=
  (CliffordAlgebra.isUnit_ι_of_isUnit Q
    (isUnit_iff_ne_zero.mpr hx)).unit

@[simp] theorem coe_cliffordVectorUnit
    (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0) :
    (cliffordVectorUnit Q x hx : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q x :=
  IsUnit.unit_spec _

theorem cliffordVectorUnit_mem_lipschitzGroup
    (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0) :
    cliffordVectorUnit Q x hx ∈ lipschitzGroup Q := by
  apply Subgroup.subset_closure
  exact ⟨x, coe_cliffordVectorUnit Q x hx⟩

/-- Clifford multiplication by an anisotropic vector realizes the negative of
the corresponding quadratic reflection on vector generators. -/
theorem cliffordVectorUnit_mul_iota
    (Q : QuadraticForm K V) (x : V) (hx : Q x ≠ 0) (y : V) :
    (cliffordVectorUnit Q x hx : CliffordAlgebra Q) *
        CliffordAlgebra.ι Q y =
      -CliffordAlgebra.ι Q (quadraticReflection Q x hx y) *
        (cliffordVectorUnit Q x hx : CliffordAlgebra Q) := by
  rw [coe_cliffordVectorUnit, quadraticReflection_apply,
    map_sub, map_smul]
  let a := (Q x)⁻¹ * QuadraticMap.polar Q x y
  change CliffordAlgebra.ι Q x * CliffordAlgebra.ι Q y =
    -(CliffordAlgebra.ι Q y - a • CliffordAlgebra.ι Q x) *
      CliffordAlgebra.ι Q x
  rw [neg_mul, sub_mul, neg_sub, smul_mul_assoc,
    CliffordAlgebra.ι_sq_scalar]
  have hscalar : a * Q x = QuadraticMap.polar Q x y := by
    dsimp [a]
    field_simp
  rw [Algebra.smul_def,
    ← (algebraMap K (CliffordAlgebra Q)).map_mul, hscalar]
  exact eq_sub_iff_add_eq.mpr
    (CliffordAlgebra.ι_mul_ι_add_swap (Q := Q) x y)

/-- The scalar sign attached to a Clifford parity bit. -/
def paritySign (K : Type u) [Field K] (p : Bool) : K :=
  if p then -1 else 1

/-- A Clifford unit intertwines the vector generators with a quadratic
isometry, up to the sign dictated by a parity bit. -/
def Intertwines
    (Q : QuadraticForm K V)
    (c : (CliffordAlgebra Q)ˣ) (p : Bool)
    (h : Q.IsometryEquiv Q) : Prop :=
  ∀ y, (c : CliffordAlgebra Q) * CliffordAlgebra.ι Q y =
    paritySign K p •
      (CliffordAlgebra.ι Q (h y) * (c : CliffordAlgebra Q))

/-- Left multiplication by a vector unit composes the induced action with its
reflection and toggles the Clifford sign. -/
theorem Intertwines.vectorStep
    (Q : QuadraticForm K V)
    (c : (CliffordAlgebra Q)ˣ) (p : Bool)
    (h : Q.IsometryEquiv Q) (hc : Intertwines Q c p h)
    (x : V) (hx : Q x ≠ 0) :
    Intertwines Q (cliffordVectorUnit Q x hx * c) (!p)
      (h.trans (quadraticReflectionIsometry Q x hx)) := by
  intro y
  change
    (cliffordVectorUnit Q x hx : CliffordAlgebra Q) *
        (c : CliffordAlgebra Q) * CliffordAlgebra.ι Q y =
      paritySign K (!p) •
        (CliffordAlgebra.ι Q
            (quadraticReflection Q x hx (h y)) *
          ((cliffordVectorUnit Q x hx : CliffordAlgebra Q) *
            (c : CliffordAlgebra Q)))
  rw [mul_assoc, hc, mul_smul_comm, ← mul_assoc,
    cliffordVectorUnit_mul_iota]
  cases p <;> simp [paritySign, mul_assoc]

variable {ι : Type w} [Fintype ι]

/-- A partial reflection reduction of a normalizing Clifford unit.  The
`factor` is already in the Lipschitz group, while `action` fixes the basis
indices recorded in `s`. -/
structure ReflectionReductionState
    (Q : QuadraticForm K V) (b : ι → V)
    (u : (CliffordAlgebra Q)ˣ) (s : Finset ι) where
  factor : (CliffordAlgebra Q)ˣ
  action : Q.IsometryEquiv Q
  parity : Bool
  factor_mem : factor ∈ lipschitzGroup Q
  intertwines : Intertwines Q (factor * u) parity action
  fixes : ∀ i ∈ s, action (b i) = b i

/-- Apply one anisotropic reflection to a partial reduction state while
preserving its already-fixed basis indices. -/
def ReflectionReductionState.vectorStep
    {Q : QuadraticForm K V} {b : ι → V}
    {u : (CliffordAlgebra Q)ˣ} {s : Finset ι}
    (st : ReflectionReductionState Q b u s)
    (x : V) (hx : Q x ≠ 0)
    (hfix : ∀ i ∈ s,
      quadraticReflection Q x hx (st.action (b i)) =
        st.action (b i)) :
    ReflectionReductionState Q b u s where
  factor := cliffordVectorUnit Q x hx * st.factor
  action := st.action.trans (quadraticReflectionIsometry Q x hx)
  parity := !st.parity
  factor_mem := (lipschitzGroup Q).mul_mem
    (cliffordVectorUnit_mem_lipschitzGroup Q x hx)
    st.factor_mem
  intertwines := by
    simpa only [mul_assoc] using Intertwines.vectorStep Q
      (st.factor * u) st.parity st.action st.intertwines
      x hx
  fixes := by
    intro i hi
    exact (hfix i hi).trans (st.fixes i hi)

variable [Invertible (2 : K)]

/-- Successively reduce a quadratic isometry along an anisotropic orthogonal
basis.  The resulting Lipschitz factor leaves an induced action fixing every
basis vector.

At a basis vector `x`, the reduction uses reflection in `y - x` when that
vector is anisotropic.  In the remaining case, reflections in `y + x` and
then `x` perform the same reduction.  Invertibility of two guarantees that
`y + x` is anisotropic in the second branch. -/
theorem exists_fullReflectionReductionState
    (Q : QuadraticForm K V) (b : Module.Basis ι K V)
    (hbQ : ∀ i, Q (b i) ≠ 0)
    (hbOrtho : ∀ i j, i ≠ j →
      QuadraticMap.polar Q (b i) (b j) = 0)
    (u : (CliffordAlgebra Q)ˣ) (g : Q.IsometryEquiv Q)
    (hu : Intertwines Q u false g) :
    Nonempty (ReflectionReductionState Q b u Finset.univ) := by
  classical
  have build : ∀ s : Finset ι,
      Nonempty (ReflectionReductionState Q b u s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨{
          factor := 1
          action := g
          parity := false
          factor_mem := (lipschitzGroup Q).one_mem
          intertwines := by
            simpa [Intertwines, paritySign] using hu
          fixes := by simp }⟩
    | @insert i s hi ih =>
        rcases ih with ⟨st⟩
        let x : V := b i
        let y : V := st.action x
        have hQyx : Q y = Q x :=
          st.action.map_app x
        by_cases hdiff : Q (y - x) = 0
        · have htwo : (2 : K) ≠ 0 :=
            isUnit_iff_ne_zero.mp
              (isUnit_of_invertible (2 : K))
          have hfour : (4 : K) ≠ 0 := by
            convert mul_ne_zero htwo htwo using 1
            norm_num
          have hadd : Q (y + x) ≠ 0 := by
            rw [map_add_eq_four_mul Q hQyx hdiff]
            exact mul_ne_zero hfour (hbQ i)
          have hfixAdd : ∀ j ∈ s,
              quadraticReflection Q (y + x) hadd
                  (st.action (b j)) =
                st.action (b j) := by
            intro j hj
            apply quadraticReflection_eq_self_of_polar_eq_zero
            rw [st.fixes j hj]
            rw [QuadraticMap.polar_add_left]
            have hij : i ≠ j := by
              intro hij
              subst j
              exact hi hj
            have hyj :
                QuadraticMap.polar Q y (b j) = 0 := by
              rw [← st.fixes j hj]
              exact (isometry_polar Q st.action x (b j)).trans
                (hbOrtho i j hij)
            rw [hyj, hbOrtho i j hij, add_zero]
          let st₁ :=
            st.vectorStep (y + x) hadd hfixAdd
          have hfixX : ∀ j ∈ s,
              quadraticReflection Q x (hbQ i)
                  (st₁.action (b j)) =
                st₁.action (b j) := by
            intro j hj
            apply quadraticReflection_eq_self_of_polar_eq_zero
            rw [st₁.fixes j hj]
            have hij : i ≠ j := by
              intro hij
              subst j
              exact hi hj
            exact hbOrtho i j hij
          let st₂ :=
            st₁.vectorStep x (hbQ i) hfixX
          refine ⟨{
            st₂ with
            fixes := ?_ }⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with hji | hj
          · subst j
            change quadraticReflection Q x (hbQ i)
                (quadraticReflection Q (y + x) hadd y) = x
            rw [quadraticReflection_add_apply Q hQyx hdiff hadd]
            exact quadraticReflection_neg_self Q x (hbQ i)
          · exact st₂.fixes j hj
        · have hfixSub : ∀ j ∈ s,
              quadraticReflection Q (y - x) hdiff
                  (st.action (b j)) =
                st.action (b j) := by
            intro j hj
            apply quadraticReflection_eq_self_of_polar_eq_zero
            rw [st.fixes j hj]
            rw [QuadraticMap.polar_sub_left]
            have hij : i ≠ j := by
              intro hij
              subst j
              exact hi hj
            have hyj :
                QuadraticMap.polar Q y (b j) = 0 := by
              rw [← st.fixes j hj]
              exact (isometry_polar Q st.action x (b j)).trans
                (hbOrtho i j hij)
            rw [hyj, hbOrtho i j hij, sub_zero]
          let st' :=
            st.vectorStep (y - x) hdiff hfixSub
          refine ⟨{
            st' with
            fixes := ?_ }⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with hji | hj
          · subst j
            change quadraticReflection Q (y - x) hdiff y = x
            exact quadraticReflection_sub_apply Q hQyx hdiff
          · exact st'.fixes j hj
  exact build Finset.univ

end
end RiemannResearch.LinearAlgebra.QuadraticForm
