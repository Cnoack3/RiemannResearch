/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact changes of signed Hermitian forms under channel subtraction

Source: user-provided argument, `signed_gain_agent.md`, Sections 1--7, and
`RH_Exact_Arithmetic_Channel_Effects_2026-09-07.md`, Section 4. These sources
support the statements and completion-of-square proof strategy. The RH
consumer is the accounting of signed arithmetic channel effects. No
arithmetic identification, positivity provider, or RH implication is assumed.

The form is a genuine complex sesquilinear map, conjugate linear in the first
argument. It need not be bounded or positive. Signed normal equations are
explicitly distinguished from Hilbert normal equations.
-/

open scoped BigOperators ComplexConjugate

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Real diagonal value of a complex sesquilinear form. -/
noncomputable def signedValue (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (x : V) : ℝ :=
  (B x x).re

theorem signedValue_sum {ι : Type*} (s : Finset ι)
    (F : ι → V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (x : V) :
    (∑ i ∈ s, F i).signedValue x = ∑ i ∈ s, (F i).signedValue x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [signedValue]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      change (F i).signedValue x + (∑ j ∈ s, F j).signedValue x = _
      rw [ih]

variable {E : Type*} [AddCommGroup E] [Module ℂ E]
variable {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}

theorem signedValue_smul (c : ℂ) (x : V) :
    B.signedValue (c • x) = Complex.normSq c * B.signedValue x := by
  simp only [signedValue, map_smulₛₗ, LinearMap.smul_apply,
    RingHom.id_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring


/-- Expansion of a finite synthesis, including every signed matrix entry. -/
theorem signedValue_synthesis {ι : Type*} (s : Finset ι)
    (z : ι → V) (a : ι → ℂ) :
    B.signedValue (∑ i ∈ s, a i • z i) =
      (∑ i ∈ s, ∑ j ∈ s, conj (a i) * B (z i) (z j) * a j).re := by
  simp only [signedValue, map_sum, LinearMap.sum_apply, map_smulₛₗ,
    LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring


/-- Synthesis redundancy is harmless for the actual signed value. -/
theorem signed_synthesis_kernel (Z : E →ₗ[ℂ] V) (r : V) (a v : E)
    (hv : Z v = 0) :
    B.signedValue (r - Z (a + v)) = B.signedValue (r - Z a) := by
  simp [hv]


/-- The signed normal equation eliminates the signed residual coupling. -/
theorem signed_normal_orthogonal (Z : E →ₗ[ℂ] V) (r : V) (a₀ : E)
    (hn : ∀ a, B (Z a) (Z a₀) = B (Z a) r) (a : E) :
    B (Z a) (r - Z a₀) = 0 := by
  simp [hn a]


private theorem linear_nonnegative_forall (A C : ℝ)
    (h : ∀ t : ℝ, 0 ≤ A + t * C) : C = 0 := by
  by_contra hc
  have hh := h (-(A + 1) / C)
  have heq : A + (-(A + 1) / C) * C = -1 := by
    field_simp [hc]
    ring
  rw [heq] at hh
  norm_num at hh


namespace IsSymm

variable (hB : B.IsSymm)

include hB

theorem signed_re_symm (x y : V) : (B x y).re = (B y x).re := by
  rw [← hB.eq x y, Complex.conj_re]

/-- Hermitian diagonal values really are real. -/
theorem signed_diagonal_im (x : V) : (B x x).im = 0 := by
  have h := congrArg Complex.im (hB.eq x x)
  simp only [Complex.conj_im] at h
  linarith

theorem signedValue_add (x y : V) :
    B.signedValue (x + y) = B.signedValue x + B.signedValue y +
      2 * (B x y).re := by
  simp only [signedValue, map_add, LinearMap.add_apply, Complex.add_re]
  rw [hB.signed_re_symm y x]
  ring

theorem signedValue_sub (x y : V) :
    B.signedValue (x - y) = B.signedValue x + B.signedValue y -
      2 * (B y x).re := by
  simp only [signedValue, map_sub, LinearMap.sub_apply, Complex.sub_re]
  rw [hB.signed_re_symm x y]
  ring

/-- Exact signed change; the coupling uses the signed form. -/
theorem signed_change (r g : V) :
    B.signedValue (r - g) - B.signedValue r =
      B.signedValue g - 2 * (B g r).re := by
  rw [hB.signedValue_sub]
  ring

/-- The equivalent residual formula preserves the signed mixed term. -/
theorem signed_gain (e g : V) :
    B.signedValue (e + g) - B.signedValue e =
      B.signedValue g + 2 * (B e g).re := by
  rw [hB.signedValue_add]
  ring

theorem signed_monotone_iff (r g : V) :
    B.signedValue (r - g) ≤ B.signedValue r ↔
      B.signedValue g ≤ 2 * (B g r).re := by
  rw [hB.signedValue_sub]
  constructor <;> intro h <;> linarith



/-- Exact matrix-and-coupling formula for arbitrary finite coefficients. -/
theorem signed_change_synthesis {ι : Type*} (s : Finset ι)
    (z : ι → V) (a : ι → ℂ) (r : V) :
    B.signedValue (r - ∑ i ∈ s, a i • z i) - B.signedValue r =
      (∑ i ∈ s, ∑ j ∈ s, conj (a i) * B (z i) (z j) * a j).re -
        2 * (∑ i ∈ s, conj (a i) * B (z i) r).re := by
  rw [hB.signed_change, signedValue_synthesis]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul]

/-- Full finite accounting: the double sum includes the diagonal and both
orientations of each mixed term, and the final sum couples the residual. -/
theorem signed_gain_sum {ι : Type*} (s : Finset ι) (e : V) (g : ι → V) :
    B.signedValue (e + ∑ i ∈ s, g i) - B.signedValue e =
      (∑ i ∈ s, ∑ j ∈ s, B (g i) (g j)).re +
        2 * (∑ i ∈ s, B e (g i)).re := by
  rw [hB.signed_gain]
  simp only [signedValue, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]

/-- Exact completion of the signed quadratic around any solution of the
signed normal equation. Neither invertibility nor positivity is needed. -/
theorem signed_complete_square (Z : E →ₗ[ℂ] V) (r : V) (a₀ : E)
    (hn : ∀ a, B (Z a) (Z a₀) = B (Z a) r) (a : E) :
    B.signedValue (r - Z a) =
      B.signedValue r - B.signedValue (Z a₀) +
        B.signedValue (Z (a - a₀)) := by
  rw [Z.map_sub, hB.signedValue_sub, hB.signedValue_sub]
  have hc := congrArg Complex.re (hn a)
  rw [hB.signed_re_symm (Z a₀) (Z a)]
  linarith

/-- Positivity on the channel range makes the normal solution a minimizer. -/
theorem signed_minimum (Z : E →ₗ[ℂ] V) (r : V) (a₀ : E)
    (hn : ∀ a, B (Z a) (Z a₀) = B (Z a) r)
    (hpos : ∀ a, 0 ≤ B.signedValue (Z a)) (a : E) :
    B.signedValue r - B.signedValue (Z a₀) ≤ B.signedValue (r - Z a) := by
  rw [hB.signed_complete_square Z r a₀ hn a]
  exact le_add_of_nonneg_right (hpos (a - a₀))

theorem signed_minimum_attained (Z : E →ₗ[ℂ] V) (r : V) (a₀ : E)
    (hn : ∀ a, B (Z a) (Z a₀) = B (Z a) r) :
    B.signedValue (r - Z a₀) = B.signedValue r - B.signedValue (Z a₀) := by
  rw [hB.signed_complete_square Z r a₀ hn a₀]
  simp [signedValue]

/-- Triangular elimination gives the augmented signed quadratic exactly. -/
theorem signed_augmented_square (Z : E →ₗ[ℂ] V) (r : V) (a₀ : E)
    (hn : ∀ a, B (Z a) (Z a₀) = B (Z a) r) (t : ℂ) (a : E) :
    B.signedValue (t • r + Z a) =
      Complex.normSq t * (B.signedValue r - B.signedValue (Z a₀)) +
        B.signedValue (Z (a + t • a₀)) := by
  have heq : t • r + Z a = t • (r - Z a₀) + Z (a + t • a₀) := by
    simp [smul_sub, map_add, map_smul]
  rw [heq, hB.signedValue_add, signedValue_smul,
    hB.signed_minimum_attained Z r a₀ hn]
  have hz : B (r - Z a₀) (Z (a + t • a₀)) = 0 := by
    rw [← hB.eq]
    rw [signed_normal_orthogonal Z r a₀ hn]
    simp
  rw [map_smulₛₗ, LinearMap.smul_apply, hz]
  simp

/-- Schur positivity on the augmented channel span, valid for singular
synthesis as soon as the signed normal equation has a solution. -/
theorem signed_schur_nonnegative_iff (Z : E →ₗ[ℂ] V) (r : V) (a₀ : E)
    (hn : ∀ a, B (Z a) (Z a₀) = B (Z a) r) :
    (∀ t : ℂ, ∀ a, 0 ≤ B.signedValue (t • r + Z a)) ↔
      (∀ a, 0 ≤ B.signedValue (Z a)) ∧
        0 ≤ B.signedValue r - B.signedValue (Z a₀) := by
  constructor
  · intro h
    constructor
    · intro a
      simpa using h 0 a
    · have hh := h 1 (-a₀)
      rw [hB.signed_augmented_square Z r a₀ hn] at hh
      simpa [signedValue] using hh
  · rintro ⟨hpos, hschur⟩ t a
    rw [hB.signed_augmented_square Z r a₀ hn]
    exact add_nonneg (mul_nonneg (Complex.normSq_nonneg t) hschur) (hpos _)


/-- Universal channel monotonicity is equivalent to positivity on the
channel subspace and vanishing of every signed mixed coupling. The second
space may be the Hilbert orthogonal complement of the first. -/
theorem signed_universal_monotone_iff (S T : Submodule ℂ V) :
    (∀ s ∈ S, ∀ e ∈ T, B.signedValue e ≤ B.signedValue (e + s)) ↔
      (∀ s ∈ S, 0 ≤ B.signedValue s) ∧
        (∀ s ∈ S, ∀ e ∈ T, B e s = 0) := by
  constructor
  · intro h
    have hp : ∀ s ∈ S, 0 ≤ B.signedValue s := by
      intro s hs
      simpa [signedValue] using h s hs 0 T.zero_mem
    have hre : ∀ s ∈ S, ∀ e ∈ T, (B e s).re = 0 := by
      intro s hs e he
      have hh : ∀ t : ℝ, 0 ≤ B.signedValue s + t * (2 * (B e s).re) := by
        intro t
        have hm := h s hs ((t : ℂ) • e) (T.smul_mem (t : ℂ) he)
        rw [hB.signedValue_add] at hm
        simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
          Complex.mul_re, Complex.conj_re, Complex.conj_im,
          Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul,
          sub_zero] at hm
        nlinarith
      have hz := linear_nonnegative_forall (B.signedValue s) (2 * (B e s).re) hh
      linarith
    refine ⟨hp, ?_⟩
    intro s hs e he
    apply Complex.ext
    · simpa using hre s hs e he
    · have hi := hre (Complex.I • s) (S.smul_mem Complex.I hs) e he
      simpa [map_smul, Complex.mul_re] using hi
  · rintro ⟨hp, hz⟩ s hs e he
    rw [hB.signedValue_add, hz s hs e he]
    simp only [Complex.zero_re, mul_zero, add_zero]
    exact le_add_of_nonneg_right (hp s hs)

private theorem signed_null_re_of_nonnegative (r z : V)
    (hz : B.signedValue z = 0)
    (hpos : ∀ t : ℂ, 0 ≤ B.signedValue (r + t • z)) :
    (B r z).re = 0 := by
  have hh : ∀ t : ℝ, 0 ≤ B.signedValue r + t * (2 * (B r z).re) := by
    intro t
    have h := hpos (t : ℂ)
    rw [hB.signedValue_add, signedValue_smul, hz, mul_zero, add_zero] at h
    simp only [map_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
    nlinarith
  have hn := linear_nonnegative_forall (B.signedValue r) (2 * (B r z).re) hh
  linarith

/-- A signed-null channel coupled to the residual obstructs positivity of
the augmented span, even when its Hilbert norm is nonzero. -/
theorem signed_null_coupling_of_nonnegative (r z : V)
    (hz : B.signedValue z = 0)
    (hpos : ∀ t : ℂ, 0 ≤ B.signedValue (r + t • z)) : B r z = 0 := by
  have hre := hB.signed_null_re_of_nonnegative r z hz hpos
  have hzi : B.signedValue (Complex.I • z) = 0 := by
    rw [signedValue_smul, hz, mul_zero]
  have hposi : ∀ t : ℂ, 0 ≤ B.signedValue (r + t • (Complex.I • z)) := by
    intro t
    simpa [smul_smul] using hpos (t * Complex.I)
  have him := hB.signed_null_re_of_nonnegative r (Complex.I • z) hzi hposi
  apply Complex.ext
  · simpa using hre
  · simpa [map_smul, Complex.mul_re] using him

theorem signed_null_coupling_negative_witness (r z : V)
    (hz : B.signedValue z = 0) (hc : B r z ≠ 0) :
    ∃ t : ℂ, B.signedValue (r + t • z) < 0 := by
  by_contra! h
  exact hc (hB.signed_null_coupling_of_nonnegative r z hz h)

/-- Equality with the signed minimum is precisely the signed normal equation,
including the singular case. Hilbert normal equations are a separate condition. -/
theorem signed_minimum_eq_iff_normal (Z : E →ₗ[ℂ] V) (r : V) (a₀ : E)
    (hn : ∀ a, B (Z a) (Z a₀) = B (Z a) r)
    (hpos : ∀ a, 0 ≤ B.signedValue (Z a)) (a : E) :
    B.signedValue (r - Z a) = B.signedValue r - B.signedValue (Z a₀) ↔
      ∀ b, B (Z b) (Z a) = B (Z b) r := by
  constructor
  · intro ha b
    have hd : B.signedValue (Z (a - a₀)) = 0 := by
      have hc := hB.signed_complete_square Z r a₀ hn a
      linarith
    have hall : ∀ t : ℂ, 0 ≤ B.signedValue (Z b + t • Z (a - a₀)) := by
      intro t
      simpa only [map_add, map_smul] using hpos (b + t • (a - a₀))
    have hc := hB.signed_null_coupling_of_nonnegative (Z b) (Z (a - a₀)) hd hall
    rw [map_sub, map_sub, sub_eq_zero] at hc
    exact hc.trans (hn b)
  · intro ha
    have h₀ := hB.signed_minimum Z r a₀ hn hpos a
    have h₁ := hB.signed_minimum Z r a ha hpos a₀
    have he₀ := hB.signed_minimum_attained Z r a₀ hn
    have he₁ := hB.signed_minimum_attained Z r a ha
    linarith

end IsSymm

/-- Finite signed sector accounting keeps each sector's quadratic and mixed
terms. An infinite arithmetic decomposition would require separate convergence. -/
theorem signed_change_sum_forms {ι : Type*} (s : Finset ι)
    (F : ι → V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hF : ∀ i ∈ s, (F i).IsSymm) (r g : V) :
    (∑ i ∈ s, F i).signedValue (r - g) - (∑ i ∈ s, F i).signedValue r =
      ∑ i ∈ s, ((F i).signedValue g - 2 * (F i g r).re) := by
  rw [signedValue_sum, signedValue_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i hi => (hF i hi).signed_change r g)

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The positive Hilbert gain and the signed change in one statement. Only
the Hilbert identity loses its mixed term under Hilbert orthogonality. -/
theorem signed_hilbert_projection_accounting
    (B : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ) (hB : B.IsSymm) (r g : H)
    (horth : inner ℂ (r - g) g = 0) :
    (‖r‖ ^ 2 - ‖r - g‖ ^ 2 = ‖g‖ ^ 2) ∧
      (B.signedValue r - B.signedValue (r - g) =
        B.signedValue g + 2 * (B (r - g) g).re) := by
  constructor
  · have hn := norm_add_sq (𝕜 := ℂ) (r - g) g
    simp only [sub_add_cancel, horth, map_zero, mul_zero, add_zero] at hn
    linarith
  · simpa only [sub_add_cancel] using hB.signed_gain (r - g) g

/-- A real multiple of the Hilbert form is a genuine Hermitian form. -/
theorem real_smul_inner_isSymm (c : ℝ) :
    ((c : ℂ) • (innerₛₗ ℂ : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ)).IsSymm := by
  constructor
  intro x y
  simp only [LinearMap.smul_apply, smul_eq_mul, innerₛₗ_apply_apply,
    map_mul, Complex.conj_ofReal, inner_conj_symm]

theorem real_smul_inner_signedValue (c : ℝ) (x : H) :
    ((c : ℂ) • (innerₛₗ ℂ : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ)).signedValue x =
      c * ‖x‖ ^ 2 := by
  simp [signedValue, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- Keeping the Hilbert data fixed, real multiples of the Hilbert form
produce signed gains with either sign. -/
theorem real_smul_inner_signed_gain (c : ℝ) (r g : H)
    (horth : inner ℂ (r - g) g = 0) :
    ((c : ℂ) • (innerₛₗ ℂ : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ)).signedValue r -
      ((c : ℂ) • (innerₛₗ ℂ : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ)).signedValue (r - g) =
        c * ‖g‖ ^ 2 := by
  have hn := (signed_hilbert_projection_accounting
    ((c : ℂ) • innerₛₗ ℂ) (real_smul_inner_isSymm c) r g horth).1
  rw [real_smul_inner_signedValue, real_smul_inner_signedValue, ← mul_sub, hn]

/-- A projected extra channel already in the old span is zero: the old
residual is Hilbert orthogonal to that span, and so is the new residual to
the removed vector. Consequently its signed change is exactly zero for
every sesquilinear form, with no positivity assumption on that form. -/
theorem signed_no_gain_of_existing_span
    (B : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ) (S : Submodule ℂ H) (r g : H)
    (hg : g ∈ S) (hr : ∀ x ∈ S, inner ℂ r x = 0)
    (hproj : inner ℂ (r - g) g = 0) :
    g = 0 ∧ B.signedValue (r - g) = B.signedValue r := by
  have hrg := hr g hg
  rw [inner_sub_left, hrg, zero_sub, neg_eq_zero] at hproj
  have hz : g = 0 := inner_self_eq_zero.mp hproj
  exact ⟨hz, by simp [hz]⟩

end Hilbert
end LinearMap
