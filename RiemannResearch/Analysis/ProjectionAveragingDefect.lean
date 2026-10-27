/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A single averaging witness detects a projection residual

Source: independently derived continuation of the user-provided
PrimeResamplingResearch20261027.md, Sections 3 and 8. This is the abstract
Hilbert-space argument, rather than an assumption of arithmetic invariance.

If an averaging projection sends one legal witness to a nonzero scalar
multiple of the target, its commutator on that witness is exactly the same
multiple of the target residual. A signed pairing identity also supplies a
lower bound on the averaging defect of the residual.

Concrete RH consumer: prime-two averaging sends the legal atom g₂ to
(3/8) times the constant target. Its centered squared norm is 3/64, giving
the quantitative lower bound D₂(r) ≥ 3 ‖r‖⁴. The arithmetic realization of
the averaging projection is a separate application obligation.
-/

noncomputable section

namespace RiemannResearch.Analysis.ProjectionAveragingDefect

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (V W : Submodule ℝ H)
  [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]

/-- Exact commutator identity at a witness belonging to the legal subspace. -/
theorem commutator_witness (u h : H) (α : ℝ) (hh : h ∈ V)
    (havg : W.starProjection h = α • u) :
    W.starProjection (V.starProjection h) -
      V.starProjection (W.starProjection h) =
        α • (u - V.starProjection u) := by
  have hp : V.starProjection h = h :=
    Submodule.starProjection_eq_self_iff.mpr hh
  simp only [hp, havg, map_smul, smul_sub]

/-- The commutator detects the complete squared residual norm exactly. -/
theorem commutator_witness_energy (u h : H) (α : ℝ) (hh : h ∈ V)
    (havg : W.starProjection h = α • u) :
    ‖W.starProjection (V.starProjection h) -
      V.starProjection (W.starProjection h)‖ ^ 2 =
        α ^ 2 * ‖u - V.starProjection u‖ ^ 2 := by
  rw [commutator_witness V W u h α hh havg, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]

/-- The complete signed pairing before applying Cauchy--Schwarz. -/
theorem defect_pairing (u h : H) (α : ℝ) (hh : h ∈ V)
    (havg : W.starProjection h = α • u) :
    inner ℝ
      ((u - V.starProjection u) - W.starProjection (u - V.starProjection u))
      (h - W.starProjection h) = -α * ‖u - V.starProjection u‖ ^ 2 := by
  have hru : inner ℝ (u - V.starProjection u) u =
      ‖u - V.starProjection u‖ ^ 2 := by
    have hz := V.starProjection_inner_eq_zero u (V.starProjection u)
      (V.starProjection_apply_mem u)
    have he := real_inner_self_eq_norm_sq (u - V.starProjection u)
    rw [inner_sub_right, hz, sub_zero] at he
    exact he
  have hrh : inner ℝ (u - V.starProjection u) h = 0 :=
    V.starProjection_inner_eq_zero u h hh
  have hw : inner ℝ (W.starProjection (u - V.starProjection u))
      (h - W.starProjection h) = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (W.starProjection_apply_mem (u - V.starProjection u))
      (Submodule.sub_starProjection_mem_orthogonal (K := W) h)
  rw [inner_sub_left, hw, sub_zero, inner_sub_right, havg,
    real_inner_smul_right, hrh, hru]
  ring

/-- Cauchy--Schwarz converts the signed identity into a residual-energy bound. -/
theorem defect_energy_bound (u h : H) (α : ℝ) (hh : h ∈ V)
    (havg : W.starProjection h = α • u) :
    α ^ 2 * (‖u - V.starProjection u‖ ^ 2) ^ 2 ≤
      ‖(u - V.starProjection u) - W.starProjection (u - V.starProjection u)‖ ^ 2 *
        ‖h - W.starProjection h‖ ^ 2 := by
  have hcs := (sq_le_sq₀ (norm_nonneg
      (inner ℝ
        ((u - V.starProjection u) - W.starProjection (u - V.starProjection u))
        (h - W.starProjection h)))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (norm_inner_le_norm
      ((u - V.starProjection u) - W.starProjection (u - V.starProjection u))
      (h - W.starProjection h))
  rw [defect_pairing V W u h α hh havg] at hcs
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow, neg_sq] using hcs

/-- Invariance under this one averaging projection is already exact target
membership. No invariance of the entire legal subspace is assumed. -/
theorem defect_zero_iff_target_mem (u h : H) (α : ℝ) (hα : α ≠ 0)
    (hh : h ∈ V) (havg : W.starProjection h = α • u) :
    (u - V.starProjection u) - W.starProjection (u - V.starProjection u) = 0 ↔
      u ∈ V := by
  constructor
  · intro hz
    have he := defect_pairing V W u h α hh havg
    rw [hz, inner_zero_left] at he
    have hm : α * ‖u - V.starProjection u‖ ^ 2 = 0 := by
      linarith only [he]
    have hn : ‖u - V.starProjection u‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hm).resolve_left hα
    have hr : u - V.starProjection u = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  · intro hu
    have hp : V.starProjection u = u :=
      Submodule.starProjection_eq_self_iff.mpr hu
    simp only [hp, sub_self, map_zero]

/-- Vanishing of the commutator on a single witness is equivalent to target
membership. This does not assert that the two projections commute. -/
theorem commutator_zero_iff_target_mem (u h : H) (α : ℝ) (hα : α ≠ 0)
    (hh : h ∈ V) (havg : W.starProjection h = α • u) :
    W.starProjection (V.starProjection h) -
      V.starProjection (W.starProjection h) = 0 ↔ u ∈ V := by
  rw [commutator_witness V W u h α hh havg]
  constructor
  · intro hz
    have hr : u - V.starProjection u = 0 :=
      (smul_eq_zero.mp hz).resolve_left hα
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  · intro hu
    have hp : V.starProjection u = u :=
      Submodule.starProjection_eq_self_iff.mpr hu
    simp only [hp, sub_self, smul_zero]

/-- Numerical specialization needed for geometric prime-two averaging. The
two averaging identities are explicit hypotheses, not hidden providers. -/
theorem parity_defect_energy_bound (u h : H) (hh : h ∈ V)
    (havg : W.starProjection h = (3 / 8 : ℝ) • u)
    (henergy : ‖h - W.starProjection h‖ ^ 2 = (3 / 64 : ℝ)) :
    3 * (‖u - V.starProjection u‖ ^ 2) ^ 2 ≤
      ‖(u - V.starProjection u) - W.starProjection (u - V.starProjection u)‖ ^ 2 := by
  have he := defect_energy_bound V W u h (3 / 8) hh havg
  rw [henergy] at he
  nlinarith only [he]

/-- The dyadic averaging defect has an exact nonnegative remainder.
The two numerical averaging identities are explicit premises here. -/
theorem parity_defect_energy_exact (u h : H) (hh : h ∈ V)
    (havg : W.starProjection h = (3 / 8 : ℝ) • u)
    (henergy : ‖h - W.starProjection h‖ ^ 2 = (3 / 64 : ℝ)) :
    ‖(u - V.starProjection u) - W.starProjection (u - V.starProjection u)‖ ^ 2 =
      3 * (‖u - V.starProjection u‖ ^ 2) ^ 2 +
        ‖((u - V.starProjection u) - W.starProjection (u - V.starProjection u)) +
          (8 * ‖u - V.starProjection u‖ ^ 2) • (h - W.starProjection h)‖ ^ 2 := by
  let r := u - V.starProjection u
  let d := r - W.starProjection r
  let z := h - W.starProjection h
  let e : ℝ := ‖r‖ ^ 2
  have hp : inner ℝ d z = -(3 / 8 : ℝ) * e :=
    defect_pairing V W u h (3 / 8) hh havg
  have hp' : inner ℝ z d = -(3 / 8 : ℝ) * e :=
    (real_inner_comm z d).symm.trans hp
  have hz : ‖z‖ ^ 2 = (3 / 64 : ℝ) := henergy
  have hexpand := real_inner_self_eq_norm_sq (d + (8 * e) • z)
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, hp, hp', hz] at hexpand
  change ‖d‖ ^ 2 = 3 * e ^ 2 + ‖d + (8 * e) • z‖ ^ 2
  nlinarith only [hexpand]

/-- Equality in the sharp dyadic defect bound means precisely that its
explicit residual remainder vanishes. -/
theorem parity_defect_energy_eq_iff (u h : H) (hh : h ∈ V)
    (havg : W.starProjection h = (3 / 8 : ℝ) • u)
    (henergy : ‖h - W.starProjection h‖ ^ 2 = (3 / 64 : ℝ)) :
    ‖(u - V.starProjection u) - W.starProjection (u - V.starProjection u)‖ ^ 2 =
        3 * (‖u - V.starProjection u‖ ^ 2) ^ 2 ↔
      ((u - V.starProjection u) - W.starProjection (u - V.starProjection u)) +
        (8 * ‖u - V.starProjection u‖ ^ 2) • (h - W.starProjection h) = 0 := by
  have he := parity_defect_energy_exact V W u h hh havg henergy
  constructor
  · intro hd
    have hz :
        ‖((u - V.starProjection u) - W.starProjection (u - V.starProjection u)) +
          (8 * ‖u - V.starProjection u‖ ^ 2) • (h - W.starProjection h)‖ ^ 2 = 0 := by
      linarith only [he, hd]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro hz
    simpa only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using he

/-- With a unit target fixed by the averaging projection, the complete
residual norm has two explicit nonnegative remainder energies. -/
theorem parity_residual_energy_exact (u h : H) (hu : ‖u‖ ^ 2 = 1)
    (huW : u ∈ W) (hh : h ∈ V)
    (havg : W.starProjection h = (3 / 8 : ℝ) • u)
    (henergy : ‖h - W.starProjection h‖ ^ 2 = (3 / 64 : ℝ)) :
    ‖u - V.starProjection u‖ ^ 2 =
      4 * (‖u - V.starProjection u‖ ^ 2) ^ 2 +
        ‖((u - V.starProjection u) - W.starProjection (u - V.starProjection u)) +
          (8 * ‖u - V.starProjection u‖ ^ 2) • (h - W.starProjection h)‖ ^ 2 +
        ‖W.starProjection (u - V.starProjection u) -
          (‖u - V.starProjection u‖ ^ 2) • u‖ ^ 2 := by
  let r := u - V.starProjection u
  let d := r - W.starProjection r
  let z := h - W.starProjection h
  let e : ℝ := ‖r‖ ^ 2
  have hru : inner ℝ r u = e := by
    have hz := V.starProjection_inner_eq_zero u (V.starProjection u)
      (V.starProjection_apply_mem u)
    have he := real_inner_self_eq_norm_sq (u - V.starProjection u)
    rw [inner_sub_right, hz, sub_zero] at he
    exact he
  have hWu : W.starProjection u = u :=
    Submodule.starProjection_eq_self_iff.mpr huW
  have hcru : inner ℝ (W.starProjection r) u = e := by
    rw [W.inner_starProjection_left_eq_right, hWu]
    exact hru
  have hucr : inner ℝ u (W.starProjection r) = e :=
    (real_inner_comm u (W.starProjection r)).symm.trans hcru
  have hcenter := real_inner_self_eq_norm_sq (W.starProjection r - e • u)
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, hcru, hucr, hu] at hcenter
  have hsplit : e = ‖W.starProjection r‖ ^ 2 + ‖d‖ ^ 2 := by
    simpa only [e, d, Submodule.starProjection_orthogonal_val] using
      Submodule.norm_sq_eq_add_norm_sq_starProjection r W
  have hdefect : ‖d‖ ^ 2 = 3 * e ^ 2 + ‖d + (8 * e) • z‖ ^ 2 :=
    parity_defect_energy_exact V W u h hh havg henergy
  change e = 4 * e ^ 2 + ‖d + (8 * e) • z‖ ^ 2 +
    ‖W.starProjection r - e • u‖ ^ 2
  nlinarith only [hsplit, hcenter, hdefect]

end RiemannResearch.Analysis.ProjectionAveragingDefect
