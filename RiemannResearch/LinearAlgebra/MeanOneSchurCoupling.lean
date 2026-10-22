/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.MeanOneBlockSchur
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Signed Schur coupling and its exact source-limit consequence

The finite mixed increment is retained before applying Cauchy--Schwarz.
Positive complete inverse-Schur forms imply `(Delta B)^2 <= Delta A*Delta C`.
The scalar source limits are explicit hypotheses; their realization by the
arithmetic packet sources is not proved here.
The resulting limit bound is algebraically the old projection bound `4*pi/Q`;
it does not prove saturation or supply a new unconditional RH provider.

Source: user-directed continuation of PhysicalMeanOneAdvance20261008.md;
finite Schur algebra and the abstract sharpness model are developed here.
-/

noncomputable section
open Matrix Filter
open scoped Topology
namespace RiemannResearch.LinearAlgebra.MeanOneSchurCoupling
open MeanOneBlockSchur

section Finite
variable {κ : Type*} [Fintype κ]

/-- Cauchy--Schwarz for the full positive inverse-Schur form; the mixed
pairing remains signed in the hypotheses and in the quadratic expansion. -/
theorem source_pair_cauchy (Z : Matrix κ κ ℝ) (u v : κ → ℝ)
    (hZsym : Zᵀ = Z) (hZpos : ∀ w : κ → ℝ, 0 ≤ w ⬝ᵥ (Z *ᵥ w)) :
    (u ⬝ᵥ (Z *ᵥ v)) ^ 2 ≤
      (u ⬝ᵥ (Z *ᵥ u)) * (v ⬝ᵥ (Z *ᵥ v)) := by
  have hpair : v ⬝ᵥ (Z *ᵥ u) = u ⬝ᵥ (Z *ᵥ v) := by
    simpa only [hZsym] using Matrix.dotProduct_transpose_mulVec Z v u
  have hexpand (t : ℝ) :
      (t • u + v) ⬝ᵥ (Z *ᵥ (t • u + v)) =
        (u ⬝ᵥ (Z *ᵥ u)) * (t * t) +
          (2 * (u ⬝ᵥ (Z *ᵥ v))) * t + v ⬝ᵥ (Z *ᵥ v) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [hpair]
    ring
  have hquad (t : ℝ) : 0 ≤
      (u ⬝ᵥ (Z *ᵥ u)) * (t * t) +
        (2 * (u ⬝ᵥ (Z *ᵥ v))) * t + v ⬝ᵥ (Z *ᵥ v) := by
    rw [← hexpand]
    exact hZpos _
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

theorem cauchy_of_coupled_updates (Z : Matrix κ κ ℝ) (u v : κ → ℝ)
    (A Anew B Bnew C Cnew : ℝ)
    (hZsym : Zᵀ = Z) (hZpos : ∀ w : κ → ℝ, 0 ≤ w ⬝ᵥ (Z *ᵥ w))
    (hA : Anew = A + u ⬝ᵥ (Z *ᵥ u))
    (hB : Bnew = B + u ⬝ᵥ (Z *ᵥ v))
    (hC : Cnew = C + v ⬝ᵥ (Z *ᵥ v)) :
    (Bnew - B) ^ 2 ≤ (Anew - A) * (Cnew - C) := by
  rw [hA, hB, hC]
  simpa only [add_sub_cancel_left] using source_pair_cauchy Z u v hZsym hZpos

/-- The inequality is sharp even for positive forms: collinear sources give
exact equality. Consequently the constant cannot be improved abstractly. -/
theorem source_pair_cauchy_sharp_on_line (Z : Matrix κ κ ℝ)
    (v : κ → ℝ) (t : ℝ) :
    ((t • v) ⬝ᵥ (Z *ᵥ v)) ^ 2 =
      ((t • v) ⬝ᵥ (Z *ᵥ (t • v))) * (v ⬝ᵥ (Z *ᵥ v)) := by
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

end Finite

section Block
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Specialization to the actual solved block equations, rather than an
assumed scalar update. Positivity of the complete inverse-Schur form is
the sole order premise beyond the exact algebraic block hypotheses. -/
theorem solved_block_coupling_cauchy
    (F R : Matrix ι ι ℝ) (J : Matrix ι κ ℝ)
    (K S Z : Matrix κ κ ℝ)
    (lam phi xLam xPhi : ι → ℝ) (lamNew phiNew yLam yPhi : κ → ℝ)
    (hRF : R * F = 1) (hR : Rᵀ = R)
    (hS : S = schurMatrix R J K) (hZS : Z * S = 1)
    (hZsym : Zᵀ = Z) (hZpos : ∀ w : κ → ℝ, 0 ≤ w ⬝ᵥ (Z *ᵥ w))
    (hLamOld : F *ᵥ xLam + J *ᵥ yLam = lam)
    (hLamNew : Jᵀ *ᵥ xLam + K *ᵥ yLam = lamNew)
    (hPhiOld : F *ᵥ xPhi + J *ᵥ yPhi = phi)
    (hPhiNew : Jᵀ *ᵥ xPhi + K *ᵥ yPhi = phiNew) :
    ((lam ⬝ᵥ xPhi + lamNew ⬝ᵥ yPhi) - lam ⬝ᵥ (R *ᵥ phi)) ^ 2 ≤
      ((lam ⬝ᵥ xLam + lamNew ⬝ᵥ yLam) - lam ⬝ᵥ (R *ᵥ lam)) *
        ((phi ⬝ᵥ xPhi + phiNew ⬝ᵥ yPhi) - phi ⬝ᵥ (R *ᵥ phi)) := by
  obtain ⟨hA, hB, hC⟩ := coupled_source_updates F R J K S Z
    lam phi xLam xPhi lamNew phiNew yLam yPhi hRF hR hS hZS
    hLamOld hLamNew hPhiOld hPhiNew
  rw [hA, hB, hC]
  simpa only [add_sub_cancel_left] using
    source_pair_cauchy Z (screenedSource R J lam lamNew)
      (screenedSource R J phi phiNew) hZsym hZpos

end Block

/-- Passing the complete finite signed coupling to its source limits, without
division and therefore without silently assuming a positive old charge. -/
theorem limiting_coupling_of_source_limits
    (p Cinf : ℝ) (A B C : ℕ → ℝ) (n : ℕ)
    (hA : Tendsto A atTop (𝓝 0))
    (hB : Tendsto B atTop (𝓝 (-2 * p)))
    (hC : Tendsto C atTop (𝓝 Cinf))
    (hpair : ∀ m : ℕ, n ≤ m →
      (B m - B n) ^ 2 ≤ (A m - A n) * (C m - C n)) :
    (2 * p + B n) ^ 2 ≤ (-A n) * (Cinf - C n) := by
  have hlim : Tendsto
      (fun m => (B m - B n) ^ 2 - (A m - A n) * (C m - C n))
      atTop (𝓝 ((-2 * p - B n) ^ 2 - (0 - A n) * (Cinf - C n))) :=
    ((hB.sub tendsto_const_nhds).pow 2).sub
      ((hA.sub tendsto_const_nhds).mul (hC.sub tendsto_const_nhds))
  have hle : (-2 * p - B n) ^ 2 - (0 - A n) * (Cinf - C n) ≤ 0 :=
    le_of_tendsto hlim (eventually_atTop.2 ⟨n, fun m hnm => sub_nonpos.mpr (hpair m hnm)⟩)
  nlinarith only [hle]

/-- The zero-charge case forces zero limiting mismatch; no undefined quotient
is introduced at this endpoint. -/
theorem zero_charge_forces_zero_mismatch
    (p Cinf : ℝ) (A B C : ℕ → ℝ) (n : ℕ)
    (hA : Tendsto A atTop (𝓝 0))
    (hB : Tendsto B atTop (𝓝 (-2 * p)))
    (hC : Tendsto C atTop (𝓝 Cinf))
    (hpair : ∀ m : ℕ, n ≤ m →
      (B m - B n) ^ 2 ≤ (A m - A n) * (C m - C n))
    (hzero : A n = 0) : 2 * p + B n = 0 := by
  have h := limiting_coupling_of_source_limits p Cinf A B C n hA hB hC hpair
  rw [hzero] at h
  nlinarith only [h, sq_nonneg (2 * p + B n)]

/-- Source-limit bound with its essential positive denominator stated. This
bound alone does not identify the saturation endpoint. -/
theorem gamma_limit_bound_of_source_limits
    (p Cinf : ℝ) (A B C : ℕ → ℝ) (n : ℕ)
    (hA : Tendsto A atTop (𝓝 0))
    (hB : Tendsto B atTop (𝓝 (-2 * p)))
    (hC : Tendsto C atTop (𝓝 Cinf))
    (hpair : ∀ m : ℕ, n ≤ m →
      (B m - B n) ^ 2 ≤ (A m - A n) * (C m - C n))
    (halpha : 0 < -A n) :
    -Cinf ≤ -C n - (2 * p + B n) ^ 2 / (-A n) := by
  have h := limiting_coupling_of_source_limits p Cinf A B C n hA hB hC hpair
  have hquot : (2 * p + B n) ^ 2 / (-A n) ≤ Cinf - C n :=
    (div_le_iff₀ halpha).2 (by simpa only [mul_comm] using h)
  linarith only [hquot]

/-- Under the exact residual projection formula, the corrected charge equals
the existing projection bound. No independent arithmetic improvement is hidden
in this reparameterization. -/
theorem correctedCharge_eq_projectionBound (p alpha gamma D Q : ℝ)
    (hp : p ≠ 0) (halpha : alpha ≠ 0)
    (hT : alpha * gamma - D ^ 2 ≠ 0)
    (hQ : Q = 4 * p * alpha / (alpha * gamma - D ^ 2)) :
    gamma - D ^ 2 / alpha = 4 * p / Q := by
  rw [hQ]
  field_simp [hp, halpha, hT]

/-- Synthetic rank-one increments attain equality for any scale parameters.
This finite family demonstrates why stronger feedback needs arithmetic input. -/
theorem synthetic_coupling_sharp (alpha D rOld rNew : ℝ) (halpha : alpha ≠ 0) :
    (-D * (rOld - rNew)) ^ 2 =
      (alpha * (rOld - rNew)) * ((D ^ 2 / alpha) * (rOld - rNew)) := by
  field_simp [halpha]

/-! The following is an abstract scalar model, not the arithmetic packet
system. It satisfies the coupling/source-limit hypotheses with a limit
strictly beyond the saturation endpoint, and keeps a nonzero signed coupling. -/
namespace AbstractModel

def r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
def A (n : ℕ) : ℝ := -r n
def B (n : ℕ) : ℝ := -2 * Real.pi + r n
def C (n : ℕ) : ℝ := -5 * Real.pi - r n

theorem r_pos (n : ℕ) : 0 < r n := by unfold r; positivity

theorem r_le_one (n : ℕ) : r n ≤ 1 := by
  unfold r
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith only [hn]

theorem r_antitone : Antitone r := by
  intro n m hnm
  unfold r
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 1)
  have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
  linarith only [hcast]

theorem r_tendsto_zero : Tendsto r atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem source_limits :
    Tendsto A atTop (𝓝 0) ∧
      Tendsto B atTop (𝓝 (-2 * Real.pi)) ∧
        Tendsto C atTop (𝓝 (-5 * Real.pi)) := by
  constructor
  · change Tendsto (fun n => -r n) atTop (𝓝 0)
    simpa only [neg_zero] using r_tendsto_zero.neg
  constructor
  · change Tendsto (fun n => -2 * Real.pi + r n) atTop (𝓝 (-2 * Real.pi))
    simpa only [add_zero] using
      (tendsto_const_nhds.add r_tendsto_zero :
        Tendsto (fun n => -2 * Real.pi + r n) atTop (𝓝 (-2 * Real.pi + 0)))
  · change Tendsto (fun n => -5 * Real.pi - r n) atTop (𝓝 (-5 * Real.pi))
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub r_tendsto_zero :
        Tendsto (fun n => -5 * Real.pi - r n) atTop (𝓝 (-5 * Real.pi - 0)))

theorem coupling_equality (n m : ℕ) :
    (B m - B n) ^ 2 = (A m - A n) * (C m - C n) := by
  unfold A B C
  ring

/-- Both diagonal increments are positive; the mixed increment is their
negative, so the full rank-one correction preserves its sign. -/
theorem increments_signed (n m : ℕ) :
    A m - A n = r n - r m ∧
      B m - B n = -(r n - r m) ∧ C m - C n = r n - r m := by
  unfold A B C
  constructor
  · ring
  constructor <;> ring

/-- The complete two-source increment form is positive semidefinite; its
negative mixed term is retained as `(r_n-r_m)*(x-y)^2`. -/
theorem increment_quadratic_nonneg (n m : ℕ) (hnm : n ≤ m) (x y : ℝ) :
    0 ≤ (A m - A n) * x ^ 2 +
      2 * (B m - B n) * x * y + (C m - C n) * y ^ 2 := by
  have hdelta : 0 ≤ r n - r m := sub_nonneg.mpr (r_antitone hnm)
  have hid : (A m - A n) * x ^ 2 +
      2 * (B m - B n) * x * y + (C m - C n) * y ^ 2 =
        (r n - r m) * (x - y) ^ 2 := by
    unfold A B C
    ring
  rw [hid]
  exact mul_nonneg hdelta (sq_nonneg _)

theorem alpha_pos (n : ℕ) : 0 < -A n := by simpa only [A, neg_neg] using r_pos n

theorem shifted_determinant (n : ℕ) :
    (-A n) * (-C n) - (2 * Real.pi + B n) ^ 2 = 5 * Real.pi * r n := by
  unfold A B C
  ring

theorem shifted_determinant_pos (n : ℕ) :
    0 < (-A n) * (-C n) - (2 * Real.pi + B n) ^ 2 := by
  rw [shifted_determinant]
  exact mul_pos (by positivity) (r_pos n)

/-- The unshifted two-source determinant is also indefinite, so this abstract
model respects that separate finite Lorentz-form restriction. -/
theorem source_determinant_neg (n : ℕ) : A n * C n - (B n) ^ 2 < 0 := by
  have hid : A n * C n - (B n) ^ 2 =
      9 * Real.pi * r n - 4 * Real.pi ^ 2 := by
    unfold A B C
    ring
  have hu : 9 * Real.pi * r n ≤ 9 * Real.pi := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (r_le_one n) (by positivity : (0 : ℝ) ≤ 9 * Real.pi)
  rw [hid]
  calc
    _ ≤ 9 * Real.pi - 4 * Real.pi ^ 2 := sub_le_sub_right hu _
    _ = Real.pi * (9 - 4 * Real.pi) := by ring
    _ < 0 := mul_neg_of_pos_of_neg Real.pi_pos (by linarith only [Real.pi_gt_three])

theorem corrected_charge (n : ℕ) :
    -C n - (2 * Real.pi + B n) ^ 2 / (-A n) = 5 * Real.pi := by
  have hr : r n ≠ 0 := ne_of_gt (r_pos n)
  unfold A B C
  field_simp [hr] <;> ring

theorem projection_charge (n : ℕ) :
    4 * Real.pi * (-A n) /
      ((-A n) * (-C n) - (2 * Real.pi + B n) ^ 2) = (4 : ℝ) / 5 := by
  have hr : r n ≠ 0 := ne_of_gt (r_pos n)
  have halpha : -A n = r n := by unfold A; ring
  have hgamma : -C n = 5 * Real.pi + r n := by unfold C; ring
  have hD : 2 * Real.pi + B n = r n := by unfold B; ring
  have hden : r n * (5 * Real.pi + r n) - (r n) ^ 2 = 5 * Real.pi * r n := by ring
  rw [halpha, hgamma, hD, hden]
  field_simp [hr, Real.pi_ne_zero] <;> ring

/-- Exact witness that all scalar coupling and source-limit premises permit
an unsaturated charge. This witness makes no claim about physical packets. -/
theorem unsaturated_source_model :
    (∀ n : ℕ, 0 < -A n) ∧
      (∀ n m : ℕ, n ≤ m → (B m - B n) ^ 2 ≤ (A m - A n) * (C m - C n)) ∧
      Tendsto A atTop (𝓝 0) ∧
      Tendsto B atTop (𝓝 (-2 * Real.pi)) ∧
      Tendsto C atTop (𝓝 (-5 * Real.pi)) ∧
      -(-5 * Real.pi) > 4 * Real.pi := by
  obtain ⟨hA, hB, hC⟩ := source_limits
  refine ⟨alpha_pos, (fun n m _ => (coupling_equality n m).le), hA, hB, hC, ?_⟩
  nlinarith only [Real.pi_pos]

end AbstractModel

section SignedSourceEnergy
variable {κ : Type*} [Fintype κ]
/-! Source: elementary completion of the complete physical signed source
eta = m U - (Q/2) V. The mixed pairing and parallel square remain in the exact
identity. Strictness of the actual two-source determinant is a separate input.
-/
/-- The complete signed quadratic source, with its mixed term retained. -/
theorem signedSource_quadratic (Z : Matrix κ κ ℝ) (u v : κ → ℝ)
    (m Q : ℝ) (hZsym : Zᵀ = Z) :
    (m • u - (Q / 2) • v) ⬝ᵥ
        (Z *ᵥ (m • u - (Q / 2) • v)) =
      m ^ 2 * (u ⬝ᵥ (Z *ᵥ u)) -
        m * Q * (u ⬝ᵥ (Z *ᵥ v)) +
        (Q ^ 2 / 4) * (v ⬝ᵥ (Z *ᵥ v)) := by
  have hpair : v ⬝ᵥ (Z *ᵥ u) = u ⬝ᵥ (Z *ᵥ v) := by
    simpa only [hZsym] using Matrix.dotProduct_transpose_mulVec Z v u
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hpair]
  ring

/-- Exact orthogonal and parallel source decomposition. The parallel square
is part of the equality; no actual source lower bound is hidden here. -/
theorem signedSource_quadratic_completeSquare (Z : Matrix κ κ ℝ)
    (u v : κ → ℝ) (m Q : ℝ) (hZsym : Zᵀ = Z)
    (hC : v ⬝ᵥ (Z *ᵥ v) ≠ 0) :
    (m • u - (Q / 2) • v) ⬝ᵥ
        (Z *ᵥ (m • u - (Q / 2) • v)) =
      m ^ 2 * (u ⬝ᵥ (Z *ᵥ u) -
        (u ⬝ᵥ (Z *ᵥ v)) ^ 2 / (v ⬝ᵥ (Z *ᵥ v))) +
      (v ⬝ᵥ (Z *ᵥ v)) *
        (Q / 2 - m * (u ⬝ᵥ (Z *ᵥ v)) / (v ⬝ᵥ (Z *ᵥ v))) ^ 2 := by
  rw [signedSource_quadratic Z u v m Q hZsym]
  field_simp [hC]
  ring

/-- A positive norm for the second source isolates a uniform-in-`Q` lower
bound. Strictness of the actual arithmetic determinant is still an input. -/
theorem signedSource_quadratic_ge_orthogonal (Z : Matrix κ κ ℝ)
    (u v : κ → ℝ) (m Q : ℝ) (hZsym : Zᵀ = Z)
    (hC : 0 < v ⬝ᵥ (Z *ᵥ v)) :
    m ^ 2 * (u ⬝ᵥ (Z *ᵥ u) -
      (u ⬝ᵥ (Z *ᵥ v)) ^ 2 / (v ⬝ᵥ (Z *ᵥ v))) ≤
      (m • u - (Q / 2) • v) ⬝ᵥ
        (Z *ᵥ (m • u - (Q / 2) • v)) := by
  rw [signedSource_quadratic_completeSquare Z u v m Q hZsym (ne_of_gt hC)]
  exact le_add_of_nonneg_right (mul_nonneg hC.le (sq_nonneg _))

/-- The orthogonal lower bound is attained at the exact compensating charge.
Thus no stronger bound uniform in `Q` follows from these three pairings alone. -/
theorem signedSource_quadratic_orthogonal_sharp (Z : Matrix κ κ ℝ)
    (u v : κ → ℝ) (m : ℝ) (hZsym : Zᵀ = Z)
    (hC : v ⬝ᵥ (Z *ᵥ v) ≠ 0) :
    (m • u - ((2 * m * (u ⬝ᵥ (Z *ᵥ v)) /
        (v ⬝ᵥ (Z *ᵥ v))) / 2) • v) ⬝ᵥ
      (Z *ᵥ (m • u - ((2 * m * (u ⬝ᵥ (Z *ᵥ v)) /
        (v ⬝ᵥ (Z *ᵥ v))) / 2) • v)) =
      m ^ 2 * (u ⬝ᵥ (Z *ᵥ u) -
        (u ⬝ᵥ (Z *ᵥ v)) ^ 2 / (v ⬝ᵥ (Z *ᵥ v))) := by
  rw [signedSource_quadratic_completeSquare Z u v m
    (2 * m * (u ⬝ᵥ (Z *ᵥ v)) / (v ⬝ᵥ (Z *ᵥ v))) hZsym hC]
  have hparallel : (2 * m * (u ⬝ᵥ (Z *ᵥ v)) /
      (v ⬝ᵥ (Z *ᵥ v))) / 2 -
      m * (u ⬝ᵥ (Z *ᵥ v)) / (v ⬝ᵥ (Z *ᵥ v)) = 0 := by ring
  rw [hparallel]
  ring

/-- The actual source gain is positive whenever a nonzero residual mean and
a strict two-source Gram determinant have both been supplied. -/
theorem signedSource_quadratic_pos_of_determinant (Z : Matrix κ κ ℝ)
    (u v : κ → ℝ) (m Q : ℝ) (hZsym : Zᵀ = Z)
    (hC : 0 < v ⬝ᵥ (Z *ᵥ v)) (hm : m ≠ 0)
    (hdet : (u ⬝ᵥ (Z *ᵥ v)) ^ 2 <
      (u ⬝ᵥ (Z *ᵥ u)) * (v ⬝ᵥ (Z *ᵥ v))) :
    0 < (m • u - (Q / 2) • v) ⬝ᵥ
      (Z *ᵥ (m • u - (Q / 2) • v)) := by
  have horth : 0 < u ⬝ᵥ (Z *ᵥ u) -
      (u ⬝ᵥ (Z *ᵥ v)) ^ 2 / (v ⬝ᵥ (Z *ᵥ v)) := by
    apply sub_pos.mpr
    exact (div_lt_iff₀ hC).2 hdet
  exact lt_of_lt_of_le (mul_pos (sq_pos_of_ne_zero hm) horth)
    (signedSource_quadratic_ge_orthogonal Z u v m Q hZsym hC)

/-- At the zero second-source endpoint, positivity forces the entire mixed
pairing to vanish; the finite formula remains valid without a quotient. -/
theorem signedSource_quadratic_of_zero_second_source (Z : Matrix κ κ ℝ)
    (u v : κ → ℝ) (m Q : ℝ) (hZsym : Zᵀ = Z)
    (hZpos : ∀ w : κ → ℝ, 0 ≤ w ⬝ᵥ (Z *ᵥ w))
    (hC : v ⬝ᵥ (Z *ᵥ v) = 0) :
    (m • u - (Q / 2) • v) ⬝ᵥ
        (Z *ᵥ (m • u - (Q / 2) • v)) =
      m ^ 2 * (u ⬝ᵥ (Z *ᵥ u)) := by
  have hc := source_pair_cauchy Z u v hZsym hZpos
  rw [hC, mul_zero] at hc
  have hB : u ⬝ᵥ (Z *ᵥ v) = 0 := by nlinarith only [hc]
  rw [signedSource_quadratic Z u v m Q hZsym, hC, hB]
  ring

end SignedSourceEnergy
end RiemannResearch.LinearAlgebra.MeanOneSchurCoupling
