/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.FiniteCurvatureGreen
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


/-!
# Exact half-density curvature and polar-null bump coordinates

Source: user-provided arguments,
`RH_Exact_Arithmetic_Channel_Effects_2026-09-07.md`, Section 8, and
`prime_half_density_bridge_agent.md`, Sections 1 and 2. These sources support
the statements and proof strategy.

For positive real nodes with nonzero adjacent gaps, the adjacent-curvature
prefix section proves the full converse and uniqueness in the half-density
range theorem, over both real and complex coefficients. No kernel, rank, or
range conclusion is assumed. The complete signed Gram congruence keeps every
mixed entry and annihilates the polar matrix exactly. The coefficient metric
is proved positive; the physical mass uses its own supplied bump Gram matrix.

The last theorem concerns actual exponential integrals of translated common
bumps. It assumes their integrability and two nonzero bump moments; it proves
the polar-null/range equivalence. Smoothness, compact support, independence of
the bump translates, prime-log density, and the all-window Weil criterion are
not established here. No positivity assertion is made for the signed Gram
matrix or for the Weil form.
-/

open scoped BigOperators Matrix
open Matrix LinearMap
namespace RiemannResearch.RH.PrimeCurvaturePolarBridge
noncomputable section

theorem _root_.Matrix.transpose_range_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (D : Matrix κ ι ℝ) (S : Matrix ι κ ℝ) (hDS : D * S = 1)
    (v : ι → ℝ) :
    (∃! a : κ → ℝ, Dᵀ *ᵥ a = v) ↔
      ∀ z, D *ᵥ z = 0 → v ⬝ᵥ z = 0 := by
  have hSD : Sᵀ * Dᵀ = 1 := by
    rw [← Matrix.transpose_mul, hDS, Matrix.transpose_one]
  constructor
  · rintro ⟨a, rfl, _⟩ z hz
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hz, dotProduct_zero]
  · intro hv
    have hp : Dᵀ *ᵥ (Sᵀ *ᵥ v) = v := by
      have hh : ∀ z, v ⬝ᵥ z = (Dᵀ *ᵥ (Sᵀ *ᵥ v)) ⬝ᵥ z := by
        intro z
        have hz : D *ᵥ (z - S *ᵥ (D *ᵥ z)) = 0 := by
          rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hDS, Matrix.one_mulVec, sub_self]
        have he := hv _ hz
        rw [dotProduct_sub, sub_eq_zero] at he
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
          Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at he
        exact he
      funext j
      simpa using (hh (Pi.single j 1)).symm
    refine ⟨Sᵀ *ᵥ v, hp, ?_⟩
    intro b hb
    have hh := congrArg (fun w => Sᵀ *ᵥ w) hb
    simpa [Matrix.mulVec_mulVec, hSD] using hh

open PrimeGapCurvature

/-- Adjacent slope-difference matrix on the first n+2 nodes. -/
def curvatureMatrix (t : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin (n+2)) ℝ :=
  LinearMap.toMatrix' (finiteCurvatureMap (finiteGapWindow n t))

/-- The already constructed prefix right inverse in matrix coordinates. -/
def prefixMatrix (t : ℕ → ℝ) (n : ℕ) : Matrix (Fin (n+2)) (Fin n) ℝ :=
  LinearMap.toMatrix' (profilePrefixLinearMap (finiteGapWindow n t))

@[simp] theorem curvatureMatrix_mulVec (t : ℕ → ℝ) (n : ℕ)
    (z : Fin (n+2) → ℝ) :
    curvatureMatrix t n *ᵥ z = finiteCurvatureMap (finiteGapWindow n t) z := by
  exact congrArg (fun f => f z)
    (Matrix.toLin'_toMatrix' (finiteCurvatureMap (finiteGapWindow n t)))

@[simp] theorem prefixMatrix_mulVec (t : ℕ → ℝ) (n : ℕ)
    (a : Fin n → ℝ) :
    prefixMatrix t n *ᵥ a = profilePrefixLinearMap (finiteGapWindow n t) a := by
  exact congrArg (fun f => f a)
    (Matrix.toLin'_toMatrix' (profilePrefixLinearMap (finiteGapWindow n t)))

theorem curvatureMatrix_mul_prefix (t : ℕ → ℝ) (n : ℕ)
    (hg : ∀ i ≤ n, gap t i ≠ 0) :
    curvatureMatrix t n * prefixMatrix t n = 1 := by
  apply Matrix.mulVec_injective
  funext a
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, prefixMatrix_mulVec,
    curvatureMatrix_mulVec]
  apply finiteCurvature_profilePrefix
  intro j
  exact hg j.val (Nat.le_of_lt_succ j.isLt)

theorem curvatureMatrix_kernel (t : ℕ → ℝ) (n : ℕ)
    (hg : ∀ i ≤ n, gap t i ≠ 0) (z : Fin (n+2) → ℝ) :
    curvatureMatrix t n *ᵥ z = 0 ↔
      ∃ A B : ℝ, ∀ j, z j = A + B * t j.val := by
  rw [curvatureMatrix_mulVec, ← LinearMap.mem_ker,
    ker_finiteCurvatureMap_eq_range_affineProfileMap t n hg]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1, p.2, fun j => (congrFun hp j).symm⟩
  · rintro ⟨A, B, h⟩
    exact ⟨(A, B), funext fun j => (h j).symm⟩

/-- The half-density transpose C=diag(sqrt(t)) Dᵀ. -/
def halfDensityMatrix (t : ℕ → ℝ) (n : ℕ) :
    Matrix (Fin (n+2)) (Fin n) ℝ :=
  Matrix.diagonal (fun j => Real.sqrt (t j.val)) * (curvatureMatrix t n)ᵀ

@[simp] theorem halfDensityMatrix_mulVec (t : ℕ → ℝ) (n : ℕ)
    (a : Fin n → ℝ) (j : Fin (n+2)) :
    (halfDensityMatrix t n *ᵥ a) j =
      Real.sqrt (t j.val) * ((curvatureMatrix t n)ᵀ *ᵥ a) j := by
  rw [halfDensityMatrix, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]

theorem polar_iff_affine_orthogonal (t : ℕ → ℝ) (n : ℕ)
    (ht : ∀ j : Fin (n+2), 0 < t j.val) (c : Fin (n+2) → ℝ) :
    ((∑ j, c j / Real.sqrt (t j.val)) = 0 ∧
      (∑ j, c j * Real.sqrt (t j.val)) = 0) ↔
    ∀ A B : ℝ, (fun j => c j / Real.sqrt (t j.val)) ⬝ᵥ
      (fun j => A + B * t j.val) = 0 := by
  have he : ∀ j : Fin (n+2),
      c j / Real.sqrt (t j.val) * t j.val = c j * Real.sqrt (t j.val) := by
    intro j
    have hs := Real.sq_sqrt (ht j).le
    have hn := (Real.sqrt_pos.2 (ht j)).ne'
    field_simp
    rw [hs]
  have hf : ∀ A B : ℝ, (fun j => c j / Real.sqrt (t j.val)) ⬝ᵥ
      (fun j => A + B * t j.val) =
      A * (∑ j, c j / Real.sqrt (t j.val)) +
      B * (∑ j, c j * Real.sqrt (t j.val)) := by
    intro A B
    simp only [dotProduct, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [show c j / Real.sqrt (t j.val) * (B * t j.val) =
        B * (c j / Real.sqrt (t j.val) * t j.val) by ring, he]
  simp_rw [hf]
  constructor
  · rintro ⟨h₀, h₁⟩ A B
    simp [h₀, h₁]
  · intro h
    exact ⟨by simpa using h 1 0, by simpa using h 0 1⟩

theorem halfDensity_existsUnique_iff (t : ℕ → ℝ) (n : ℕ)
    (hg : ∀ i ≤ n, gap t i ≠ 0)
    (ht : ∀ j : Fin (n+2), 0 < t j.val) (c : Fin (n+2) → ℝ) :
    (∃! a, halfDensityMatrix t n *ᵥ a = c) ↔
      (∑ j, c j / Real.sqrt (t j.val)) = 0 ∧
      (∑ j, c j * Real.sqrt (t j.val)) = 0 := by
  have hc : ∀ a, halfDensityMatrix t n *ᵥ a = c ↔
      (curvatureMatrix t n)ᵀ *ᵥ a = fun j => c j / Real.sqrt (t j.val) := by
    intro a
    simp only [funext_iff, halfDensityMatrix_mulVec]
    apply forall_congr'
    intro j
    rw [eq_div_iff (Real.sqrt_pos.2 (ht j)).ne']
    exact (mul_comm _ _).congr_left
  simp_rw [hc]
  rw [transpose_range_iff _ _ (curvatureMatrix_mul_prefix t n hg),
    polar_iff_affine_orthogonal t n ht c]
  constructor
  · intro h A B
    apply h
    rw [curvatureMatrix_kernel t n hg]
    exact ⟨A, B, fun _ => rfl⟩
  · intro h z hz
    obtain ⟨A, B, hh⟩ := (curvatureMatrix_kernel t n hg z).mp hz
    simpa only [funext hh] using h A B

/-- The real polar kernel on positive multiplicative nodes. -/
def polarMatrix (t : ℕ → ℝ) (n : ℕ) (μ : ℝ) :
    Matrix (Fin (n+2)) (Fin (n+2)) ℝ :=
  fun i j => μ * (Real.sqrt (t i.val) / Real.sqrt (t j.val) +
    Real.sqrt (t j.val) / Real.sqrt (t i.val))

theorem weighted_polarMatrix (t : ℕ → ℝ) (n : ℕ)
    (ht : ∀ j : Fin (n+2), 0 < t j.val) (μ : ℝ) :
    Matrix.diagonal (fun i : Fin (n+2) => Real.sqrt (t i.val)) *
      polarMatrix t n μ *
      Matrix.diagonal (fun i : Fin (n+2) => Real.sqrt (t i.val)) =
    fun i j => μ * (t i.val + t j.val) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, polarMatrix]
  have hi := (Real.sqrt_pos.2 (ht i)).ne'
  have hj := (Real.sqrt_pos.2 (ht j)).ne'
  have si := Real.sq_sqrt (ht i).le
  have sj := Real.sq_sqrt (ht j).le
  field_simp
  rw [si, sj]

theorem curvature_mul_affinePolar (t : ℕ → ℝ) (n : ℕ)
    (hg : ∀ i ≤ n, gap t i ≠ 0) (μ : ℝ) :
    curvatureMatrix t n * (show Matrix (Fin (n+2)) (Fin (n+2)) ℝ from
      fun i j => μ * (t i.val + t j.val)) = 0 := by
  ext i j
  have h := (curvatureMatrix_kernel t n hg
    (fun k : Fin (n+2) => μ * (t k.val + t j.val))).2
    ⟨μ * t j.val, μ, fun k => by ring⟩
  exact congrFun h i

theorem halfDensity_polar_annihilation (t : ℕ → ℝ) (n : ℕ)
    (hg : ∀ i ≤ n, gap t i ≠ 0)
    (ht : ∀ j : Fin (n+2), 0 < t j.val) (μ : ℝ) :
    (halfDensityMatrix t n)ᵀ * polarMatrix t n μ *
      halfDensityMatrix t n = 0 := by
  simp only [halfDensityMatrix, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose]
  calc
    _ = curvatureMatrix t n *
      (Matrix.diagonal (fun i : Fin (n+2) => Real.sqrt (t i.val)) *
      polarMatrix t n μ *
      Matrix.diagonal (fun i : Fin (n+2) => Real.sqrt (t i.val))) *
      (curvatureMatrix t n)ᵀ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [weighted_polarMatrix t n ht, curvature_mul_affinePolar t n hg,
      Matrix.zero_mul]

/-- Matrix congruence for the full signed real bilinear form, with every mixed entry. -/
theorem _root_.Matrix.signed_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : Matrix ι κ ℝ) (H : Matrix ι ι ℝ) (a b : κ → ℝ) :
    (C *ᵥ a) ⬝ᵥ (H *ᵥ (C *ᵥ b)) =
      a ⬝ᵥ ((Cᵀ * H * C) *ᵥ b) := by
  rw [dotProduct_comm (C *ᵥ a), Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm _ a,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]


/-- Physical mass is compressed through the bump Gram matrix M₀. -/
def _root_.Matrix.physicalMass {ι κ : Type*} [Fintype ι]
    (C : Matrix ι κ ℝ) (M₀ : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  Cᵀ * M₀ * C

/-- Coefficient mass uses the identity coefficient metric. -/
def _root_.Matrix.coefficientMass {ι κ : Type*} [Fintype ι]
    (C : Matrix ι κ ℝ) : Matrix κ κ ℝ := Cᵀ * C

theorem halfDensity_coefficientMass (t : ℕ → ℝ) (n : ℕ)
    (ht : ∀ j : Fin (n+2), 0 ≤ t j.val) :
    coefficientMass (halfDensityMatrix t n) =
      curvatureMatrix t n * Matrix.diagonal (fun j => t j.val) *
        (curvatureMatrix t n)ᵀ := by
  simp only [coefficientMass, halfDensityMatrix, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.diagonal_transpose]
  have hd : Matrix.diagonal (fun j : Fin (n+2) => Real.sqrt (t j.val)) *
      Matrix.diagonal (fun j : Fin (n+2) => Real.sqrt (t j.val)) =
      Matrix.diagonal (fun j : Fin (n+2) => t j.val) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    exact Real.mul_self_sqrt (ht j)
  calc
    _ = curvatureMatrix t n *
      (Matrix.diagonal (fun j : Fin (n+2) => Real.sqrt (t j.val)) *
       Matrix.diagonal (fun j : Fin (n+2) => Real.sqrt (t j.val))) *
      (curvatureMatrix t n)ᵀ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hd]


/-- The complete complex sesquilinear matrix transforms by conjugate congruence. -/
theorem _root_.Matrix.signed_complex_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : Matrix ι κ ℂ) (H : Matrix ι ι ℂ) (a b : κ → ℂ) :
    star (C *ᵥ a) ⬝ᵥ (H *ᵥ (C *ᵥ b)) =
      star a ⬝ᵥ ((Cᴴ * H * C) *ᵥ b) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- The Gram entries of an arbitrary real bilinear form retain all mixed terms. -/
theorem _root_.LinearMap.bilinear_gram_expansion {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℝ E] (Q : LinearMap.BilinForm ℝ E)
    (h : ι → E) (a b : ι → ℝ) :
    Q (∑ i, a i • h i) (∑ j, b j • h j) =
      a ⬝ᵥ ((fun i j => Q (h i) (h j)) *ᵥ b) := by
  simp [dotProduct, Matrix.mulVec, map_sum, map_smul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- No nonzero curvature coordinate vector is lost by half-density synthesis. -/
theorem halfDensity_injective (t : ℕ → ℝ) (n : ℕ)
    (hg : ∀ i ≤ n, gap t i ≠ 0)
    (ht : ∀ j : Fin (n+2), 0 < t j.val) :
    Function.Injective (fun a => halfDensityMatrix t n *ᵥ a) := by
  intro a b hab
  have heq : (curvatureMatrix t n)ᵀ *ᵥ a = (curvatureMatrix t n)ᵀ *ᵥ b := by
    funext j
    have hj := congrFun hab j
    simp only [halfDensityMatrix_mulVec] at hj
    exact mul_left_cancel₀ (Real.sqrt_pos.2 (ht j)).ne' hj
  have hh := congrArg (fun v => (prefixMatrix t n)ᵀ *ᵥ v) heq
  simpa only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    curvatureMatrix_mul_prefix t n hg, Matrix.transpose_one, Matrix.one_mulVec] using hh

theorem _root_.Matrix.coefficientMass_positive {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : Matrix ι κ ℝ) (hC : Function.Injective (fun a => C *ᵥ a))
    (a : κ → ℝ) (ha : a ≠ 0) :
    0 < a ⬝ᵥ (coefficientMass C *ᵥ a) := by
  have he : a ⬝ᵥ (coefficientMass C *ᵥ a) = (C *ᵥ a) ⬝ᵥ (C *ᵥ a) := by
    rw [coefficientMass, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, Matrix.transpose_transpose]
  rw [he]
  have hn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (C *ᵥ a) i * (C *ᵥ a) i :=
    fun i _ => mul_self_nonneg _
  apply lt_of_le_of_ne (Finset.sum_nonneg hn)
  intro hh
  have hz : C *ᵥ a = C *ᵥ 0 := by
    rw [Matrix.mulVec_zero]
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hn).1 hh.symm i (Finset.mem_univ i)
    exact (mul_self_eq_zero).1 hi
  exact ha (hC hz)

theorem halfDensity_coefficientMass_positive (t : ℕ → ℝ) (n : ℕ)
    (hg : ∀ i ≤ n, gap t i ≠ 0)
    (ht : ∀ j : Fin (n+2), 0 < t j.val)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    0 < a ⬝ᵥ (coefficientMass (halfDensityMatrix t n) *ᵥ a) :=
  coefficientMass_positive _ (halfDensity_injective t n hg ht) a ha

/-- Real matrices acting on complex coefficients. -/
def _root_.Matrix.complexify {ι κ : Type*} (C : Matrix ι κ ℝ) : Matrix ι κ ℂ :=
  fun i j => (C i j : ℂ)

@[simp] theorem _root_.Matrix.complexify_mulVec_re {ι κ : Type*} [Fintype κ]
    (C : Matrix ι κ ℝ) (a : κ → ℂ) (i : ι) :
    ((complexify C *ᵥ a) i).re = (C *ᵥ (fun j => (a j).re)) i := by
  simp [complexify, Matrix.mulVec, dotProduct, Complex.mul_re]

@[simp] theorem _root_.Matrix.complexify_mulVec_im {ι κ : Type*} [Fintype κ]
    (C : Matrix ι κ ℝ) (a : κ → ℂ) (i : ι) :
    ((complexify C *ᵥ a) i).im = (C *ᵥ (fun j => (a j).im)) i := by
  simp [complexify, Matrix.mulVec, dotProduct, Complex.mul_im]

theorem halfDensity_complex_injective (t : ℕ → ℝ) (n : ℕ)
    (hg : ∀ i ≤ n, gap t i ≠ 0)
    (ht : ∀ j : Fin (n+2), 0 < t j.val) :
    Function.Injective (fun a => complexify (halfDensityMatrix t n) *ᵥ a) := by
  intro a b hab
  have hr : (fun j => (a j).re) = (fun j => (b j).re) := by
    apply halfDensity_injective t n hg ht
    funext i
    have hi := congrArg Complex.re (congrFun hab i)
    simpa only [complexify_mulVec_re] using hi
  have hi : (fun j => (a j).im) = (fun j => (b j).im) := by
    apply halfDensity_injective t n hg ht
    funext i
    have hi := congrArg Complex.im (congrFun hab i)
    simpa only [complexify_mulVec_im] using hi
  funext j
  exact Complex.ext (congrFun hr j) (congrFun hi j)

/-- Exact two polar constraints and unique curvature coefficients also over ℂ. -/
theorem halfDensity_complex_existsUnique_iff (t : ℕ → ℝ) (n : ℕ)
    (hg : ∀ i ≤ n, gap t i ≠ 0)
    (ht : ∀ j : Fin (n+2), 0 < t j.val) (c : Fin (n+2) → ℂ) :
    (∃! a, complexify (halfDensityMatrix t n) *ᵥ a = c) ↔
      (∑ j, c j * ((Real.sqrt (t j.val))⁻¹ : ℝ)) = 0 ∧
      (∑ j, c j * (Real.sqrt (t j.val) : ℝ)) = 0 := by
  have hsplit :
      ((∑ j, c j * ((Real.sqrt (t j.val))⁻¹ : ℝ)) = 0 ∧
       (∑ j, c j * (Real.sqrt (t j.val) : ℝ)) = 0) ↔
      (((∑ j, (c j).re / Real.sqrt (t j.val)) = 0 ∧
        (∑ j, (c j).re * Real.sqrt (t j.val)) = 0) ∧
       ((∑ j, (c j).im / Real.sqrt (t j.val)) = 0 ∧
        (∑ j, (c j).im * Real.sqrt (t j.val)) = 0)) := by
    have hs : ∀ j : Fin (n+2), Real.sqrt (t j.val) ≠ 0 :=
      fun j => (Real.sqrt_pos.2 (ht j)).ne'
    simp [Complex.ext_iff, div_eq_mul_inv, ← mul_assoc, hs]
    tauto
  rw [hsplit]
  constructor
  · rintro ⟨a, ha, _⟩
    constructor
    · apply (halfDensity_existsUnique_iff t n hg ht _).1
      refine ⟨fun j => (a j).re, ?_, ?_⟩
      · funext i
        have hi := congrArg Complex.re (congrFun ha i)
        simpa only [complexify_mulVec_re] using hi
      · intro b hb
        apply halfDensity_injective t n hg ht
        change halfDensityMatrix t n *ᵥ b = _
        rw [hb]
        funext i
        have hi := congrArg Complex.re (congrFun ha i)
        simpa only [complexify_mulVec_re] using hi.symm
    · apply (halfDensity_existsUnique_iff t n hg ht _).1
      refine ⟨fun j => (a j).im, ?_, ?_⟩
      · funext i
        have hi := congrArg Complex.im (congrFun ha i)
        simpa only [complexify_mulVec_im] using hi
      · intro b hb
        apply halfDensity_injective t n hg ht
        change halfDensityMatrix t n *ᵥ b = _
        rw [hb]
        funext i
        have hi := congrArg Complex.im (congrFun ha i)
        simpa only [complexify_mulVec_im] using hi.symm
  · rintro ⟨hr, hi⟩
    obtain ⟨ar, har, _⟩ := (halfDensity_existsUnique_iff t n hg ht _).2 hr
    obtain ⟨ai, hai, _⟩ := (halfDensity_existsUnique_iff t n hg ht _).2 hi
    let a : Fin n → ℂ := fun j => ⟨ar j, ai j⟩
    have ha : complexify (halfDensityMatrix t n) *ᵥ a = c := by
      funext j
      apply Complex.ext
      · simpa only [complexify_mulVec_re] using congrFun har j
      · simpa only [complexify_mulVec_im] using congrFun hai j
    exact ⟨a, ha, fun b hb => halfDensity_complex_injective t n hg ht (hb.trans ha.symm)⟩

/-- Synthesis by a finite family converts every sesquilinear form to its full Gram matrix. -/
theorem _root_.LinearMap.sesquilinear_gram_expansion {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℂ E] (Q : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ)
    (h : ι → E) (a b : ι → ℂ) :
    Q (∑ i, a i • h i) (∑ j, b j • h j) =
      star a ⬝ᵥ ((fun i j => Q (h i) (h j)) *ᵥ b) := by
  simp [dotProduct, Matrix.mulVec, map_sum, map_smul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Full Gram congruence after finite synthesis, with no positivity assumption. -/
theorem _root_.LinearMap.sesquilinear_curvature_compression {ι κ E : Type*}
    [Fintype ι] [Fintype κ] [AddCommGroup E] [Module ℂ E]
    (Q : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ) (h : ι → E)
    (C : Matrix ι κ ℂ) (a b : κ → ℂ) :
    Q (∑ i, (C *ᵥ a) i • h i) (∑ j, (C *ᵥ b) j • h j) =
      star a ⬝ᵥ ((Cᴴ * (show Matrix ι ι ℂ from fun i j => Q (h i) (h j)) * C) *ᵥ b) := by
  rw [sesquilinear_gram_expansion]
  exact signed_complex_congruence C (fun i j => Q (h i) (h j)) a b

/-- For an identity bump Gram matrix, physical and coefficient mass agree. -/
theorem _root_.Matrix.physicalMass_identity {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι κ ℝ) :
    physicalMass C (1 : Matrix ι ι ℝ) = coefficientMass C := by
  simp [physicalMass, coefficientMass]

open MeasureTheory

/-- Exponential moment; the two polar moments use r=±1/2. -/
def _root_.MeasureTheory.exponentialMoment (r : ℝ) (φ : ℝ → ℂ) : ℂ :=
  ∫ y, φ y * (Real.exp (r * y) : ℂ)

/-- The change of variables behind the exact half-density bridge. -/
theorem _root_.MeasureTheory.exponentialMoment_translate (r s : ℝ) (φ : ℝ → ℂ) :
    exponentialMoment r (fun y => φ (y-s)) =
      (Real.exp (r*s) : ℂ) * exponentialMoment r φ := by
  unfold exponentialMoment
  have hf : (fun y => φ (y-s) * (Real.exp (r*y) : ℂ)) =
      fun y => (Real.exp (r*s) : ℂ) *
        (φ (y-s) * (Real.exp (r*(y-s)) : ℂ)) := by
    funext y
    rw [show r*y = r*s + r*(y-s) by ring, Real.exp_add, Complex.ofReal_mul]
    ring
  rw [hf, integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self (fun y => φ y * (Real.exp (r*y) : ℂ)) s

/-- A finite common-bump synthesis. -/
def _root_.MeasureTheory.translatedSynthesis {ι : Type*} [Fintype ι]
    (φ : ℝ → ℂ) (s : ι → ℝ) (c : ι → ℂ) : ℝ → ℂ :=
  fun y => ∑ j, c j * φ (y-s j)

theorem _root_.MeasureTheory.exponentialMoment_synthesis {ι : Type*} [Fintype ι]
    (r : ℝ) (φ : ℝ → ℂ) (s : ι → ℝ) (c : ι → ℂ)
    (hi : ∀ j, Integrable (fun y => φ (y-s j) * (Real.exp (r*y) : ℂ))) :
    exponentialMoment r (translatedSynthesis φ s c) =
      (∑ j, c j * (Real.exp (r*s j) : ℂ)) * exponentialMoment r φ := by
  unfold exponentialMoment translatedSynthesis
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun j _ => (hi j).const_mul (c j))]
  simp_rw [integral_const_mul]
  change (∑ j, c j * exponentialMoment r (fun y => φ (y-s j))) = _
  simp_rw [exponentialMoment_translate, ← mul_assoc]
  rfl

private theorem exp_half_log (x : ℝ) (hx : 0 < x) :
    Real.exp ((1/2 : ℝ) * Real.log x) = Real.sqrt x := by
  rw [show (1/2 : ℝ) * Real.log x = Real.log x / 2 by ring,
    Real.exp_half, Real.exp_log hx]

private theorem exp_neg_half_log (x : ℝ) (hx : 0 < x) :
    Real.exp ((-1/2 : ℝ) * Real.log x) = (Real.sqrt x)⁻¹ := by
  rw [show (-1/2 : ℝ) * Real.log x = -((1/2 : ℝ) * Real.log x) by ring,
    Real.exp_neg, exp_half_log x hx]

@[simp] theorem _root_.Matrix.complexify_mul {ι κ ν : Type*} [Fintype κ]
    (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    complexify (A * B) = complexify A * complexify B := by
  ext i j
  simp [complexify, Matrix.mul_apply]

@[simp] theorem _root_.Matrix.complexify_transpose {ι κ : Type*}
    (A : Matrix ι κ ℝ) :
    complexify Aᵀ = (complexify A)ᴴ := by
  ext i j
  simp [complexify]

@[simp] theorem _root_.Matrix.complexify_zero {ι κ : Type*} :
    complexify (0 : Matrix ι κ ℝ) = 0 := by
  ext i j
  rfl

theorem halfDensity_complex_polar_annihilation (t : ℕ → ℝ) (n : ℕ)
    (hg : ∀ i ≤ n, gap t i ≠ 0)
    (ht : ∀ j : Fin (n+2), 0 < t j.val) (μ : ℝ) :
    (complexify (halfDensityMatrix t n))ᴴ * complexify (polarMatrix t n μ) *
      complexify (halfDensityMatrix t n) = 0 := by
  have h := congrArg (complexify (ι := Fin n) (κ := Fin n))
    (halfDensity_polar_annihilation t n hg ht μ)
  simpa only [complexify_mul, complexify_transpose, complexify_zero] using h

/-- The actual two exponential moments of common logarithmic bump translates vanish
exactly on the half-density curvature range. Integrability and nonzero bump moments
are the analytic hypotheses; the range and uniqueness are proved, not assumed. -/
theorem translated_polarNull_iff_unique_curvature
    (t : ℕ → ℝ) (n : ℕ) (hg : ∀ i ≤ n, gap t i ≠ 0)
    (ht : ∀ j : Fin (n+2), 0 < t j.val) (φ : ℝ → ℂ)
    (hplus : exponentialMoment (1/2) φ ≠ 0)
    (hminus : exponentialMoment (-1/2) φ ≠ 0)
    (hiplus : ∀ j : Fin (n+2), Integrable
      (fun y => φ (y-Real.log (t j.val)) * (Real.exp ((1/2)*y) : ℂ)))
    (himinus : ∀ j : Fin (n+2), Integrable
      (fun y => φ (y-Real.log (t j.val)) * (Real.exp ((-1/2)*y) : ℂ)))
    (c : Fin (n+2) → ℂ) :
    (exponentialMoment (1/2)
        (translatedSynthesis φ (fun j => Real.log (t j.val)) c) = 0 ∧
      exponentialMoment (-1/2)
        (translatedSynthesis φ (fun j => Real.log (t j.val)) c) = 0) ↔
    ∃! a, complexify (halfDensityMatrix t n) *ᵥ a = c := by
  rw [exponentialMoment_synthesis _ _ _ _ hiplus,
    exponentialMoment_synthesis _ _ _ _ himinus,
    halfDensity_complex_existsUnique_iff t n hg ht]
  simp_rw [exp_half_log _ (ht _), exp_neg_half_log _ (ht _)]
  simp only [mul_eq_zero, hplus, hminus, or_false]
  exact and_comm

end
end RiemannResearch.RH.PrimeCurvaturePolarBridge
