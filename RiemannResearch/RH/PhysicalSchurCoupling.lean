/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PhysicalSchurReindex
import RiemannResearch.LinearAlgebra.MeanOneSchurCoupling

/-!
# Actual complete inverse-Schur coupling for physical packets

Nested legal finite packet sets and an old odd prime discharge all matrix
inverse and positivity premises of the complete signed Schur update.
No source limit or endpoint saturation is asserted here.

Source: user-directed continuation of PhysicalMeanOneAdvance20261008.md;
the finite physical specialization is assembled from the proved inertia and
complete block Schur identities.
-/

noncomputable section
open Matrix Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PhysicalSchurCoupling
open RiemannResearch.RH.Pareto
open PhysicalPacketCore PhysicalSchurReindex
open RiemannResearch.LinearAlgebra.MeanOneBlockSchur
open RiemannResearch.LinearAlgebra.MeanOneSchurCoupling

/-- The full Schur complement of the actual arithmetic core, with every
new packet retained simultaneously. -/
def coreSchur (s t : Finset ℕ) (hst : s ⊆ t) : Matrix ↥(t \ s) ↥(t \ s) ℝ :=
  schurMatrix (derivedCore s)⁻¹ (crossCore s t hst) (derivedCore (t \ s))

def screenedLambda (s t : Finset ℕ) (hst : s ⊆ t) : ↥(t \ s) → ℝ :=
  screenedSource (derivedCore s)⁻¹ (crossCore s t hst)
    (ramanujanVonMangoldtVector s) (ramanujanVonMangoldtVector (t \ s))

def screenedTotient (s t : Finset ℕ) (hst : s ⊆ t) : ↥(t \ s) → ℝ :=
  screenedSource (derivedCore s)⁻¹ (crossCore s t hst)
    (ramanujanTotientVector s) (ramanujanTotientVector (t \ s))

def logarithmicCharge (s : Finset ℕ) : ℝ :=
  ramanujanVonMangoldtVector s ⬝ᵥ
    ((derivedCore s)⁻¹ *ᵥ ramanujanVonMangoldtVector s)

def mixedCharge (s : Finset ℕ) : ℝ :=
  ramanujanVonMangoldtVector s ⬝ᵥ
    ((derivedCore s)⁻¹ *ᵥ ramanujanTotientVector s)

def shiftedDeterminant (s : Finset ℕ) : ℝ :=
  logarithmicCharge s * inverseCharge s - (2 * Real.pi + mixedCharge s) ^ 2

def sourceCorrectedCharge (s : Finset ℕ) : ℝ :=
  -inverseCharge s - (2 * Real.pi + mixedCharge s) ^ 2 / (-logarithmicCharge s)

/-- The source-charge expression used in the projection bound. This
definition alone asserts no Gram-inverse identification. -/
def sourceProjectionCharge (s : Finset ℕ) : ℝ :=
  4 * Real.pi * (-logarithmicCharge s) / shiftedDeterminant s

theorem inverseCore_transpose (s : Finset ℕ) :
    ((derivedCore s)⁻¹)ᵀ = (derivedCore s)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, derivedCore_transpose]

theorem inverseCore_mul (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    (derivedCore s)⁻¹ * derivedCore s = 1 := by
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (derivedCore_det_ne_zero s hs hodd))

theorem coreSchur_transpose (s t : Finset ℕ) (hst : s ⊆ t) :
    (coreSchur s t hst)ᵀ = coreSchur s t hst := by
  unfold coreSchur schurMatrix
  simp only [Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose, inverseCore_transpose,
    derivedCore_transpose, Matrix.mul_assoc]

/-- The complete negative mean correction still has a positive quadratic
form: it is the actual mean-zero physical tangent Gram. -/
theorem meanTangentSchur_pos (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (y : ↥(t \ s) → ℝ) (hy : y ≠ 0) :
    0 < y ⬝ᵥ (meanTangentSchur (coreSchur s t hst)
      (screenedTotient s t hst) (inverseCharge s) *ᵥ y) := by
  have hs : ∀ q ∈ s, 1 < q := fun q hq => ht q (hst hq)
  have hC : inverseCharge s ≠ 0 := ne_of_lt (inverseCharge_neg s hs hodd)
  let x := tangentOld (derivedCore s)⁻¹ (crossCore s t hst)
    (ramanujanTotientVector s) (screenedTotient s t hst) y (inverseCharge s)
  have hmean : ramanujanTotientVector s ⬝ᵥ x +
      ramanujanTotientVector (t \ s) ⬝ᵥ y = 0 := by
    exact tangent_mean_zero (derivedCore s)⁻¹ (crossCore s t hst)
      (ramanujanTotientVector s) (ramanujanTotientVector (t \ s)) y
      (inverseCore_transpose s) hC
  have htotalmean : ramanujanTotientVector t ⬝ᵥ assemble s t hst x y = 0 := by
    rw [assembled_totient]
    exact hmean
  have hpos := derivedCore_pos_on_totient_kernel t ht (assemble s t hst x y)
    (assemble_ne_zero_of_fresh s t hst x y hy) htotalmean
  rw [assembled_core_quadratic] at hpos
  have he := tangent_core_quadratic (derivedCore s) (derivedCore s)⁻¹
    (crossCore s t hst) (derivedCore (t \ s)) (coreSchur s t hst)
    (ramanujanTotientVector s) (screenedTotient s t hst) y
    (derivedCore_mul_inverse s hs hodd) (inverseCore_transpose s) rfl hC
  change x ⬝ᵥ (derivedCore s *ᵥ x + crossCore s t hst *ᵥ y) +
    y ⬝ᵥ ((crossCore s t hst)ᵀ *ᵥ x + derivedCore (t \ s) *ᵥ y) = _ at he
  rw [he] at hpos
  exact hpos

/-- Removing the negative mean correction makes the ordinary Schur
complement strictly positive. No independent PSD hypothesis is needed. -/
theorem coreSchur_pos (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (y : ↥(t \ s) → ℝ) (hy : y ≠ 0) :
    0 < y ⬝ᵥ (coreSchur s t hst *ᵥ y) := by
  have hs : ∀ q ∈ s, 1 < q := fun q hq => ht q (hst hq)
  have hp := meanTangentSchur_pos s t hst ht hodd y hy
  rw [meanTangentSchur_quadratic] at hp
  have hc : (screenedTotient s t hst ⬝ᵥ y) ^ 2 / inverseCharge s ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (inverseCharge_neg s hs hodd).le
  linarith

theorem coreSchur_det_ne_zero (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    (coreSchur s t hst).det ≠ 0 := by
  intro hd
  obtain ⟨y, hy, hSy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hp := coreSchur_pos s t hst ht hodd y hy
  simp only [hSy, dotProduct_zero] at hp
  exact (lt_irrefl 0) hp

theorem coreSchur_mul_inverse (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    coreSchur s t hst * (coreSchur s t hst)⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (coreSchur_det_ne_zero s t hst ht hodd))

theorem coreSchur_inverse_mul (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    (coreSchur s t hst)⁻¹ * coreSchur s t hst = 1 := by
  exact Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (coreSchur_det_ne_zero s t hst ht hodd))

theorem coreSchur_inverse_transpose (s t : Finset ℕ) (hst : s ⊆ t) :
    ((coreSchur s t hst)⁻¹)ᵀ = (coreSchur s t hst)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, coreSchur_transpose]

/-- Strict positivity transfers to the genuine, proved inverse. -/
theorem coreSchur_inverse_pos (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (w : ↥(t \ s) → ℝ) (hw : w ≠ 0) :
    0 < w ⬝ᵥ ((coreSchur s t hst)⁻¹ *ᵥ w) := by
  let z := (coreSchur s t hst)⁻¹ *ᵥ w
  have hSz : coreSchur s t hst *ᵥ z = w := by
    dsimp only [z]
    rw [Matrix.mulVec_mulVec, coreSchur_mul_inverse s t hst ht hodd,
      Matrix.one_mulVec]
  have hz : z ≠ 0 := by
    intro he
    apply hw
    simpa only [he, Matrix.mulVec_zero] using hSz.symm
  have hp := coreSchur_pos s t hst ht hodd z hz
  rw [hSz, dotProduct_comm] at hp
  exact hp

theorem coreSchur_inverse_nonneg (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (w : ↥(t \ s) → ℝ) :
    0 ≤ w ⬝ᵥ ((coreSchur s t hst)⁻¹ *ᵥ w) := by
  by_cases hw : w = 0
  · simp only [hw, Matrix.mulVec_zero, dotProduct_zero, le_refl]
  · exact (coreSchur_inverse_pos s t hst ht hodd w hw).le

/-- Every actual enlarged inverse-core pairing has the complete block
update, with the entire signed screened source on each side. -/
theorem physical_bilinear_update (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (a c : t → ℝ) :
    a ⬝ᵥ ((derivedCore t)⁻¹ *ᵥ c) =
      (a ∘ oldInclusion s t hst) ⬝ᵥ
        ((derivedCore s)⁻¹ *ᵥ (c ∘ oldInclusion s t hst)) +
      screenedSource (derivedCore s)⁻¹ (crossCore s t hst)
        (a ∘ oldInclusion s t hst) (a ∘ freshInclusion s t) ⬝ᵥ
        ((coreSchur s t hst)⁻¹ *ᵥ
          screenedSource (derivedCore s)⁻¹ (crossCore s t hst)
            (c ∘ oldInclusion s t hst) (c ∘ freshInclusion s t)) := by
  have hs : ∀ q ∈ s, 1 < q := fun q hq => ht q (hst hq)
  have hoddT : ∃ p ∈ t, p.Prime ∧ 2 < p := by
    obtain ⟨p, hps, hp, hpodd⟩ := hodd
    exact ⟨p, hst hps, hp, hpodd⟩
  let z := (derivedCore t)⁻¹ *ᵥ c
  have hfull : derivedCore t *ᵥ z = c := by
    dsimp only [z]
    rw [Matrix.mulVec_mulVec, derivedCore_mul_inverse t ht hoddT,
      Matrix.one_mulVec]
  have hold : derivedCore s *ᵥ (z ∘ oldInclusion s t hst) +
      crossCore s t hst *ᵥ (z ∘ freshInclusion s t) =
        c ∘ oldInclusion s t hst := by
    rw [← old_mulVec, hfull]
  have hnew : (crossCore s t hst)ᵀ *ᵥ (z ∘ oldInclusion s t hst) +
      derivedCore (t \ s) *ᵥ (z ∘ freshInclusion s t) =
        c ∘ freshInclusion s t := by
    rw [← fresh_mulVec, hfull]
  change a ⬝ᵥ z = _
  rw [split_dotProduct s t hst]
  exact solved_block_bilinear_update (derivedCore s) (derivedCore s)⁻¹
    (crossCore s t hst) (derivedCore (t \ s)) (coreSchur s t hst)
    (coreSchur s t hst)⁻¹
    (a ∘ oldInclusion s t hst) (c ∘ oldInclusion s t hst)
    (z ∘ oldInclusion s t hst) (a ∘ freshInclusion s t)
    (c ∘ freshInclusion s t) (z ∘ freshInclusion s t)
    (inverseCore_mul s hs hodd) (inverseCore_transpose s) rfl
    (coreSchur_inverse_mul s t hst ht hodd) hold hnew

/-- Genuine physical A/B/C updates. In particular the middle term retains
`Uᵀ S⁻¹ V` with its sign, and neither screened source is shortened. -/
theorem physical_coupled_source_updates (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    (logarithmicCharge t = logarithmicCharge s +
      screenedLambda s t hst ⬝ᵥ
        ((coreSchur s t hst)⁻¹ *ᵥ screenedLambda s t hst)) ∧
    (mixedCharge t = mixedCharge s +
      screenedLambda s t hst ⬝ᵥ
        ((coreSchur s t hst)⁻¹ *ᵥ screenedTotient s t hst)) ∧
    (inverseCharge t = inverseCharge s +
      screenedTotient s t hst ⬝ᵥ
        ((coreSchur s t hst)⁻¹ *ᵥ screenedTotient s t hst)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [logarithmicCharge, screenedLambda, vonMangoldt_old,
      vonMangoldt_fresh] using
      physical_bilinear_update s t hst ht hodd
        (ramanujanVonMangoldtVector t) (ramanujanVonMangoldtVector t)
  · simpa only [mixedCharge, screenedLambda, screenedTotient, vonMangoldt_old,
      vonMangoldt_fresh, totient_old, totient_fresh] using
      physical_bilinear_update s t hst ht hodd
        (ramanujanVonMangoldtVector t) (ramanujanTotientVector t)
  · simpa only [inverseCharge, screenedTotient, totient_old, totient_fresh] using
      physical_bilinear_update s t hst ht hodd
        (ramanujanTotientVector t) (ramanujanTotientVector t)

/-- The signed mixed update satisfies actual physical finite Cauchy--Schwarz;
all inverse and PSD premises have been discharged by legal packet inertia. -/
theorem physical_coupling_cauchy (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    (mixedCharge t - mixedCharge s) ^ 2 ≤
      (logarithmicCharge t - logarithmicCharge s) *
        (inverseCharge t - inverseCharge s) := by
  obtain ⟨hA, hB, hC⟩ := physical_coupled_source_updates s t hst ht hodd
  exact cauchy_of_coupled_updates (coreSchur s t hst)⁻¹
    (screenedLambda s t hst) (screenedTotient s t hst)
    (logarithmicCharge s) (logarithmicCharge t)
    (mixedCharge s) (mixedCharge t) (inverseCharge s) (inverseCharge t)
    (coreSchur_inverse_transpose s t hst)
    (coreSchur_inverse_nonneg s t hst ht hodd) hA hB hC

theorem logarithmicCharge_mono (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    logarithmicCharge s ≤ logarithmicCharge t := by
  have hA := (physical_coupled_source_updates s t hst ht hodd).1
  rw [hA]
  exact le_add_of_nonneg_right (coreSchur_inverse_nonneg s t hst ht hodd _)

theorem inverseCharge_schur_mono (s t : Finset ℕ) (hst : s ⊆ t)
    (ht : ∀ q ∈ t, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    inverseCharge s ≤ inverseCharge t := by
  have hC := (physical_coupled_source_updates s t hst ht hodd).2.2
  rw [hC]
  exact le_add_of_nonneg_right (coreSchur_inverse_nonneg s t hst ht hodd _)

/-- The actual mixed charge is strictly below `-π`, from complete Gram
positivity on the old inverse-totient vector. -/
theorem mixedCharge_lt_neg_pi (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    mixedCharge s < -Real.pi := by
  let w := (derivedCore s)⁻¹ *ᵥ ramanujanTotientVector s
  have hFw : derivedCore s *ᵥ w = ramanujanTotientVector s := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, derivedCore_mul_inverse s hs hodd,
      Matrix.one_mulVec]
  have hC := inverseCharge_neg s hs hodd
  have hw : w ≠ 0 := by
    intro he
    have hc0 : inverseCharge s = 0 := by
      change ramanujanTotientVector s ⬝ᵥ w = 0
      rw [he, dotProduct_zero]
    exact (ne_of_lt hC) hc0
  have hquad : w ⬝ᵥ (derivedCore s *ᵥ w) = inverseCharge s := by
    rw [hFw, dotProduct_comm]
    rfl
  have hg := gram_quadratic_pos s hs w hw
  rw [gram_quadratic_eq_core, hquad] at hg
  change 0 < Real.pi * inverseCharge s + mixedCharge s * inverseCharge s at hg
  have hmul : 0 < inverseCharge s * (Real.pi + mixedCharge s) := by
    nlinarith only [hg]
  have hsum : Real.pi + mixedCharge s < 0 := by
    by_contra h
    have hn := mul_nonpos_of_nonpos_of_nonneg hC.le (le_of_not_gt h)
    exact (not_lt_of_ge hn) hmul
  linarith

/-- The positive denominator `α=-A` is an actual finite physical fact,
not an extra hypothesis of the later source-limit specialization. -/
theorem logarithmicCharge_neg (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    logarithmicCharge s < 0 := by
  let v := (derivedCore s)⁻¹ *ᵥ ramanujanVonMangoldtVector s
  have hFv : derivedCore s *ᵥ v = ramanujanVonMangoldtVector s := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec, derivedCore_mul_inverse s hs hodd,
      Matrix.one_mulVec]
  have hpair : ramanujanTotientVector s ⬝ᵥ v = mixedCharge s := by
    dsimp only [v, mixedCharge]
    simpa only [inverseCore_transpose s] using
      Matrix.dotProduct_transpose_mulVec (derivedCore s)⁻¹
        (ramanujanTotientVector s) (ramanujanVonMangoldtVector s)
  have hB := mixedCharge_lt_neg_pi s hs hodd
  have hBneg : mixedCharge s < 0 :=
    lt_trans hB (neg_lt_zero.mpr Real.pi_pos)
  have hv : v ≠ 0 := by
    intro he
    have hb0 : mixedCharge s = 0 := by
      rw [← hpair, he, dotProduct_zero]
    exact (ne_of_lt hBneg) hb0
  have hquad : v ⬝ᵥ (derivedCore s *ᵥ v) = logarithmicCharge s := by
    rw [hFv, dotProduct_comm]
    rfl
  have hg := gram_quadratic_pos s hs v hv
  rw [gram_quadratic_eq_core, hquad, hpair] at hg
  change 0 < Real.pi * logarithmicCharge s +
    logarithmicCharge s * mixedCharge s at hg
  have hmul : 0 < logarithmicCharge s * (Real.pi + mixedCharge s) := by
    nlinarith only [hg]
  have hsum : Real.pi + mixedCharge s < 0 := by linarith
  by_contra h
  have hn := mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt h) hsum.le
  exact (not_lt_of_ge hn) hmul

/-- Positivity of the genuine complete Gram gives the full shifted
determinant, including the signed mixed correction, a positive value. -/
theorem shiftedDeterminant_pos (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    0 < shiftedDeterminant s := by
  let A := logarithmicCharge s
  let B := mixedCharge s
  let C := inverseCharge s
  let D := 2 * Real.pi + B
  let tau := D / C
  let v := (derivedCore s)⁻¹ *ᵥ ramanujanVonMangoldtVector s
  let w := (derivedCore s)⁻¹ *ᵥ ramanujanTotientVector s
  let u := v - tau • w
  have hC : C < 0 := inverseCharge_neg s hs hodd
  have hC0 : C ≠ 0 := ne_of_lt hC
  have hFv : derivedCore s *ᵥ v = ramanujanVonMangoldtVector s := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec, derivedCore_mul_inverse s hs hodd,
      Matrix.one_mulVec]
  have hFw : derivedCore s *ᵥ w = ramanujanTotientVector s := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, derivedCore_mul_inverse s hs hodd,
      Matrix.one_mulVec]
  have hphiV : ramanujanTotientVector s ⬝ᵥ v = B := by
    dsimp only [v, B, mixedCharge]
    simpa only [inverseCore_transpose s] using
      Matrix.dotProduct_transpose_mulVec (derivedCore s)⁻¹
        (ramanujanTotientVector s) (ramanujanVonMangoldtVector s)
  have hphiW : ramanujanTotientVector s ⬝ᵥ w = C := rfl
  have hphiU : ramanujanTotientVector s ⬝ᵥ u = -2 * Real.pi := by
    dsimp only [u]
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hphiV, hphiW]
    dsimp only [tau, D]
    rw [div_mul_cancel₀ _ hC0]
    ring
  have hU : u ≠ 0 := by
    intro he
    have hz := hphiU
    rw [he, dotProduct_zero] at hz
    exact Real.pi_ne_zero (by linarith)
  have hqv : v ⬝ᵥ (derivedCore s *ᵥ v) = A := by
    rw [hFv, dotProduct_comm]
    rfl
  have hqw : w ⬝ᵥ (derivedCore s *ᵥ w) = C := by
    rw [hFw, dotProduct_comm]
    rfl
  have hcross : v ⬝ᵥ (derivedCore s *ᵥ w) = B := by
    rw [hFw, dotProduct_comm]
    exact hphiV
  have hquad : u ⬝ᵥ (derivedCore s *ᵥ u) =
      A - 2 * tau * B + tau ^ 2 * C := by
    exact (RiemannResearch.LinearAlgebra.MeanOneCoreInertia.quadratic_sub
      (derivedCore s) (derivedCore_transpose s) v w tau).trans
      (by rw [hqv, hqw, hcross])
  have hLamU : ramanujanVonMangoldtVector s ⬝ᵥ u = A - tau * B := by
    dsimp only [u]
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rfl
  have hGram : u ⬝ᵥ (ramanujanGramMatrix s *ᵥ u) =
      Real.pi * (A * C - D ^ 2) / (-C) := by
    rw [gram_quadratic_eq_core, hquad, hLamU, hphiU]
    dsimp only [tau, D]
    field_simp [hC0]
    ring
  have hp := gram_quadratic_pos s hs u hU
  rw [hGram] at hp
  have hnum := mul_pos hp (neg_pos.mpr hC)
  rw [div_mul_cancel₀ _ (neg_ne_zero.mpr hC0)] at hnum
  exact (mul_pos_iff_of_pos_left Real.pi_pos).mp hnum

theorem sourceProjectionCharge_pos (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    0 < sourceProjectionCharge s := by
  unfold sourceProjectionCharge
  exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (neg_pos.mpr (logarithmicCharge_neg s hs hodd))) (shiftedDeterminant_pos s hs hodd)

/-- The corrected physical source charge is exactly the existing scalar
projection bound; the equality introduces no stronger endpoint estimate. -/
theorem physical_correctedCharge_eq_projectionBound (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    sourceCorrectedCharge s = 4 * Real.pi / sourceProjectionCharge s := by
  have hT : (-logarithmicCharge s) * (-inverseCharge s) -
      (2 * Real.pi + mixedCharge s) ^ 2 ≠ 0 := by
    simpa only [neg_mul_neg, shiftedDeterminant] using
      (ne_of_gt (shiftedDeterminant_pos s hs hodd))
  have hQ : sourceProjectionCharge s = 4 * Real.pi * (-logarithmicCharge s) /
      ((-logarithmicCharge s) * (-inverseCharge s) -
        (2 * Real.pi + mixedCharge s) ^ 2) := by
    simp only [neg_mul_neg, sourceProjectionCharge, shiftedDeterminant]
  exact correctedCharge_eq_projectionBound Real.pi (-logarithmicCharge s)
    (-inverseCharge s) (2 * Real.pi + mixedCharge s) (sourceProjectionCharge s)
    Real.pi_ne_zero (neg_ne_zero.mpr (ne_of_lt (logarithmicCharge_neg s hs hodd))) hT hQ

/-- Conditional analytic specialization to an actual nested physical
chain. Finite signed coupling and `α>0` are proved above; all three source
limits remain explicit premises, and no endpoint equality is concluded. -/
theorem physical_source_limit_bound (packets : ℕ → Finset ℕ) (n : ℕ) (Cinf : ℝ)
    (hnested : ∀ m : ℕ, n ≤ m → packets n ⊆ packets m)
    (hlegal : ∀ m : ℕ, ∀ q ∈ packets m, 1 < q)
    (hodd : ∃ p ∈ packets n, p.Prime ∧ 2 < p)
    (hA : Tendsto (fun m => logarithmicCharge (packets m)) atTop (𝓝 0))
    (hB : Tendsto (fun m => mixedCharge (packets m)) atTop (𝓝 (-2 * Real.pi)))
    (hC : Tendsto (fun m => inverseCharge (packets m)) atTop (𝓝 Cinf)) :
    -Cinf ≤ -inverseCharge (packets n) -
      (2 * Real.pi + mixedCharge (packets n)) ^ 2 /
        (-logarithmicCharge (packets n)) := by
  exact gamma_limit_bound_of_source_limits Real.pi Cinf
    (fun m => logarithmicCharge (packets m)) (fun m => mixedCharge (packets m))
    (fun m => inverseCharge (packets m)) n hA hB hC
    (fun m hnm => physical_coupling_cauchy (packets n) (packets m)
      (hnested m hnm) (hlegal m) hodd)
    (neg_pos.mpr (logarithmicCharge_neg (packets n) (hlegal n) hodd))

end RiemannResearch.RH.Pareto.PhysicalSchurCoupling
