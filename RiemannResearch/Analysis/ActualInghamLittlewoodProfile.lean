/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamSharpDensity
import RiemannResearch.Analysis.ActualSelbergDensityAssembly
import RiemannResearch.Analysis.InghamInterpolationParameters

/-!
# Uniform exponents in the Gabriel–Littlewood count

The single interpolation line may lie anywhere in the logarithmic collar
selected by Littlewood's lemma. Its height exponent differs from the limiting
one by at most a constant divided by the logarithm of the height. We also
absorb the count at a fixed lower height and treat every height down to two.
-/

noncomputable section
open Set Zeta23
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- Move the interpolating line and the right endpoint by at most two
logarithmic units each; the resulting product of powers costs one absolute
multiplicative constant. -/
theorem ingham_shifted_moment_le_profile {T σ α η : ℝ}
    (hT : 1 ≤ T) (hL : 1 ≤ Real.log T) (hσ : σ ∈ Icc (1 / 2 : ℝ) 1)
    (hα : α ∈ Icc (1 / 2 : ℝ) σ) (hδ : (σ - α) * Real.log T ≤ 2)
    (hη : 0 ≤ η) (hηL : η * Real.log T ≤ 2) :
    let θ := (α - 1 / 2) / (1 + η - 1 / 2)
    let q := 3 * (1 - σ) / (2 - σ)
    let A := 3 * (1 - θ) / (3 - θ)
    T ^ A * (Real.log T) ^ (1 + A) ≤
      Real.exp 24 * (T ^ q * (Real.log T) ^ (1 + q)) := by
  intro θ q A
  let c := 3 * η + 3 * (σ - α)
  let L := Real.log T
  have hp : 0 < T := by linarith
  have hlp : 0 < L := by dsimp [L]; linarith
  have hα1 := hα.2.trans hσ.2
  have he : 0 < 1 + η - 1 / 2 := by linarith
  have ht : θ ≤ 1 := (div_le_iff₀ he).mpr (by linarith)
  have ht3 : 0 < 3 - θ := by linarith
  have hden : 0 < 2 + 3 * η - α := by linarith
  have hA : A = 3 * (1 + η - α) / (2 + 3 * η - α) := by
    apply (div_eq_div_iff ht3.ne' hden.ne').mpr
    have ht' : θ * (1 + η - 1 / 2) = α - 1 / 2 := div_mul_cancel₀ _ he.ne'
    nlinarith only [ht']
  have hda : 1 ≤ 2 - α := by linarith
  have hds : 1 ≤ 2 - σ := by linarith [hσ.2]
  have hqa : 3 * (1 - α) / (2 - α) - q =
      3 * (σ - α) / ((2 - α) * (2 - σ)) := by
    dsimp [q]
    field_simp [show 2 - α ≠ 0 by linarith, show 2 - σ ≠ 0 by linarith]
    ring
  have hqa' : 3 * (1 - α) / (2 - α) - q ≤ 3 * (σ - α) := by
    rw [hqa]
    exact div_le_self (by nlinarith [hα.2]) (one_le_mul_of_one_le_of_one_le hda hds)
  have hAc : A ≤ q + c := by
    rw [hA]
    have hm := InghamInterpolation.moving_height_exponent_le hη
      (show α ∈ Icc (1 / 2 : ℝ) 1 from ⟨hα.1, hα1⟩)
    dsimp [c]; linarith
  have hc : 0 ≤ c := by dsimp [c]; linarith [hα.2]
  have hcL : c * L ≤ 12 := by dsimp [c, L]; nlinarith only [hδ, hηL]
  have hbase : 1 ≤ T * L := one_le_mul_of_one_le_of_one_le hT hL
  have hbp : 0 < T * L := mul_pos hp hlp
  have hlog : Real.log (T * L) ≤ 2 * L := by
    rw [Real.log_mul hp.ne' hlp.ne']
    change L + Real.log L ≤ 2 * L
    linarith [Real.log_le_sub_one_of_pos hlp]
  have hcost : (T * L) ^ c ≤ Real.exp 24 := by
    rw [Real.rpow_def_of_pos hbp]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hlog hc, hcL]
  have hpow : (T * L) ^ A ≤ (T * L) ^ q * Real.exp 24 := calc
    _ ≤ (T * L) ^ (q + c) := Real.rpow_le_rpow_of_exponent_le hbase hAc
    _ = (T * L) ^ q * (T * L) ^ c := Real.rpow_add hbp _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg hbp.le _)
  have hprod (a : ℝ) : T ^ a * L ^ (1 + a) = (T * L) ^ a * L := by
    rw [Real.rpow_add hlp, Real.rpow_one, Real.mul_rpow hp.le hlp.le]; ring
  change T ^ A * L ^ (1 + A) ≤ Real.exp 24 * (T ^ q * L ^ (1 + q))
  rw [hprod, hprod]
  exact (mul_le_mul_of_nonneg_right hpow hlp.le).trans_eq (by ring)

/-- A uniform fixed-lower-height rectangle count, with the actual
Gabriel exponent on the selected left edge, gives the global Ingham
profile with log exponent `2+q`. -/
theorem exists_ingham_littlewood_profile_of_comparable_count
    {D : ℝ} (hD : 0 < D)
    (hwindow : ∀ {X : ℕ}, 72 ≤ X → ∀ {H T σ : ℝ},
      4 ≤ H → H ≤ T → (X : ℝ) ≤ T → T ≤ 2 * (X : ℝ) → 1 ≤ Real.log T →
      1 / 2 + 2 / (Real.log T) ≤ σ → σ ≤ 1 →
      ∃ a ∈ Ioo (σ - 2 / Real.log T) (σ - 1 / Real.log T),
        let β := 1 + 1 / Real.log (X : ℝ)
        let θ := (a - 1 / 2) / (β - 1 / 2)
        let A := 3 * (1 - θ) / (3 - θ)
        rightInclusiveCount T σ - rightInclusiveCount H σ ≤
          D * Real.log T * (T ^ A * (Real.log T) ^ (1 + A) + Real.log T)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
      let q := 3 * (1 - σ) / (2 - σ)
      rightInclusiveCount T σ ≤ C * min (T * Real.log T) (T ^ q * (Real.log T) ^ (2 + q)) := by
  obtain ⟨P, hP, hprev⟩ := exists_ingham_density_sharp_all_heights
  obtain ⟨K, hK, hthin⟩ := exists_selberg_form_on_logarithmic_strip 2 2 (by norm_num)
  let B := (Ncount 0 4 : ℝ) + D * (Real.exp 24 + 1)
  let C := max (max (16 * P) K) B
  have hPC : 16 * P ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hKC : K ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hBC : B ≤ C := le_max_right _ _
  have hC := hK.trans_le hKC
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ q
  let L := Real.log T
  let W := T ^ q * L ^ (2 + q)
  have hp : 0 < T := by linarith
  have hp1 : 1 ≤ T := by linarith
  have hL : 0 < L := Real.log_pos (by linarith)
  have hden : 0 < 2 - σ := by linarith [hσ.2]
  have hq : 0 ≤ q := div_nonneg (by linarith [hσ.2]) hden.le
  have hW : 0 ≤ W := mul_nonneg (Real.rpow_nonneg hp.le _) (Real.rpow_nonneg hL.le _)
  have hP' := hprev T hT σ hσ
  rw [mul_min_of_nonneg _ _ hC.le]
  refine le_min ?_ ?_
  · have hc : P ≤ C := by linarith
    exact (hP'.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hP.le)).trans
      (mul_le_mul_of_nonneg_right hc (mul_nonneg hp.le hL.le))
  change rightInclusiveCount T σ ≤ C * W
  by_cases hlarge : Real.exp 16 ≤ T
  · have hL16 : 16 ≤ L := by simpa [L] using Real.log_le_log (Real.exp_pos 16) hlarge
    have hL1 : 1 ≤ L := by linarith
    have hTq : 1 ≤ T ^ q := Real.one_le_rpow hp1 hq
    have hT72 : 72 ≤ T := by
      have h8 := Real.add_one_le_exp 8
      have h16 : Real.exp 16 = Real.exp 8 * Real.exp 8 := by norm_num [← Real.exp_add]
      nlinarith only [hlarge, h16, h8, sq_nonneg (Real.exp 8 - 9)]
    have hLsq : L ^ (2 : ℕ) ≤ W := by
      have hs : L ^ (2 : ℝ) ≤ L ^ (2 + q) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      rw [Real.rpow_two] at hs
      exact hs.trans (le_mul_of_one_le_left (Real.rpow_nonneg hL.le _) hTq)
    have hW1 : 1 ≤ W := (one_le_pow₀ hL1).trans hLsq
    by_cases hband : 2 ≤ (σ - 1 / 2) * L
    · let X : ℕ := ⌊T⌋₊
      have hx : (X : ℝ) ≤ T := Nat.floor_le hp.le
      have hx72 : 72 ≤ X := (Nat.le_floor_iff hp.le).mpr hT72
      have hx72r : (72 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hx72
      have hXp : 0 < (X : ℝ) := by linarith
      have hxT : T ≤ 2 * (X : ℝ) := by linarith [show T < (X : ℝ) + 1 from Nat.lt_floor_add_one _]
      have hgap : 1 / 2 + 2 / L ≤ σ := by linarith [(div_le_iff₀ hL).mpr hband]
      obtain ⟨α, hα, hb⟩ := hwindow hx72 (H := 4) (T := T) (σ := σ)
        (by norm_num) (by linarith) hx hxT hL1 hgap hσ.2
      let η := 1 / Real.log (X : ℝ)
      have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
      have hη : 0 ≤ η := by dsimp [η]; positivity
      have hLX : L ≤ 2 * Real.log (X : ℝ) := by
        apply (Real.log_le_log hp hxT).trans
        rw [Real.log_mul (by norm_num) hXp.ne']
        linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (show (2 : ℝ) ≤ (X : ℝ) by linarith)]
      have hηL : η * L ≤ 2 := by
        rw [show η * L = L / Real.log (X : ℝ) by dsimp [η]; ring]
        exact (div_le_iff₀ hlogX).mpr hLX
      have hshift : α ∈ Icc (1 / 2 : ℝ) σ := by
        constructor
        · linarith [hα.1]
        · linarith [hα.2, one_div_pos.mpr hL]
      have hδ : (σ - α) * L ≤ 2 := (le_div_iff₀ hL).mp (by linarith [hα.1])
      have he := ingham_shifted_moment_le_profile hp1 hL1 hσ hshift hδ hη hηL
      let θ := (α - 1 / 2) / (1 + η - 1 / 2)
      let A := 3 * (1 - θ) / (3 - θ)
      change T ^ A * L ^ (1 + A) ≤ Real.exp 24 * (T ^ q * L ^ (1 + q)) at he
      change rightInclusiveCount T σ - rightInclusiveCount 4 σ ≤
        D * L * (T ^ A * L ^ (1 + A) + L) at hb
      have hprod : L * (T ^ q * L ^ (1 + q)) = W := by
        dsimp [W]
        rw [show 2 + q = 1 + (1 + q) by ring, Real.rpow_add hL 1 (1 + q), Real.rpow_one]
        ring
      have hmain : rightInclusiveCount T σ - rightInclusiveCount 4 σ ≤ D * (Real.exp 24 + 1) * W := by
        calc
          _ ≤ D * L * (Real.exp 24 * (T ^ q * L ^ (1 + q)) + L) :=
            hb.trans (mul_le_mul_of_nonneg_left (add_le_add he le_rfl) (mul_nonneg hD.le hL.le))
          _ = D * (Real.exp 24 * W + L ^ (2 : ℕ)) := by rw [← hprod]; ring
          _ ≤ D * (Real.exp 24 * W + W) := by gcongr
          _ = D * (Real.exp 24 + 1) * W := by ring
      have hlow : rightInclusiveCount 4 σ ≤ (Ncount 0 4 : ℝ) * W :=
        (rightInclusiveCount_le_count 4 σ).trans (le_mul_of_one_le_right (by positivity) hW1)
      exact (show rightInclusiveCount T σ ≤ B * W by dsimp [B]; linarith only [hmain, hlow]).trans
        (mul_le_mul_of_nonneg_right hBC hW)
    · have hh := hthin T (by linarith) σ (le_of_not_ge hband)
      have he : 1 - 2 * (σ - 1 / 2) ≤ q := (le_div_iff₀ hden).mpr (by
        nlinarith [mul_nonneg (sub_nonneg.mpr hσ.1) (sub_nonneg.mpr hσ.2)])
      have hTp := Real.rpow_le_rpow_of_exponent_le hp1 he
      have hlogp : L ≤ L ^ (2 + q) := by
        simpa using (Real.rpow_le_rpow_of_exponent_le hL1 (show (1 : ℝ) ≤ 2 + q by linarith))
      have hh' : rightInclusiveCount T σ ≤ K * W := by
        apply hh.trans
        change K * T ^ (1 - 2 * (σ - 1 / 2)) * L ≤ K * (T ^ q * L ^ (2 + q))
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hTp hlogp hL.le (Real.rpow_nonneg hp.le _)) hK.le
      exact hh'.trans (mul_le_mul_of_nonneg_right hKC hW)
  · have hL16 : L ≤ 16 := by simpa [L] using Real.log_le_log hp (le_of_not_ge hlarge)
    have hs : T ^ q * L ^ (3 + q) = L * W := by
      dsimp [W]; rw [show 3 + q = 1 + (2 + q) by ring, Real.rpow_add hL, Real.rpow_one]; ring
    have hh := hP'.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hP.le)
    change rightInclusiveCount T σ ≤ P * (T ^ q * L ^ (3 + q)) at hh
    rw [hs] at hh
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hL16 (mul_nonneg hP.le hW),
                                       mul_le_mul_of_nonneg_right hPC hW])

end RiemannResearch.Analysis.ActualZeroOrdinate
