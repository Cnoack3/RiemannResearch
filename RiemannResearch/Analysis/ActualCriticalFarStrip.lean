/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualHuxleyKorobovVinogradov
import RiemannResearch.Analysis.ActualQuasiRiemannSupport

/-!
# Optimized critical weight up to the exact quasi-Riemann boundary

The fixed-abscissa source proposition records the relevant part of
Tao–Trudgian–Yang, ANTEDB Table 11.1, Theorems 11.22 and 11.32.
The second branch is Bourgain's 2000 density theorem. See
https://teorth.github.io/expdb/blueprint/zero-density-chapter.html and
Tao–Trudgian–Yang, *New exponent pairs, zero density estimates, and zero
additive energy estimates*, Math. Comp. 95 (2026), DOI 10.1090/mcom/4138.

The published constants may depend on each fixed abscissa. A finite
mesh turns those estimates into bounds uniform throughout the actual
zero support. At weight exp(2 log T · displacement), the maximum of the
two-piece height exponent occurs at the lower or upper support endpoint.
-/

noncomputable section
open Filter Set Zeta23

namespace RiemannResearch.Analysis.ActualZeroOrdinate

def farDensityCoefficient (σ : ℝ) : ℝ :=
  if σ < 1867 / 2347 then 9 / (8 * (2 * σ - 1)) else 3 / (2 * σ)

/-- Positive-ordinate consequence of the fixed-abscissa estimates on the
part of the half strip used by the critical-weight argument. -/
def TaoBourgainFarDensityHypothesis : Prop :=
  ∀ σ ∈ Icc (25 / 32 : ℝ) (7 / 8), ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ T : ℝ in atTop, rightInclusiveCount T σ ≤ C * T ^ (farDensityCoefficient σ * (1 - σ) + ε)

def farWeightedExcess (σ : ℝ) : ℝ := (farDensityCoefficient σ - 2) * (1 - σ)
private def firstExcess (σ : ℝ) : ℝ := (9 / (8 * (2 * σ - 1)) - 2) * (1 - σ)
/-- Normalized critical-weight exponent for the coefficient 3 / (2σ). -/
def bourgainWeightedExcess (σ : ℝ) : ℝ := (3 / (2 * σ) - 2) * (1 - σ)

/-- The exact endpoint maximum for the two-piece published budget. -/
def farWeightedExcessBudget (σ₀ B : ℝ) : ℝ := max (farWeightedExcess σ₀) (farWeightedExcess B)

private theorem firstExcess_antitone {x y : ℝ}
    (hx : 25 / 32 ≤ x) (hxy : x ≤ y) (hy : y ≤ 7 / 8) : firstExcess y ≤ firstExcess x := by
  have ha : 0 < 2 * x - 1 := by linarith
  have hb : 0 < 2 * y - 1 := by linarith
  have ha' : -1 + x * 2 ≠ 0 := by linarith
  have hb' : -1 + y * 2 ≠ 0 := by linarith
  have hden := mul_le_mul (show 2 * x - 1 ≤ 3 / 4 by linarith)
    (show 2 * y - 1 ≤ 3 / 4 by linarith) hb.le (by norm_num)
  have hratio : 0 ≤ 9 / (8 * (2 * x - 1) * (2 * y - 1)) - 2 := by
    apply sub_nonneg.mpr ((le_div_iff₀ (by positivity)).mpr ?_)
    linarith only [hden]
  have he : firstExcess x - firstExcess y =
      (y - x) * (9 / (8 * (2 * x - 1) * (2 * y - 1)) - 2) := by
    unfold firstExcess
    field_simp [ha.ne', hb.ne', ha', hb']; ring
  exact sub_nonneg.mp (he.symm ▸ mul_nonneg (sub_nonneg.mpr hxy) hratio)

private theorem bourgainWeightedExcess_diff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    bourgainWeightedExcess y - bourgainWeightedExcess x = (y - x) * (2 - 3 / (2 * x * y)) := by
  unfold bourgainWeightedExcess
  field_simp [hx.ne', hy.ne']; ring

/-- The convex rational exponent on the right is controlled by its endpoints. -/
theorem bourgainWeightedExcess_le_endpoints {x y B : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyB : y ≤ B) :
    bourgainWeightedExcess y ≤ max (bourgainWeightedExcess x) (bourgainWeightedExcess B) := by
  have hy := hx.trans_le hxy
  have hB := hy.trans_le hyB
  by_cases hy2 : y * y ≤ 3 / 4
  · have hp := (mul_le_mul_of_nonneg_right hxy hy.le).trans hy2
    have hs : 2 - 3 / (2 * x * y) ≤ 0 := by
      apply sub_nonpos.mpr ((le_div_iff₀ (by positivity)).mpr ?_)
      linarith only [hp]
    have he := bourgainWeightedExcess_diff hx hy
    have hh := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy) hs
    exact (show bourgainWeightedExcess y ≤ bourgainWeightedExcess x by linarith only [he, hh]).trans
      (le_max_left _ _)
  · have hp := (le_of_not_ge hy2).trans (mul_le_mul_of_nonneg_left hyB hy.le)
    have hs : 0 ≤ 2 - 3 / (2 * y * B) := by
      apply sub_nonneg.mpr ((div_le_iff₀ (by positivity)).mpr ?_)
      linarith only [hp]
    have he := bourgainWeightedExcess_diff hy hB
    have hh := mul_nonneg (sub_nonneg.mpr hyB) hs
    exact (show bourgainWeightedExcess y ≤ bourgainWeightedExcess B by linarith only [he, hh]).trans
      (le_max_right _ _)

private theorem bourgainWeightedExcess_le_active {x : ℝ} (hx : 25 / 32 ≤ x) (hx' : x ≤ 7 / 8) :
    bourgainWeightedExcess x ≤ farWeightedExcess x := by
  unfold farWeightedExcess farDensityCoefficient bourgainWeightedExcess
  split_ifs with hb
  · have hp : 0 < 2 * x := by linarith
    have hq : 0 < 8 * (2 * x - 1) := by linarith
    have h := (div_le_div_iff₀ hp hq).mpr (show 3 * (8 * (2 * x - 1)) ≤ 9 * (2 * x) by
      linarith only [hb])
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right h 2) (by linarith)
  · exact le_rfl

theorem farWeightedExcess_le_budget {σ₀ σ B : ℝ}
    (h₀ : 25 / 32 ≤ σ₀) (hσ : σ ∈ Icc σ₀ B) (hB : B ≤ 7 / 8) :
    farWeightedExcess σ ≤ farWeightedExcessBudget σ₀ B := by
  by_cases hb : σ < 1867 / 2347
  · have h₁ : farWeightedExcess σ = firstExcess σ := by
      simp [farWeightedExcess, farDensityCoefficient, firstExcess, hb]
    have h₂ : farWeightedExcess σ₀ = firstExcess σ₀ := by
      simp [farWeightedExcess, farDensityCoefficient, firstExcess, lt_of_le_of_lt hσ.1 hb]
    rw [h₁, farWeightedExcessBudget, h₂]
    exact (firstExcess_antitone h₀ hσ.1 (hσ.2.trans hB)).trans (le_max_left _ _)
  · have h₁ : farWeightedExcess σ = bourgainWeightedExcess σ := by
      simp [farWeightedExcess, farDensityCoefficient, bourgainWeightedExcess, hb]
    rw [h₁, farWeightedExcessBudget]
    exact (bourgainWeightedExcess_le_endpoints (by linarith only [h₀]) hσ.1 hσ.2).trans
      (max_le_max (bourgainWeightedExcess_le_active h₀ (hσ.1.trans (hσ.2.trans hB)))
        (bourgainWeightedExcess_le_active (h₀.trans (hσ.1.trans hσ.2)) hB))

theorem farWeightedExcess_negative {σ : ℝ} (h₀ : 25 / 32 < σ) (hσ : σ ≤ 7 / 8) :
    farWeightedExcess σ < 0 := by
  have hlt : farDensityCoefficient σ < 2 := by
    unfold farDensityCoefficient
    split_ifs
    · exact (div_lt_iff₀ (by linarith : 0 < 8 * (2 * σ - 1))).mpr (by linarith)
    · exact (div_lt_iff₀ (by linarith : 0 < 2 * σ)).mpr (by linarith)
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt) (by linarith)

/-- A finite grid gives one eventual estimate wherever the pointwise
exponent lies below an affine function of slope −2. -/
private theorem uniform_critical_count {lo hi e ε : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) (hε : 0 < ε)
    (hc : ∀ x ∈ Icc lo hi, ∃ D : ℝ, 0 < D ∧ ∀ᶠ T : ℝ in atTop,
      rightInclusiveCount T x ≤ D * T ^ (1 + e - 2 * (x - 1 / 2) + ε / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc lo hi,
      rightInclusiveCount T x * T ^ (2 * (x - 1 / 2)) ≤ C * T ^ (1 + e + ε) := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / ε)
  have hn₀ : 0 < (n : ℝ) := lt_trans (by positivity : 0 < 4 / ε) hn
  have hmesh : 2 / (n : ℝ) < ε / 2 := by
    apply (div_lt_iff₀ hn₀).mpr
    have h := (div_lt_iff₀ hε).mp hn
    linarith only [h]
  let grid (i : Fin (n + 1)) : ℝ := min hi (lo + (i.val : ℝ) / n)
  have hgrid (i : Fin (n + 1)) : grid i ∈ Icc lo hi :=
    ⟨le_min hlohi (le_add_of_nonneg_right (by positivity)), min_le_left _ _⟩
  choose D hD hb using fun i : Fin (n + 1) => hc _ (hgrid i)
  let C := 1 + ∑ i : Fin (n + 1), D i
  have hsum : 0 ≤ ∑ i : Fin (n + 1), D i := Finset.sum_nonneg (fun i _ => (hD i).le)
  have hC : 0 < C := by dsimp [C]; linarith only [hsum]
  refine ⟨C, hC, ?_⟩
  have hall : ∀ᶠ T : ℝ in atTop, ∀ i : Fin (n + 1), rightInclusiveCount T (grid i) ≤
      D i * T ^ (1 + e - 2 * (grid i - 1 / 2) + ε / 2) := Filter.eventually_all.mpr hb
  filter_upwards [hall, eventually_ge_atTop (1 : ℝ)] with T hT hT₁
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT₁
  intro x hx
  let z := (x - lo) * (n : ℝ)
  have hz : 0 ≤ z := mul_nonneg (sub_nonneg.mpr hx.1) hn₀.le
  have hzn : z ≤ (n : ℝ) := by
    change (x - lo) * n ≤ n
    nlinarith only [mul_nonneg (show 0 ≤ 1 - (x - lo) by linarith only [hx.2, hhi, hlo]) hn₀.le]
  have hk := Nat.floor_le hz
  have hk' := Nat.lt_floor_add_one z
  have hkn : ⌊z⌋₊ ≤ n := by exact_mod_cast hk.trans hzn
  let i : Fin (n + 1) := ⟨⌊z⌋₊, Nat.lt_succ_of_le hkn⟩
  have hgx : lo + (i.val : ℝ) / n ≤ x := by
    have h : (i.val : ℝ) / n ≤ x - lo := (div_le_iff₀ hn₀).mpr hk
    linarith
  have heq : grid i = lo + (i.val : ℝ) / n := min_eq_right (hgx.trans hx.2)
  have hg : x - grid i < 1 / n := by
    rw [heq]
    have h : x - lo < ((i.val : ℝ) + 1) / n := (lt_div_iff₀ hn₀).mpr hk'
    rw [add_div] at h
    linarith
  have hDC : D i ≤ C := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hD j).le) (Finset.mem_univ i)
    dsimp [C]; linarith only [h]
  have htwo : 2 * (x - grid i) < 2 / n := by
    calc
      _ < 2 * (1 / (n : ℝ)) := mul_lt_mul_of_pos_left hg (by norm_num)
      _ = _ := by ring
  calc
    _ ≤ (D i * T ^ (1 + e - 2 * (grid i - 1 / 2) + ε / 2)) * T ^ (2 * (x - 1 / 2)) :=
      mul_le_mul_of_nonneg_right ((rightInclusiveCount_antitone T (heq.trans_le hgx)).trans (hT i))
        (Real.rpow_nonneg hTp.le _)
    _ = D i * T ^ ((1 + e - 2 * (grid i - 1 / 2) + ε / 2) + 2 * (x - 1 / 2)) := by
      rw [mul_assoc, ← Real.rpow_add hTp]
    _ ≤ _ := mul_le_mul hDC (Real.rpow_le_rpow_of_exponent_le hT₁ (by linarith only [htwo, hmesh]))
      (Real.rpow_nonneg hTp.le _) hC.le

/-- Positive-ordinate inclusive tails vanish strictly to the right of
the quasi-Riemann boundary. Zeros at the boundary need no exclusion. -/
theorem rightInclusiveCount_eq_zero_of_zeroFreeHalfPlane {B σ : ℝ}
    (h : ZetaZeroFreeHalfPlane B) (hσ : B < σ) (T : ℝ) : rightInclusiveCount T σ = 0 := by
  classical
  unfold rightInclusiveCount realSum
  apply Finset.sum_eq_zero
  intro ρ hρ
  have ha := displacement_le_of_zeroFreeHalfPlane h hρ
  have hb := (abs_le.mp ha).2
  have hlt : ρ.re < σ := by linarith only [hb, hσ]
  simp only [if_neg (not_le.mpr hlt), mul_zero]

/-- Uniform weighted-count estimate across a compact portion of the strip.
No fixed zero-free support is required for this intermediate result. -/
theorem weighted_compact_count_of_farDensity {B σ₀ : ℝ}
    (hD : TaoBourgainFarDensityHypothesis) (h₀ : 25 / 32 < σ₀)
    (h₀B : σ₀ ≤ B) (hB : B ≤ 7 / 8) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc σ₀ B,
      rightInclusiveCount T x * T ^ (2 * (x - 1 / 2)) ≤
        C * T ^ (1 + farWeightedExcessBudget σ₀ B + ε) := by
  let E := farWeightedExcessBudget σ₀ B
  have hc (x : ℝ) (hx : x ∈ Icc σ₀ B) : ∃ D : ℝ, 0 < D ∧ ∀ᶠ T : ℝ in atTop,
      rightInclusiveCount T x ≤ D * T ^ (1 + E - 2 * (x - 1 / 2) + ε / 2) := by
    obtain ⟨D, hD', he⟩ := hD x ⟨h₀.le.trans hx.1, hx.2.trans hB⟩ (ε / 2) (by linarith)
    refine ⟨D, hD', ?_⟩
    filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with T hT hT₁
    have hweight := farWeightedExcess_le_budget h₀.le hx hB
    change (farDensityCoefficient x - 2) * (1 - x) ≤ E at hweight
    apply hT.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT₁ ?_) hD'.le)
    linarith only [hweight]
  exact uniform_critical_count (by linarith only [h₀]) h₀B (by linarith only [hB]) hε hc

/-- Transfer any uniform compact weighted count budget to the complete mass
when a fixed zero-free half-plane supplies the upper support. -/
theorem normalized_critical_weight_of_compact_count {B σ₀ e : ℝ}
    (hZ : ZetaZeroFreeHalfPlane B) (h₀ : 1 / 2 ≤ σ₀) (h₀B : σ₀ ≤ B) (hB : B ≤ 1)
    (hc : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc σ₀ B,
      rightInclusiveCount T σ * T ^ (2 * (σ - 1 / 2)) ≤ C * T ^ (1 + e)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      badWeightedSum T (σ₀ - 1 / 2) (fun t => Real.exp (2 * Real.log T * t)) /
        (Ncount 0 T : ℝ) ≤ C * T ^ e := by
  obtain ⟨C, hC, he⟩ := hc
  refine ⟨64 * Real.pi * C, by positivity, ?_⟩
  filter_upwards [he, eventually_count_ge_log, eventually_ge_atTop (Real.exp 1)] with T hT hN hE
  have hTp := (Real.exp_pos _).trans_le hE
  have hall (σ : ℝ) (hσ : σ ∈ Icc (1 / 2 + (σ₀ - 1 / 2)) 1) :
      rightInclusiveCount T σ * T ^ (2 * (σ - 1 / 2)) ≤ (C * T ^ e) * T := by
    by_cases hb : σ ≤ B
    · have h := hT σ ⟨by linarith only [hσ.1], hb⟩
      rw [show 1 + e = e + 1 by ring, Real.rpow_add hTp, Real.rpow_one] at h
      simpa only [mul_assoc] using h
    · rw [rightInclusiveCount_eq_zero_of_zeroFreeHalfPlane hZ (lt_of_not_ge hb), zero_mul]
      positivity
  have h := normalized_critical_weight_of_count (δ := σ₀ - 1 / 2)
    ⟨sub_nonneg.mpr h₀, by linarith only [h₀B, hB]⟩ hE
    (show 0 ≤ C * T ^ e by positivity) hN hall
  simpa only [mul_assoc] using h

theorem normalized_critical_weight_of_farDensity {B σ₀ : ℝ}
    (hZ : ZetaZeroFreeHalfPlane B) (hD : TaoBourgainFarDensityHypothesis)
    (h₀ : 25 / 32 < σ₀) (h₀B : σ₀ ≤ B) (hB : B ≤ 7 / 8) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      badWeightedSum T (σ₀ - 1 / 2) (fun t => Real.exp (2 * Real.log T * t)) /
        (Ncount 0 T : ℝ) ≤ C * T ^ (farWeightedExcessBudget σ₀ B + ε) := by
  apply normalized_critical_weight_of_compact_count hZ (by linarith only [h₀]) h₀B
    (by linarith only [hB])
  simpa only [add_assoc] using weighted_compact_count_of_farDensity hD h₀ h₀B hB hε

/-- For every displacement strictly greater than 9/32 and up to the
exact support, every power strictly below the two-endpoint margin is saved. -/
theorem normalized_critical_weight_power_saving_at_continuumContact
    (hZ : ContinuumContactNonvanishing) (hD : TaoBourgainFarDensityHypothesis)
    {δ : ℝ} (hδ : 9 / 32 < δ) (hB : 1 / 2 + δ ≤ continuumContact) :
    0 < -farWeightedExcessBudget (1 / 2 + δ) continuumContact ∧
    ∀ η : ℝ, 0 < η → η < -farWeightedExcessBudget (1 / 2 + δ) continuumContact →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
        badWeightedSum T δ (fun t => Real.exp (2 * Real.log T * t)) / (Ncount 0 T : ℝ) ≤
          C * T ^ (-η) := by
  have hlo : 25 / 32 < 1 / 2 + δ := by linarith only [hδ]
  have hhi := continuumContact_mem.2.le
  have hm : farWeightedExcessBudget (1 / 2 + δ) continuumContact < 0 :=
    max_lt (farWeightedExcess_negative hlo (hB.trans hhi))
      (farWeightedExcess_negative (hlo.trans_le hB) hhi)
  refine ⟨neg_pos.mpr hm, ?_⟩
  intro η _hη he
  let ε := -farWeightedExcessBudget (1 / 2 + δ) continuumContact - η
  have hε : 0 < ε := sub_pos.mpr he
  have h := normalized_critical_weight_of_farDensity hZ hD hlo hB hhi hε
  have hexp : farWeightedExcessBudget (1 / 2 + δ) continuumContact + ε = -η := by dsimp [ε]; ring
  simpa only [hexp, add_sub_cancel_left] using h

/-- Every ordinary power saving dominates a prescribed logarithmic saving. -/
theorem eventually_rpow_le_log_neg {e : ℝ} (he : e < 0) (A : ℝ) :
    ∀ᶠ T : ℝ in atTop, T ^ e ≤ (Real.log T) ^ (-A) := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := -e) A (neg_pos.mpr he)).bound zero_lt_one
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with T hT hT₁
  have hTp : 0 < T := zero_lt_one.trans hT₁
  have hL := Real.log_pos hT₁
  change ‖(Real.log T) ^ A‖ ≤ 1 * ‖T ^ (-e)‖ at hT
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL _), abs_of_pos (Real.rpow_pos_of_pos hTp _),
    Real.rpow_neg hTp.le] at hT
  rw [Real.rpow_neg hL.le]
  exact (le_inv_comm₀ (Real.rpow_pos_of_pos hTp _ ) (Real.rpow_pos_of_pos hL _)).mpr hT

/-- A genuine power saving on the compact shoulder and classical Huxley–VK
beyond 7/8 give a logarithmic saving over the complete finite support. -/
theorem normalized_critical_weight_superlog_of_compact_count {δ e : ℝ}
    (hδ : δ ∈ Icc (0 : ℝ) (1 / 2)) (he : e < 0)
    (hc : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ Icc (1 / 2 + δ) (7 / 8),
      rightInclusiveCount T σ * T ^ (2 * (σ - 1 / 2)) ≤ C * T ^ (1 + e))
    (hH : HuxleyDensityHypothesis) (hv : BellottiKorobovVinogradovCount) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      badWeightedSum T δ (fun t => Real.exp (2 * Real.log T * t)) / (Ncount 0 T : ℝ) ≤
        C * (Real.log T) ^ (-A) := by
  obtain ⟨C, hC, hc⟩ := hc
  obtain ⟨D, hD', hd⟩ := weighted_huxley_count_superlog hH hv (σ₀ := (7 / 8 : ℝ)) (by norm_num) A hA
  let K := max C D
  have hK : 0 < K := hC.trans_le (le_max_left _ _)
  refine ⟨64 * Real.pi * K, by positivity, ?_⟩
  filter_upwards [hc, hd, eventually_rpow_le_log_neg he A,
    eventually_count_ge_log, eventually_ge_atTop (Real.exp 1)] with T hcT hdT hpow hN hexp
  have hTp := (Real.exp_pos _).trans_le hexp
  have hL : 0 < Real.log T := lt_of_lt_of_le zero_lt_one
    (by simpa using Real.log_le_log (Real.exp_pos _) hexp)
  have hall (σ : ℝ) (hσ : σ ∈ Icc (1 / 2 + δ) 1) :
      rightInclusiveCount T σ * T ^ (2 * (σ - 1 / 2)) ≤ (K * (Real.log T) ^ (-A)) * T := by
    by_cases hs : σ ≤ 7 / 8
    · have h := hcT σ ⟨hσ.1, hs⟩
      rw [show 1 + e = e + 1 by ring, Real.rpow_add hTp, Real.rpow_one] at h
      apply h.trans
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hTp.le
      exact mul_le_mul (le_max_left _ _) hpow (Real.rpow_nonneg hTp.le _) hK.le
    · have h := hdT σ ⟨(lt_of_not_ge hs).le, hσ.2⟩
      calc
        _ ≤ _ := h
        _ = D * (Real.log T) ^ (-A) * T := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hL.le _)) hTp.le
  have h := normalized_critical_weight_of_count (δ := δ) hδ hexp
    (show 0 ≤ K * (Real.log T) ^ (-A) by positivity) hN hall
  simpa only [mul_assoc] using h

/-- TTY/Bourgain handles the compact shoulder up to 7/8; Huxley and
the Vinogradov–Korobov region handle the remaining moving abscissae.
This proof obtains every logarithmic saving above 9/32 without a
quasi-Riemann half-plane assumption. -/
theorem normalized_critical_weight_superlog_of_farDensity
    (hD : TaoBourgainFarDensityHypothesis) (hH : HuxleyDensityHypothesis)
    (hv : BellottiKorobovVinogradovCount) {δ : ℝ} (hδ : δ ∈ Ioc (9 / 32 : ℝ) (1 / 2))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      badWeightedSum T δ (fun t => Real.exp (2 * Real.log T * t)) / (Ncount 0 T : ℝ) ≤
        C * (Real.log T) ^ (-A) := by
  by_cases hhigh : 1 / 3 < δ
  · exact normalized_critical_weight_superlog_of_huxley hH hv ⟨hhigh, hδ.2⟩ A hA
  let lo := 1 / 2 + δ
  let hi := (7 / 8 : ℝ)
  have hlo : 25 / 32 < lo := by dsimp [lo]; linarith only [hδ.1]
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith only [le_of_not_gt hhigh]
  let E := farWeightedExcessBudget lo hi
  have hE : E < 0 := max_lt (farWeightedExcess_negative hlo hlohi)
    (farWeightedExcess_negative (hlo.trans_le hlohi) le_rfl)
  have he : E / 2 < 0 := by linarith
  apply normalized_critical_weight_superlog_of_compact_count ⟨by linarith only [hδ.1], hδ.2⟩ he
    _ hH hv A hA
  have hc := weighted_compact_count_of_farDensity hD hlo hlohi (by rfl : hi ≤ 7 / 8)
    (show 0 < -E / 2 by linarith)
  have hexp : 1 + farWeightedExcessBudget lo hi + -E / 2 = 1 + E / 2 := by
    change 1 + E + -E / 2 = 1 + E / 2
    ring
  simpa only [hexp] using hc

end RiemannResearch.Analysis.ActualZeroOrdinate
