/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoResidueCriticalGram
import RiemannResearch.RH.ParetoResidueZeroNormal
import RiemannResearch.RH.MellinCriticalPoint
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Real zero certificates and their inverse-log limit

The exact zero normal equations supply a canonical certificate at every
stage, including singular stages. For fixed distinct positive ordinates
the normalized real Gram has an invertible diagonal limit. This applies
Burnol's finite zero projection strategy to the physical residue quotient
with its complete multiples source correction.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin
open RiemannResearch.Analysis.FiniteHilbertGram
open MellinFrequency (criticalPoint)

/-- Extract the real Gram entry from the difference and sum coefficients. -/
def crossPart (b c : Bool) : ℂ × ℂ →L[ℝ] ℝ :=
  let r₁ := Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)
  let r₂ := Complex.reCLM.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)
  let i₁ := Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℂ)
  let i₂ := Complex.imCLM.comp (ContinuousLinearMap.snd ℝ ℂ ℂ)
  match b, c with
  | false, false => (1 / 2 : ℝ) • (r₁ + r₂)
  | false, true => (1 / 2 : ℝ) • (i₂ - i₁)
  | true, false => (1 / 2 : ℝ) • (i₁ + i₂)
  | true, true => (1 / 2 : ℝ) • (r₁ - r₂)

private theorem crossPart_term (b c : Bool) (x y : ℂ) :
    crossPart b c (x * star y, x * y) = part b x * part c y := by
  cases b <;> cases c <;>
    simp [crossPart, part, Complex.mul_re, Complex.mul_im] <;> ring

theorem crossPart_zero_right (b c : Bool) (v : ℝ) :
    crossPart b c ((v : ℂ), 0) = if b = c then v / 2 else 0 := by
  cases b <;> cases c <;> simp [crossPart, div_eq_mul_inv, mul_comm]

variable {ι : Type*}

/-- The real Gram of the two observations per ordinate, divided by log L. -/
def normalizedCriticalGram (γ : ι → ℝ) (N : ℕ) : Matrix (ι × Bool) (ι × Bool) ℝ :=
  (Real.log ((N : ℝ) + 1))⁻¹ • gramMatrix (rowVector N (fun i => criticalPoint (γ i)))

theorem normalizedCriticalGram_entry (γ : ι → ℝ) (N : ℕ) (i j : ι × Bool) :
    normalizedCriticalGram γ N i j = crossPart i.2 j.2
      (classCross (γ i.1) (γ j.1) N, classCross (γ i.1) (-γ j.1) N) := by
  let t := γ i.1
  let u := γ j.1
  let pair := fun r : Fin N =>
    (classCrossTerm t u N r.castSucc, classCrossTerm t (-u) N r.castSucc)
  let F := crossPart i.2 j.2
  have hpair (r : Fin N) :
      pair r = (classWeight N r.castSucc)⁻¹ •
        (classMellin N (criticalPoint t) r.castSucc *
            star (classMellin N (criticalPoint u) r.castSucc),
         classMellin N (criticalPoint t) r.castSucc *
            classMellin N (criticalPoint u) r.castSucc) := by
    have hn := classMellin_critical_neg u N r.castSucc
    dsimp only [pair, classCrossTerm]
    rw [hn, star_star]
    apply Prod.ext <;> simp [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  have hsum : (classCross t u N, classCross t (-u) N) =
      (Real.log ((N : ℝ) + 1))⁻¹ • (∑ r, pair r) := by
    have hp : (∑ r, pair r) = (classCrossSum t u N, classCrossSum t (-u) N) := by
      apply Prod.ext
      · exact map_sum (LinearMap.fst ℝ ℂ ℂ) pair Finset.univ
      · exact map_sum (LinearMap.snd ℝ ℂ ℂ) pair Finset.univ
    rw [hp]
    apply Prod.ext
    · change classCross t u N = (Real.log ((N : ℝ) + 1))⁻¹ • classCrossSum t u N
      simp only [classCross, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
    · change classCross t (-u) N = (Real.log ((N : ℝ) + 1))⁻¹ • classCrossSum t (-u) N
      simp only [classCross, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]
  change normalizedCriticalGram γ N i j = F (classCross t u N, classCross t (-u) N)
  rw [hsum, map_smul, map_sum]
  rw [normalizedCriticalGram, Matrix.smul_apply, zero_gram_entry]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [hpair, map_smul]
  change _ = (classWeight N r.castSucc)⁻¹ *
    crossPart i.2 j.2 (classMellin N (criticalPoint t) r.castSucc *
          star (classMellin N (criticalPoint u) r.castSucc),
      classMellin N (criticalPoint t) r.castSucc *
          classMellin N (criticalPoint u) r.castSucc)
  rw [crossPart_term]
  unfold rowEntry
  dsimp only [t, u]
  ring

/-- The limiting real diagonal has one half of the squared Mellin frequency
norm in each of the two rows. -/
def criticalGramDiagonal [DecidableEq ι] (γ : ι → ℝ) : Matrix (ι × Bool) (ι × Bool) ℝ :=
  Matrix.diagonal (fun i : ι × Bool => ‖criticalPoint (γ i.1)‖^2 / 2)

theorem normalizedCriticalGram_tendsto [DecidableEq ι] (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i) :
    Tendsto (normalizedCriticalGram γ) atTop (𝓝 (criticalGramDiagonal γ)) := by
  apply tendsto_pi_nhds.2
  rintro ⟨i, b⟩
  apply tendsto_pi_nhds.2
  rintro ⟨j, c⟩
  have hn : γ i ≠ -γ j := by
    intro h
    linarith [hpos i, hpos j]
  let v : ℂ := if γ i = γ j then criticalPoint (γ i) * star (criticalPoint (γ j)) else 0
  have h₂ : Tendsto (classCross (γ i) (-γ j)) atTop (𝓝 0) := by
    simpa only [if_neg hn] using classCross_tendsto (γ i) (-γ j)
  have hp := (classCross_tendsto (γ i) (γ j)).prodMk_nhds h₂
  have h := ((crossPart b c).continuous.tendsto (v, 0)).comp hp
  have hd : crossPart b c (v, 0) = criticalGramDiagonal γ (i, b) (j, c) := by
    by_cases hij : i = j
    · subst j
      have hv : v = ((‖criticalPoint (γ i)‖^2 : ℝ) : ℂ) := by
        simp [v, Complex.sq_norm, Complex.mul_conj]
      rw [hv, crossPart_zero_right]
      by_cases hbc : b = c <;> simp [criticalGramDiagonal, hbc]
    · have hneq : γ i ≠ γ j := fun he => hij (hγ he)
      have hv : v = 0 := if_neg hneq
      have hzero : crossPart b c ((0, 0) : ℂ × ℂ) = 0 := map_zero _
      simp [hv, hzero, criticalGramDiagonal, hij]
  rw [hd] at h
  simpa only [Function.comp_def, normalizedCriticalGram_entry] using h

private def criticalSourceLimit (i : ι × Bool) : ℝ := part i.2 1

private theorem criticalSource_tendsto (γ : ι → ℝ) (i : ι × Bool) :
    Tendsto (fun N => source N (fun k => criticalPoint (γ k)) i)
      atTop (𝓝 (criticalSourceLimit i)) := by
  rcases i with ⟨i, b⟩
  have h : Tendsto (fun N => 1 - classMellin N (criticalPoint (γ i)) (Fin.last N))
      atTop (𝓝 (1 : ℂ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (critical_class_multiples_tendsto (γ i))
  cases b
  · exact (Complex.continuous_re.tendsto _).comp h
  · exact (Complex.continuous_im.tendsto _).comp h

variable [Fintype ι]

/-- The synthesized certificate is canonical even at a singular stage. -/
def certificateVector (N : ℕ) (z : ι → ℂ) : EuclideanSpace ℝ (Fin N) :=
  (synthesisSpan (rowVector N z)).starProjection (errorVector N 0)

def certificateEnergy (N : ℕ) (z : ι → ℂ) : ℝ := ‖certificateVector N z‖ ^ 2

theorem certificateEnergy_nonneg (N : ℕ) (z : ι → ℂ) : 0 ≤ certificateEnergy N z :=
  sq_nonneg _

theorem certificateEnergy_eq_dot {N : ℕ} (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0)
    (a : ι × Bool → ℝ) (ha : (gramMatrix (rowVector N z)).mulVec a = source N z) :
    certificateEnergy N z = dotProduct a (source N z) := by
  rw [certificateEnergy, certificateVector,
    ← certificate_eq_projection ((trialSpace (N + 1)).zero_mem) z hs hs1 hz a ha,
    gramMatrix_quadratic, ha]

/-- The exact finite identity expressed without a choice of normal coefficients. -/
theorem legal_error_completion_canonical {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0) :
    ‖hilbertOne - f‖ ^ 2 = classWeight N (Fin.last N) + certificateEnergy N z +
      ‖errorVector N f - certificateVector N z‖ ^ 2 := by
  obtain ⟨a, ha⟩ := exists_zero_normal N z hs hs1 hz
  have he := legal_error_completion hf z hs hs1 hz a ha
  rw [← certificateEnergy_eq_dot z hs hs1 hz a ha,
    certificate_eq_projection ((trialSpace (N + 1)).zero_mem) z hs hs1 hz a ha] at he
  exact he

private theorem criticalGramDiagonal_det_ne_zero [DecidableEq ι] (γ : ι → ℝ) :
    (criticalGramDiagonal γ).det ≠ 0 := by
  rw [criticalGramDiagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
    div_ne_zero (pow_ne_zero 2 (norm_ne_zero_iff.mpr (MellinFrequency.criticalPoint_ne_zero _)))
      (by norm_num))

private theorem diagonal_quadratic [DecidableEq ι] (γ : ι → ℝ) :
    (∑ i : ι × Bool, ((criticalGramDiagonal γ)⁻¹.mulVec criticalSourceLimit) i *
      criticalSourceLimit i) = 2 * ∑ i, 1 / ‖criticalPoint (γ i)‖^2 := by
  let D := criticalGramDiagonal γ
  let a := fun i : ι × Bool => criticalSourceLimit i / (‖criticalPoint (γ i.1)‖ ^ 2 / 2)
  have ha : D.mulVec a = criticalSourceLimit := by
    funext i
    change (Matrix.diagonal (fun j : ι × Bool => ‖criticalPoint (γ j.1)‖ ^ 2 / 2)).mulVec a i = _
    rw [Matrix.mulVec_diagonal]
    dsimp only [a]
    have hn : ‖criticalPoint (γ i.1)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (MellinFrequency.criticalPoint_ne_zero _)
    field_simp
  have hd : D⁻¹.mulVec criticalSourceLimit = a := by
    rw [← ha, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (criticalGramDiagonal_det_ne_zero γ)),
      Matrix.one_mulVec]
  change (∑ i, (D⁻¹.mulVec criticalSourceLimit) i * criticalSourceLimit i) = _
  rw [hd]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hbool : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [hbool, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [a, criticalSourceLimit, part]
  ring

/-- The exact certificate energy has the inverse-log asymptotic for each
fixed finite family of distinct positive critical ordinates of actual zeros. -/
theorem critical_certificate_log_tendsto (γ : ι → ℝ) (hγ : Function.Injective γ)
    (hpos : ∀ i, 0 < γ i) (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) *
      certificateEnergy N (fun i => criticalPoint (γ i))) atTop
      (𝓝 (2 * ∑ i, 1 / ‖criticalPoint (γ i)‖^2)) := by
  classical
  let z := fun i => criticalPoint (γ i)
  let G := normalizedCriticalGram γ
  let D := criticalGramDiagonal γ
  have hG : Tendsto G atTop (𝓝 D) := normalizedCriticalGram_tendsto γ hγ hpos
  have hD : D.det ≠ 0 := criticalGramDiagonal_det_ne_zero γ
  have hscalar : ContinuousAt Ring.inverse D.det := by
    simpa only [Ring.inverse_eq_inv'] using (ContinuousInv₀.continuousAt_inv₀ hD)
  have hi : Tendsto (fun N => (G N)⁻¹) atTop (𝓝 (D⁻¹)) :=
    Filter.Tendsto.comp (continuousAt_matrix_inv D hscalar) hG
  have hdet : Tendsto (fun N => (G N).det) atTop (𝓝 D.det) :=
    (continuous_id.matrix_det.tendsto D).comp hG
  have hopen : IsOpen ({0} : Set ℝ)ᶜ := isClosed_singleton.isOpen_compl
  have hn : ∀ᶠ N in atTop, (G N).det ≠ 0 := by
    exact hdet.eventually (hopen.mem_nhds (by simpa using hD))
  have hsol (i : ι × Bool) :
      Tendsto (fun N => ((G N)⁻¹.mulVec (source N z)) i) atTop
        (𝓝 ((D⁻¹.mulVec criticalSourceLimit) i)) := by
    change Tendsto (fun N => ∑ j, (G N)⁻¹ i j * source N z j) atTop
      (𝓝 (∑ j, D⁻¹ i j * criticalSourceLimit j))
    exact tendsto_finsetSum Finset.univ (fun j _ =>
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hi i) j).mul (criticalSource_tendsto γ j))
  have hquad := tendsto_finsetSum Finset.univ
    (fun i _ => (hsol i).mul (criticalSource_tendsto γ i))
  rw [show (∑ i, (D⁻¹.mulVec criticalSourceLimit) i * criticalSourceLimit i) =
      2 * ∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2 from diagonal_quadratic γ] at hquad
  refine hquad.congr' ?_
  filter_upwards [hn, eventually_ge_atTop (1 : ℕ)] with N hN hposN
  let logL := Real.log ((N : ℝ) + 1)
  let d := (G N)⁻¹.mulVec (source N z)
  let a := logL⁻¹ • d
  have hlog : logL ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    have h : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hposN
    linarith
  have hm : (G N).mulVec d = source N z := by
    dsimp only [d]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hN),
      Matrix.one_mulVec]
  have ha : (gramMatrix (rowVector N z)).mulVec a = source N z := by
    change (logL⁻¹ • gramMatrix (rowVector N z)).mulVec d = source N z at hm
    simpa only [Matrix.smul_mulVec, a, Matrix.mulVec_smul] using hm
  have he := certificateEnergy_eq_dot z (fun i => by simp [z])
    (fun i => MellinFrequency.criticalPoint_ne_one (γ i)) hz a ha
  change (∑ i, d i * source N z i) = logL * certificateEnergy N z
  rw [he, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change d i * source N z i = logL * ((logL⁻¹ * d i) * source N z i)
  rw [← mul_assoc logL _ _, ← mul_assoc logL _ _, mul_inv_cancel₀ hlog, one_mul]

/-- The same fixed critical family has vanishing unscaled certificate energy. -/
theorem critical_certificate_tendsto_zero (γ : ι → ℝ) (hγ : Function.Injective γ)
    (hpos : ∀ i, 0 < γ i) (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) :
    Tendsto (fun N => certificateEnergy N (fun i => criticalPoint (γ i))) atTop (𝓝 0) := by
  have hmod : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun N : ℕ => (Real.log ((N : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hmod)
  have hh := hi.mul (critical_certificate_log_tendsto γ hγ hpos hz)
  rw [zero_mul] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hp : 0 < Real.log ((N : ℝ) + 1) := by
    apply Real.log_pos
    have h : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]

/-- Every legal competitor obeys the same asymptotic lower floor from a fixed
finite family. The estimate is uniform over the legal coefficients. -/
theorem critical_certificate_legal_error_floor (γ : ι → ℝ) (hγ : Function.Injective γ)
    (hpos : ∀ i, 0 < γ i) (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f ∈ trialSpace (N + 1),
      2 * (∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2) - ε ≤
        Real.log ((N : ℝ) + 1) * ‖hilbertOne - f‖ ^ 2 := by
  have h := (critical_certificate_log_tendsto γ hγ hpos hz).eventually
    (lt_mem_nhds (show 2 * (∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2) - ε <
      2 * (∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2) by linarith))
  filter_upwards [h] with N hN f hf
  have he := legal_error_completion_canonical hf (fun i => criticalPoint (γ i))
    (fun i => by simp) (fun i => MellinFrequency.criticalPoint_ne_one (γ i)) hz
  have hE : certificateEnergy N (fun i => criticalPoint (γ i)) ≤ ‖hilbertOne - f‖ ^ 2 := by
    linarith [classWeight_pos N (Fin.last N),
      sq_nonneg ‖errorVector N f - certificateVector N (fun i => criticalPoint (γ i))‖]
  exact hN.le.trans (mul_le_mul_of_nonneg_left hE
    (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])))

end RiemannResearch.RH.Pareto.ResidueMellin
