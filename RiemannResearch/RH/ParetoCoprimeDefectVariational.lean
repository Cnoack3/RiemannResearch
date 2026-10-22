/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoCoprimeDefectScreening
import RiemannResearch.RH.FirstCoordinateTailGap
import RiemannResearch.Analysis.FiniteGramSourceTranslation

/-!
# Exact odd-moment variational formulation of the Pareto defect

Source: continuation of the user-provided
ParetoCapacityFormalization20260921_Continued(4)(1).md (2026-09-21).
The explicit odd source is interpolated against the entire tail dictionary.
The exact optimizer keeps even and composite dictionary vectors. Its
arbitrarily small energy, equivalently unbounded defect capacity, remains
an Open arithmetic premise of the conditional RH endpoint.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.RH.Pareto.IntegerDPP
open Filter

def coprimeDefectSource (n : ℕ) (i : Fin n) : ℝ :=
  coprimeObservationDefect 2 (i.val+2)

def coprimeDefectMinimum (n : ℕ) : ThresholdHilbert :=
  minimumVector (finiteTailAtom_independent n) (coprimeDefectSource n)

def coprimeDefectCapacity (n : ℕ) : ℝ :=
  capacity (finiteTailAtom_independent n) (coprimeDefectSource n)

theorem coprimeDefectSource_eq_sub_observed (n : ℕ) :
    coprimeDefectSource n = reciprocalSource n -
      cross (fun i : Fin n => tailAtom i.val) (infiniteCoprimeCertificate 2) := by
  funext i
  dsimp [coprimeDefectSource, reciprocalSource, cross]
  rw [infiniteCoprimeCertificate_all_observations _ _ (by decide) (by decide)]
  ring

theorem coprimeDefectMinimum_eq (n : ℕ) :
    coprimeDefectMinimum n = tailMinimum n -
      minimumVector (finiteTailAtom_independent n)
        (cross (fun i : Fin n => tailAtom i.val) (infiniteCoprimeCertificate 2)) := by
  unfold coprimeDefectMinimum
  rw [coprimeDefectSource_eq_sub_observed, minimumVector_sub_observed]
  rfl

theorem coprimeDefectCapacity_exact (n : ℕ) :
    coprimeDefectCapacity n = tailCapacity n -
      2 * inner ℝ (tailMinimum n) (infiniteCoprimeCertificate 2) +
      capacity (finiteTailAtom_independent n)
        (cross (fun i : Fin n => tailAtom i.val) (infiniteCoprimeCertificate 2)) := by
  unfold coprimeDefectCapacity
  rw [coprimeDefectSource_eq_sub_observed, capacity_sub_observed_exact]
  rfl

theorem coprimeDefectMinimum_observation (n : ℕ) (i : Fin n) :
    inner ℝ (tailAtom i.val) (coprimeDefectMinimum n) = coprimeDefectSource n i :=
  minimumVector_observation (finiteTailAtom_independent n) (coprimeDefectSource n) i

theorem coprimeDefectMinimum_norm_sq (n : ℕ) :
    ‖coprimeDefectMinimum n‖^2 = coprimeDefectCapacity n :=
  (capacity_eq_norm_sq _ _).symm

theorem coprimeDefect_feasible_completion (n : ℕ) (x : ThresholdHilbert)
    (hx : ∀ i : Fin n, inner ℝ (tailAtom i.val) x = coprimeDefectSource n i) :
    ‖x‖^2 = coprimeDefectCapacity n + ‖x - coprimeDefectMinimum n‖^2 := by
  have h := feasible_norm_sq_completion (finiteTailAtom_independent n) (coprimeDefectSource n) x hx
  change ‖x‖^2 = ‖coprimeDefectMinimum n‖^2 + ‖x - coprimeDefectMinimum n‖^2 at h
  simpa only [coprimeDefectMinimum_norm_sq] using h

theorem coprimeDefectMinimum_increment (m n : ℕ) (hmn : m ≤ n) :
    ‖coprimeDefectMinimum n - coprimeDefectMinimum m‖^2 =
      coprimeDefectCapacity n - coprimeDefectCapacity m := by
  have h := coprimeDefect_feasible_completion m (coprimeDefectMinimum n)
    (fun i => coprimeDefectMinimum_observation n (Fin.castLE hmn i))
  rw [coprimeDefectMinimum_norm_sq] at h
  linarith

theorem coprimeDefectCapacity_monotone : Monotone coprimeDefectCapacity := by
  intro m n hmn
  have h := coprimeDefectMinimum_increment m n hmn
  nlinarith [sq_nonneg ‖coprimeDefectMinimum n - coprimeDefectMinimum m‖]

theorem coprimeDefectCapacity_le (n : ℕ) :
    coprimeDefectCapacity n ≤
      2 * tailCapacity n + 2 * ‖infiniteCoprimeCertificate 2‖^2 := by
  unfold coprimeDefectCapacity
  rw [coprimeDefectSource_eq_sub_observed]
  exact capacity_sub_observed_le _ _ _

theorem tailCapacity_le_coprimeDefectCapacity (n : ℕ) :
    tailCapacity n ≤
      2 * coprimeDefectCapacity n + 2 * ‖infiniteCoprimeCertificate 2‖^2 := by
  unfold coprimeDefectCapacity
  rw [coprimeDefectSource_eq_sub_observed]
  exact capacity_le_sub_observed _ _ _

theorem coprimeDefectCapacity_bounded_iff :
    (∃ B : ℝ, ∀ n, coprimeDefectCapacity n ≤ B) ↔
      (∃ B : ℝ, ∀ n, tailCapacity n ≤ B) := by
  constructor
  · rintro ⟨B,hB⟩
    refine ⟨2*B + 2*‖infiniteCoprimeCertificate 2‖^2, fun n => ?_⟩
    have h := tailCapacity_le_coprimeDefectCapacity n
    linarith [hB n]
  · rintro ⟨B,hB⟩
    refine ⟨2*B + 2*‖infiniteCoprimeCertificate 2‖^2, fun n => ?_⟩
    have h := coprimeDefectCapacity_le n
    linarith [hB n]

theorem coprimeDefectCapacity_bounded_iff_interpolant :
    (∃ B : ℝ, ∀ n, coprimeDefectCapacity n ≤ B) ↔
      ∃ x : ThresholdHilbert, ∀ k : ℕ,
        inner ℝ (tailAtom k) x = coprimeObservationDefect 2 (k+2) := by
  constructor
  · intro hb
    obtain ⟨z,hz⟩ := tailCapacity_bounded_iff_exists_certificate.mp
      (coprimeDefectCapacity_bounded_iff.mp hb)
    refine ⟨z - infiniteCoprimeCertificate 2, fun k => ?_⟩
    rw [inner_sub_right]
    have h := tailCertificate_observation z hz (k+1) ⟨k,by omega⟩
    rw [h, infiniteCoprimeCertificate_all_observations _ _ (by decide) (by decide)]
    dsimp [reciprocalSource]
    ring
  · rintro ⟨x,hx⟩
    refine ⟨‖x‖^2,fun n => ?_⟩
    have h := coprimeDefect_feasible_completion n x (fun i => hx i.val)
    nlinarith [sq_nonneg ‖x - coprimeDefectMinimum n‖]

theorem coprimeDefectCapacity_bounded_of_not_RH (hRH : ¬ RiemannHypothesis) :
    ∃ B : ℝ, ∀ n, coprimeDefectCapacity n ≤ B := by
  apply coprimeDefectCapacity_bounded_iff.mpr
  exact firstCoordinateTailGap_pos_iff_capacity_bounded.mp
    (not_RH_firstCoordinateTailGap_pos hRH)

theorem riemannHypothesis_of_coprimeDefectCapacity_unbounded
    (h : ¬ ∃ B : ℝ, ∀ n, coprimeDefectCapacity n ≤ B) : RiemannHypothesis := by
  by_contra hRH
  exact h (coprimeDefectCapacity_bounded_of_not_RH hRH)

theorem coprimeDefect_pairing_explicit (n : ℕ) (c : Fin n → ℝ) :
    (∑ i, c i * coprimeDefectSource n i) =
      (1 + ‖infiniteCoprimeCertificate 2‖^2/2) *
        ∑ i, if 2 ∣ i.val+2 then 0 else c i / ((i.val+2 : ℕ) : ℝ)^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [coprimeDefectSource, coprimeObservationDefect_two]
  split_ifs <;> ring

theorem coprimeDefect_source_sq_le (n : ℕ) (c : Fin n → ℝ) :
    (∑ i, c i * coprimeDefectSource n i)^2 ≤ coprimeDefectCapacity n *
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 :=
  source_sq_le_capacity_mul_energy _ _ _

/-- CONDITIONAL RESEARCH REDUCTION: constructing these normalized small-energy
legal combinations remains Open. All even and composite dictionary vectors
remain available in the combination and its full tail norm. -/
theorem riemannHypothesis_of_oddMoment_small_tail
    (h : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℝ),
      (∑ i, if 2 ∣ i.val+2 then 0 else c i / ((i.val+2 : ℕ) : ℝ)^2) = 1 ∧
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 < ε) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨B,hB⟩ := coprimeDefectCapacity_bounded_of_not_RH hRH
  let K : ℝ := 1 + ‖infiniteCoprimeCertificate 2‖^2/2
  have hK : 0 < K := by dsimp [K]; nlinarith [sq_nonneg ‖infiniteCoprimeCertificate 2‖]
  have hB0 : 0 ≤ B := (capacity_nonneg (finiteTailAtom_independent 0)
    (coprimeDefectSource 0)).trans (hB 0)
  have hBp : 0 < B+1 := by linarith
  obtain ⟨n,c,hc,he⟩ := h (K^2/(B+1)) (div_pos (sq_pos_of_pos hK) hBp)
  have hs := coprimeDefect_source_sq_le n c
  rw [coprimeDefect_pairing_explicit, hc, mul_one] at hs
  change K^2 ≤ _ at hs
  have hu := mul_le_mul_of_nonneg_right (hB n)
    (sq_nonneg ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖)
  have hl := (lt_div_iff₀ hBp).mp he
  nlinarith [sq_nonneg ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖]

theorem coprimeDefectSource_ne_zero (n : ℕ) (hn : 2 ≤ n) :
    coprimeDefectSource n ≠ 0 := by
  intro hz
  have h := congrFun hz ⟨1,by omega⟩
  change coprimeObservationDefect 2 (1+2) = 0 at h
  rw [coprimeObservationDefect_two] at h
  norm_num at h
  nlinarith [sq_nonneg ‖infiniteCoprimeCertificate 2‖]

theorem coprimeDefectCapacity_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < coprimeDefectCapacity n :=
  capacity_pos (finiteTailAtom_independent n) (coprimeDefectSource n)
    (coprimeDefectSource_ne_zero n hn)

/-- Actual inverse-Gram coefficients attaining odd moment one. -/
def oddMomentOptimizer (n : ℕ) : Fin n → ℝ :=
  ((1 + ‖infiniteCoprimeCertificate 2‖^2/2) / coprimeDefectCapacity n) •
    inverseSource (finiteTailAtom_independent n) (coprimeDefectSource n)

theorem oddMomentOptimizer_normalized (n : ℕ) (hn : 2 ≤ n) :
    (∑ i, if 2 ∣ i.val+2 then 0 else
      oddMomentOptimizer n i / ((i.val+2 : ℕ) : ℝ)^2) = 1 := by
  have h := coprimeDefect_pairing_explicit n (oddMomentOptimizer n)
  have hs : (∑ i, oddMomentOptimizer n i * coprimeDefectSource n i) =
      1 + ‖infiniteCoprimeCertificate 2‖^2/2 := by
    simp only [oddMomentOptimizer, Pi.smul_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum]
    change (_ / coprimeDefectCapacity n) * coprimeDefectCapacity n = _
    exact div_mul_cancel₀ _ (ne_of_gt (coprimeDefectCapacity_pos n hn))
  rw [hs] at h
  have hK : 0 < 1 + ‖infiniteCoprimeCertificate 2‖^2/2 := by
    nlinarith [sq_nonneg ‖infiniteCoprimeCertificate 2‖]
  nlinarith

/-- Exact energy of the genuine odd-moment optimizer. -/
theorem oddMomentOptimizer_energy (n : ℕ) (hn : 2 ≤ n) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
      (oddMomentOptimizer n)‖^2 =
      (1 + ‖infiniteCoprimeCertificate 2‖^2/2)^2 / coprimeDefectCapacity n := by
  rw [oddMomentOptimizer, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  change (_ / coprimeDefectCapacity n)^2 * ‖coprimeDefectMinimum n‖^2 = _
  rw [coprimeDefectMinimum_norm_sq]
  field_simp [ne_of_gt (coprimeDefectCapacity_pos n hn)]

/-- Exact completion, retaining the entire signed tail energy. -/
theorem oddMoment_tail_energy_completion (n : ℕ) (hn : 2 ≤ n) (c : Fin n → ℝ)
    (hc : (∑ i, if 2 ∣ i.val+2 then 0 else c i / ((i.val+2 : ℕ) : ℝ)^2) = 1) :
    ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 =
      (1 + ‖infiniteCoprimeCertificate 2‖^2/2)^2 / coprimeDefectCapacity n +
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (c - oddMomentOptimizer n)‖^2 := by
  have hs := coprimeDefect_pairing_explicit n c
  rw [hc, mul_one] at hs
  rw [map_sub, norm_sub_sq_real, oddMomentOptimizer_energy n hn]
  have hp : inner ℝ (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
      (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (oddMomentOptimizer n)) =
      (1 + ‖infiniteCoprimeCertificate 2‖^2/2)^2 / coprimeDefectCapacity n := by
    rw [oddMomentOptimizer, map_smul, inner_smul_right]
    change (_ / coprimeDefectCapacity n) *
      inner ℝ (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c)
        (minimumVector (finiteTailAtom_independent n) (coprimeDefectSource n)) = _
    rw [inner_synthesis_minimumVector, hs]
    ring
  rw [hp]
  ring

theorem coprimeDefectCapacity_bounded_iff_rowEnergy :
    (∃ B : ℝ, ∀ n, coprimeDefectCapacity n ≤ B) ↔
      Summable factorialCrossGramRowEnergy := by
  rw [coprimeDefectCapacity_bounded_iff,
    factorialCrossGramRowEnergy_summable_iff_schurGain]
  constructor
  · rintro ⟨B,hB⟩
    by_contra h
    have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun n => div_nonneg (sq_nonneg (schurEta n)) (schurSigma_pos n).le)).mp h
    have hev := (tendsto_atTop.mp ht) (B+1)
    obtain ⟨n,hn⟩ := eventually_atTop.mp hev
    have hh := hn n le_rfl
    rw [← capacity_eq_sum_schur] at hh
    linarith [hB n]
  · intro h
    refine ⟨∑' n, (schurEta n)^2 / schurSigma n, fun n => ?_⟩
    rw [capacity_eq_sum_schur]
    exact Summable.sum_le_tsum (Finset.range n)
      (fun n _ => div_nonneg (sq_nonneg _) (schurSigma_pos n).le) h

/-- The explicit constant in the odd-moment normalization. -/
theorem coprimeDefect_odd_constant :
    1 + ‖infiniteCoprimeCertificate 2‖^2/2 = Real.pi^2/(Real.pi^2-8) := by
  have h := coprimeObservationDefect_two_explicit 1
  rw [coprimeObservationDefect_two] at h
  norm_num at h
  calc
    _ = 9 * ((1 + ‖infiniteCoprimeCertificate 2‖^2/2) / 9) := by ring
    _ = 9 * (Real.pi^2 / ((Real.pi^2-8)*9)) := by rw [h]
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Exact variational equivalence. Neither side is supplied unconditionally. -/
theorem coprimeDefectCapacity_unbounded_iff_small_tail :
    (¬ ∃ B : ℝ, ∀ n, coprimeDefectCapacity n ≤ B) ↔
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (c : Fin n → ℝ),
      (∑ i, if 2 ∣ i.val+2 then 0 else c i / ((i.val+2 : ℕ) : ℝ)^2) = 1 ∧
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖^2 < ε := by
  constructor
  · intro h ε hε
    push Not at h
    let K : ℝ := 1 + ‖infiniteCoprimeCertificate 2‖^2/2
    obtain ⟨n,hn⟩ := h (K^2/ε)
    have hl : K^2/ε < coprimeDefectCapacity (n+2) :=
      hn.trans_le (coprimeDefectCapacity_monotone (by omega))
    refine ⟨n+2, oddMomentOptimizer (n+2),
      oddMomentOptimizer_normalized _ (by omega), ?_⟩
    rw [oddMomentOptimizer_energy _ (by omega)]
    apply (div_lt_iff₀ (coprimeDefectCapacity_pos _ (by omega))).mpr
    have hh := (div_lt_iff₀ hε).mp hl
    dsimp [K] at hh
    nlinarith
  · intro h hb
    obtain ⟨B,hB⟩ := hb
    let K : ℝ := 1 + ‖infiniteCoprimeCertificate 2‖^2/2
    have hK : 0 < K := by
      dsimp [K]
      nlinarith [sq_nonneg ‖infiniteCoprimeCertificate 2‖]
    have hB0 : 0 ≤ B := (capacity_nonneg (finiteTailAtom_independent 0)
      (coprimeDefectSource 0)).trans (hB 0)
    have hBp : 0 < B+1 := by linarith
    obtain ⟨n,c,hc,he⟩ := h (K^2/(B+1)) (div_pos (sq_pos_of_pos hK) hBp)
    have hs := coprimeDefect_source_sq_le n c
    rw [coprimeDefect_pairing_explicit, hc, mul_one] at hs
    change K^2 ≤ _ at hs
    have hu := mul_le_mul_of_nonneg_right (hB n)
      (sq_nonneg ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖)
    have hl := (lt_div_iff₀ hBp).mp he
    nlinarith [sq_nonneg ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖]

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
