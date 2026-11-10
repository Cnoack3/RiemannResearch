/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GrowingFourierGramBounds
import RiemannResearch.RH.ParetoResidueCriticalGramRate
import RiemannResearch.RH.ParetoResidueMicroscopicGram
import RiemannResearch.RH.ParetoResidueMovingCertificate
import RiemannResearch.RH.ParetoResidueAtomTests
import RiemannResearch.Analysis.ActualZeroReciprocalConstant
import RiemannResearch.RH.WeilExplicitFormula.ZetaReflect
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.Harmonic.Bounds
import Lean.Elab.Tactic.Omega

/-!
# Spacing bounds for moving zero families

A sorted separated set has at most two points at each rank distance.
The harmonic sum controls each row of the absolute inverse-gap matrix.
Complex pairings also retain their coefficient weights and can use the full
logarithmic-window kernel in the microscopic regime.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin
open SpectralObstruction (logPhaseKernel phaseSumBudget reciprocalSquareMass)
open RiemannResearch.Fourier (finiteGramErrorPairing finiteGramErrorPairing_norm_le_wiener_sq)
open MellinFrequency (criticalPoint)

private theorem rank_gap_le {m : ℕ} (f : Fin m → ℝ) (hf : StrictMono f) (δ : ℝ)
    (hgap : ∀ i j, i ≠ j → δ ≤ |f i - f j|)
    (i j : Fin m) (hij : i ≤ j) :
    δ * ((j.val - i.val : ℕ) : ℝ) ≤ f j - f i := by
  have hstep : ∀ k (hk : k < m), i.val ≤ k →
      δ * ((k - i.val : ℕ) : ℝ) ≤ f ⟨k, hk⟩ - f i := by
    intro k
    induction k with
    | zero =>
      intro hk hi
      have h : (⟨0, hk⟩ : Fin m) = i := Fin.ext (by change 0 = i.val; omega)
      simp [h]
    | succ k ih =>
      intro hk hi
      by_cases he : k + 1 = i.val
      · have h : (⟨k + 1, hk⟩ : Fin m) = i := Fin.ext he
        simp [he]
      · have hk' : k < m := by omega
        have hik : i.val ≤ k := by omega
        have hlt : (⟨k, hk'⟩ : Fin m) < ⟨k + 1, hk⟩ := by
          exact Nat.lt_succ_self k
        have hg := hgap ⟨k, hk'⟩ ⟨k + 1, hk⟩ (ne_of_lt hlt)
        rw [abs_of_nonpos (sub_nonpos.mpr (hf hlt).le)] at hg
        rw [show k + 1 - i.val = k - i.val + 1 by omega, Nat.cast_add, Nat.cast_one]
        linarith only [ih hk' hik, hg]
  exact hstep j.val j.isLt hij

private theorem sum_inv_gaps_sorted_le {m : ℕ} (f : Fin m → ℝ) (hf : StrictMono f)
    (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ i j, i ≠ j → δ ≤ |f i - f j|) (i : Fin m) :
    (∑ j, |f i - f j|⁻¹) ≤ 2 * (harmonic m : ℝ) / δ := by
  let s := (Finset.univ : Finset (Fin m)).erase i
  let e (j : Fin m) : Bool × ℕ :=
    if i.val ≤ j.val then (false, j.val - i.val - 1) else (true, i.val - j.val - 1)
  have hne (j : Fin m) (hj : j ∈ s) : j.val ≠ i.val := by
    intro h
    exact (Finset.mem_erase.mp hj).1 (Fin.ext h)
  have he : Set.InjOn e (↑s : Set (Fin m)) := by
    intro j hj k hk h
    have hjn := hne j hj
    have hkn := hne k hk
    apply Fin.ext
    by_cases hji : i.val ≤ j.val
    · by_cases hki : i.val ≤ k.val
      · have h' : j.val - i.val - 1 = k.val - i.val - 1 := by
          simpa only [e, if_pos hji, if_pos hki] using congrArg Prod.snd h
        omega
      · have h' : false = true := by
          simpa only [e, if_pos hji, if_neg hki] using congrArg Prod.fst h
        cases h'
    · by_cases hki : i.val ≤ k.val
      · have h' : true = false := by
          simpa only [e, if_neg hji, if_pos hki] using congrArg Prod.fst h
        cases h'
      · have h' : i.val - j.val - 1 = i.val - k.val - 1 := by
          simpa only [e, if_neg hji, if_neg hki] using congrArg Prod.snd h
        omega
  let S := (Finset.univ : Finset Bool) ×ˢ Finset.range m
  have hS : Finset.image e s ⊆ S := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    dsimp only [S]
    rw [Finset.mem_product]
    refine ⟨Finset.mem_univ _, Finset.mem_range.mpr ?_⟩
    dsimp only [e]
    split <;> omega
  have hdist (j : Fin m) (hj : j ∈ s) :
      δ * (((e j).2 : ℝ) + 1) ≤ |f i - f j| := by
    have hjn := hne j hj
    by_cases hij : i.val ≤ j.val
    · have hc : ((j.val - i.val - 1 : ℕ) : ℝ) + 1 = ((j.val - i.val : ℕ) : ℝ) := by
        exact_mod_cast (show j.val - i.val - 1 + 1 = j.val - i.val by omega)
      simp only [e, if_pos hij, hc]
      rw [abs_of_nonpos (sub_nonpos.mpr (hf.monotone hij))]
      linarith only [rank_gap_le f hf δ hgap i j hij]
    · have hji : j ≤ i := by change j.val ≤ i.val; omega
      have hc : ((i.val - j.val - 1 : ℕ) : ℝ) + 1 = ((i.val - j.val : ℕ) : ℝ) := by
        exact_mod_cast (show i.val - j.val - 1 + 1 = i.val - j.val by omega)
      simp only [e, if_neg hij, hc]
      rw [abs_of_nonneg (sub_nonneg.mpr (hf.monotone hji))]
      exact rank_gap_le f hf δ hgap j i hji
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
  simp only [sub_self, abs_zero, inv_zero, add_zero]
  change (∑ j ∈ s, |f i - f j|⁻¹) ≤ _
  calc
    _ ≤ ∑ j ∈ s, (δ * (((e j).2 : ℝ) + 1))⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) (hdist j hj)
    _ = ∑ p ∈ s.image e, (δ * ((p.2 : ℝ) + 1))⁻¹ := by rw [Finset.sum_image he]
    _ ≤ ∑ p ∈ S, (δ * ((p.2 : ℝ) + 1))⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
    _ = _ := by
      dsimp only [S]
      rw [Finset.sum_product, Fintype.sum_bool]
      simp_rw [mul_inv, ← Finset.mul_sum]
      rw [show (∑ j ∈ Finset.range m, ((j : ℝ) + 1)⁻¹) = (harmonic m : ℝ) by simp [harmonic]]
      ring

/-- The inverse-gap row sum of an arbitrary finite separated real family.
The diagonal summand has value zero. -/
theorem sum_inv_gaps_le_harmonic {η : Type*} [Fintype η] (f : η → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ i j, i ≠ j → δ ≤ |f i - f j|) (i : η) :
    (∑ j, |f i - f j|⁻¹) ≤ 2 * (harmonic (Fintype.card η) : ℝ) / δ := by
  classical
  have hf : Function.Injective f := by
    intro j k h
    by_contra hne
    have hh := hgap j k hne
    simp [h] at hh
    linarith
  let _ : LinearOrder η := LinearOrder.lift' f hf
  let E : ↑(Finset.univ : Finset η) ≃ η :=
    Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, fun j => ⟨⟨j, Finset.mem_univ j⟩, rfl⟩⟩
  let e₀ := (Finset.univ : Finset η).orderIsoOfFin Finset.card_univ
  let e := e₀.toEquiv.trans E
  have he : StrictMono (fun k => f (e k)) := by
    intro j k hjk
    exact e₀.strictMono hjk
  obtain ⟨k, rfl⟩ := e.surjective i
  rw [← Equiv.sum_comp e (fun j => |f (e k) - f j|⁻¹)]
  exact sum_inv_gaps_sorted_le (fun j => f (e j)) he δ hδ
    (fun j l h => hgap _ _ (fun h' => h (e.injective h'))) k

/-- The height-dependent part of the separated coefficient bound. -/
def criticalHeightConstant : ℝ :=
  2 * (1 + criticalTailMass) ^ 2 + 1 + 6 * reciprocalSquareMass

private theorem criticalHeightConstant_nonneg : 0 ≤ criticalHeightConstant := by
  have h : 0 ≤ reciprocalSquareMass := tsum_nonneg (fun _ => by positivity)
  unfold criticalHeightConstant
  positivity

theorem microscopicCrossBudget_height_le (t u T : ℝ) (hT : 0 ≤ T)
    (ht : |t| ≤ T) (hu : |u| ≤ T) :
    microscopicCrossBudget t u ≤ criticalHeightConstant * (1 + T) := by
  have h₀ : 0 ≤ reciprocalSquareMass := tsum_nonneg (fun _ => by positivity)
  have hnorm (x : ℝ) : ‖(x : ℂ) * Complex.I‖ = |x| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hpoint (x : ℝ) : ‖criticalPoint x + 1‖ ≤ 3 / 2 + |x| := by
    rw [show criticalPoint x + 1 = (3 / 2 : ℂ) + (x : ℂ) * Complex.I by
      unfold MellinFrequency.criticalPoint
      ring]
    refine (norm_add_le _ _).trans_eq ?_
    rw [hnorm, show ‖(3 / 2 : ℂ)‖ = (3 / 2 : ℝ) by
      rw [norm_div]; norm_num]
  have hphase : ‖((t - u : ℝ) : ℂ) * Complex.I + 1‖ ≤ 1 + 2 * T := by
    refine (norm_add_le _ _).trans ?_
    rw [hnorm, norm_one]
    linarith only [abs_sub t u, ht, hu]
  have hh : 1 + ‖criticalPoint t + 1‖ + ‖criticalPoint u + 1‖ +
      ‖((t - u : ℝ) : ℂ) * Complex.I + 1‖ ≤ 6 * (1 + T) := by
    linarith only [hpoint t, hpoint u, hphase, ht, hu, hT]
  unfold microscopicCrossBudget criticalHeightConstant
  nlinarith only [mul_le_mul_of_nonneg_left hh h₀,
    mul_nonneg hT (by positivity : 0 ≤ 2 * (1 + criticalTailMass) ^ 2 + 1)]

theorem criticalCrossBudget_height_le (t u T : ℝ) (hT : 0 ≤ T)
    (ht : |t| ≤ T) (hu : |u| ≤ T) :
    criticalCrossBudget t u ≤ criticalHeightConstant * (1 + T) + 2 * |t - u|⁻¹ := by
  refine (show criticalCrossBudget t u ≤ microscopicCrossBudget t u + 2 * |t - u|⁻¹ from ?_).trans
    (add_le_add (microscopicCrossBudget_height_le t u T hT ht hu) le_rfl)
  have h₀ : 0 ≤ reciprocalSquareMass := tsum_nonneg (fun _ => by positivity)
  have hp : phaseSumBudget (t - u) ≤
      1 + reciprocalSquareMass * ‖((t - u : ℝ) : ℂ) * Complex.I + 1‖ + 2 * |t - u|⁻¹ := by
    unfold phaseSumBudget
    split
    · have h := mul_nonneg h₀ (norm_nonneg (((t - u : ℝ) : ℂ) * Complex.I + 1))
      have hg : 0 ≤ 2 * |t - u|⁻¹ := by positivity
      linarith only [h, hg]
    · rw [div_eq_mul_inv]
      linarith
  unfold criticalCrossBudget microscopicCrossBudget
  nlinarith only [hp]

/-- Keep the actual weighted inverse-gap rows, and separate the height term from them. -/
theorem criticalGramWeightedBudget_le_height_rows {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (u : ι → ℝ) (N : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hu : ∀ i ∈ s, |u i| ≤ T) :
    criticalGramWeightedBudget s a u N ≤
      (criticalHeightConstant * (1 + T) *
          (∑ i ∈ s, (‖a i‖ * ‖criticalPoint (u i)‖)) ^ 2 +
        2 * ∑ i ∈ s, (‖a i‖ * ‖criticalPoint (u i)‖) ^ 2 *
          (∑ j ∈ s, |u i - u j|⁻¹)) / Real.log ((N : ℝ) + 1) := by
  let w (i : ι) := ‖a i‖ * ‖criticalPoint (u i)‖
  let g (i j : ι) := |u i - u j|⁻¹
  let C := criticalHeightConstant * (1 + T)
  unfold criticalGramWeightedBudget
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N]))
  have hsym :
      (∑ i ∈ s, ∑ j ∈ s, w j ^ 2 * g i j) =
        ∑ i ∈ s, ∑ j ∈ s, w i ^ 2 * g i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [g]
    rw [abs_sub_comm]
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, (C * (w i * w j) + (w i ^ 2 * g i j + w j ^ 2 * g i j)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ = w i * w j * criticalCrossBudget (u i) (u j) := by dsimp only [w]; ring
        _ ≤ w i * w j * (C + 2 * g i j) :=
          mul_le_mul_of_nonneg_left (criticalCrossBudget_height_le (u i) (u j) T hT
            (hu i hi) (hu j hj)) (by positivity [w])
        _ ≤ _ := by
          have hn := mul_nonneg (sq_nonneg (w i - w j)) (by dsimp only [g]; positivity : 0 ≤ g i j)
          nlinarith only [hn]
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [hsym]
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- The gap cost uses squared coefficient mass and the harmonic row bound. -/
theorem criticalGramWeightedBudget_le_height_spacing {ι : Type*} [Fintype ι]
    (a : ι → ℂ) (u : ι → ℝ) (N : ℕ) (T δ : ℝ) (hT : 0 ≤ T)
    (hu : ∀ i, |u i| ≤ T) (hδ : 0 < δ) (hgap : ∀ i j, i ≠ j → δ ≤ |u i - u j|) :
    criticalGramWeightedBudget Finset.univ a u N ≤
      (criticalHeightConstant * (1 + T) *
          (∑ i, (‖a i‖ * ‖criticalPoint (u i)‖)) ^ 2 +
        (4 * (harmonic (Fintype.card ι) : ℝ) / δ) *
          ∑ i, (‖a i‖ * ‖criticalPoint (u i)‖) ^ 2) / Real.log ((N : ℝ) + 1) := by
  refine (criticalGramWeightedBudget_le_height_rows Finset.univ a u N T hT
    (fun i _ => hu i)).trans ?_
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N]))
  apply add_le_add_right
  calc
    _ ≤ 2 * ∑ i, (‖a i‖ * ‖criticalPoint (u i)‖) ^ 2 *
        (2 * (harmonic (Fintype.card ι) : ℝ) / δ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (sum_inv_gaps_le_harmonic u δ hδ hgap i) (sq_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- A moving complex Gram pairing from the separated weighted schedule. -/
theorem growing_critical_gram_pairing_error_of_height_spacing (κ : ℕ → Type*) [∀ k, Fintype (κ k)]
    (a : ∀ k, κ k → ℂ) (u : ∀ k, κ k → ℝ) (N : ℕ → ℕ) (T δ : ℕ → ℝ)
    (hN : ∀ᶠ k in atTop, 0 < N k)
    (hT : ∀ k, 0 ≤ T k) (hu : ∀ k i, |u k i| ≤ T k) (hδ : ∀ k, 0 < δ k)
    (hgap : ∀ k i j, i ≠ j → δ k ≤ |u k i - u k j|)
    (hB : Tendsto (fun k =>
      (criticalHeightConstant * (1 + T k) *
          (∑ i, (‖a k i‖ * ‖criticalPoint (u k i)‖)) ^ 2 +
        (4 * (harmonic (Fintype.card (κ k)) : ℝ) / δ k) *
          ∑ i, (‖a k i‖ * ‖criticalPoint (u k i)‖) ^ 2) / Real.log ((N k : ℝ) + 1))
      atTop (𝓝 0)) :
    Tendsto (fun k => finiteGramErrorPairing Finset.univ (a k) (fun i j =>
        classCross (u k i) (u k j) (N k) -
          (if u k i = u k j then criticalPoint (u k i) * star (criticalPoint (u k j)) else 0)))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) (hN.mono fun k hk => ?_) hB
  exact (critical_gram_pairing_error_le Finset.univ (a k) (u k) (N k) hk).trans
    (criticalGramWeightedBudget_le_height_spacing (a k) (u k) (N k) (T k) (δ k) (hT k)
      (hu k) (hδ k) (hgap k))

/-- Approximate a moving complex Gram by its full logarithmic-window kernel.
Keeping that kernel permits coincident or microscopically close ordinates. -/
theorem growing_phaseStripped_critical_gram_pairing_error_of_height {ι : Type*}
    (s : ℕ → Finset ι) (b : ℕ → ι → ℂ) (u : ℕ → ι → ℝ) (N : ℕ → ℕ) (T : ℕ → ℝ)
    (hN : ∀ᶠ k in atTop, 0 < N k) (hT : ∀ k, 0 ≤ T k)
    (hu : ∀ k i, i ∈ s k → |u k i| ≤ T k)
    (hB : Tendsto (fun k =>
      (criticalHeightConstant * (1 + T k) / Real.log ((N k : ℝ) + 1)) *
        (∑ i ∈ s k, ‖b k i‖) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => finiteGramErrorPairing (s k) (b k) (fun i j =>
        phaseStrippedCross (u k i) (u k j) (N k) -
          logPhaseKernel ((u k i - u k j) * Real.log ((N k : ℝ) + 1))))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) (hN.mono fun k hk => ?_) hB
  apply finiteGramErrorPairing_norm_le_wiener_sq
  intro i hi j hj
  have hlog : 0 ≤ Real.log ((N k : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (N k)])
  exact (phaseStrippedCross_sub_logPhaseKernel_le (u k i) (u k j) (N k) hk).trans
    (div_le_div_of_nonneg_right (microscopicCrossBudget_height_le (u k i) (u k j) (T k)
      (hT k) (hu k i hi) (hu k j hj)) hlog)

variable {ι : Type*} [Fintype ι]

/-- Include both signs because the real normal equations use sum frequencies. -/
def signedCriticalOrdinate (γ : ι → ℝ) (i : ι × Bool) : ℝ :=
  if i.2 then -γ i.1 else γ i.1

theorem criticalRowBudget_le_height_harmonic (γ : ι → ℝ)
    (T δ : ℝ) (hT : 0 ≤ T) (hγ : ∀ i, |γ i| ≤ T) (hδ : 0 < δ)
    (hgap : ∀ i j, i ≠ j → δ ≤ |signedCriticalOrdinate γ i - signedCriticalOrdinate γ j|)
    (N : ℕ) (hN : 0 < N) (i : ι) :
    criticalRowBudget γ N i ≤
      (2 * (Fintype.card ι : ℝ) * criticalHeightConstant * (1 + T) +
        4 * (harmonic (2 * Fintype.card ι) : ℝ) / δ) / Real.log ((N : ℝ) + 1) := by
  let f := signedCriticalOrdinate γ
  have hfi : f (i, false) = γ i := rfl
  have hF (j : ι × Bool) : |f j| ≤ T := by
    rcases j with ⟨j, b⟩
    cases b <;> simpa [f, signedCriticalOrdinate] using hγ j
  have hg := sum_inv_gaps_le_harmonic f δ hδ hgap (i, false)
  rw [hfi, Fintype.card_prod, Fintype.card_bool, mul_comm (Fintype.card ι) 2] at hg
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (ι × Bool)))
    (fun j _ => criticalCrossBudget_height_le (γ i) (f j) T hT (hγ i) (hF j))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_bool, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hQ : (∑ j, criticalCrossBudget (γ i) (f j)) =
      ∑ j, (criticalCrossBudget (γ i) (γ j) + criticalCrossBudget (γ i) (-γ j)) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [Fintype.sum_bool]
    simp [f, signedCriticalOrdinate, add_comm]
  have hlog : 0 < Real.log ((N : ℝ) + 1) := by
    have h : 0 < (N : ℝ) := by exact_mod_cast hN
    exact Real.log_pos (by linarith)
  rw [criticalRowBudget, ← hQ]
  apply div_le_div_of_nonneg_right _ hlog.le
  refine hsum.trans ((add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ) ≤ 2))).trans_eq ?_)
  push_cast
  ring

/-- A scale for the uniform growth hypothesis. The harmonic term is
bounded by one plus the logarithm of the number of signed ordinates. -/
def criticalSpacingBudget (m : ℕ) (T δ : ℝ) (N : ℕ) : ℝ :=
  ((m : ℝ) * (1 + T) + (harmonic (2 * m) : ℝ) / δ) / Real.log ((N : ℝ) + 1)

theorem criticalSourceError_le_inv (N : ℕ) :
    0 ≤ criticalSourceError N ∧
      criticalSourceError N ≤ (1 + criticalTailMass) / ((N : ℝ) + 1) := by
  have ht : 0 ≤ criticalTailMass := tsum_nonneg (fun _ => by unfold criticalScale; positivity)
  let L : ℝ := (N : ℝ) + 1
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hL' : 0 < L := by linarith
  have hS : 1 ≤ Real.sqrt L := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  unfold criticalSourceError criticalScale
  rw [Nat.cast_add, Nat.cast_one]
  change 0 ≤ (1 + criticalTailMass) * (1 / (L * Real.sqrt L)) ∧
    (1 + criticalTailMass) * (1 / (L * Real.sqrt L)) ≤ (1 + criticalTailMass) / L
  rw [← mul_div_assoc, mul_one]
  exact ⟨by positivity, div_le_div_of_nonneg_left (by positivity) hL'
    (le_mul_of_one_le_right hL'.le hS)⟩

private theorem criticalSource_card_bound (m N : ℕ) (hN : 0 < N) :
    (m : ℝ) * (criticalSourceError N * (4 + criticalSourceError N)) ≤
      ((1 + criticalTailMass) * (5 + criticalTailMass)) * ((m : ℝ) / Real.log ((N : ℝ) + 1)) := by
  let L := (N : ℝ) + 1
  let C := 1 + criticalTailMass
  let e := criticalSourceError N
  have hL : 1 ≤ L := by dsimp only [L]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hL' : 0 < L := by linarith
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 < Real.log L := Real.log_pos (by dsimp only [L]; linarith)
  have hlogL : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos hL']
  have hC : 0 ≤ C := by
    have ht : 0 ≤ criticalTailMass := tsum_nonneg (fun _ => by unfold criticalScale; positivity)
    dsimp only [C]; positivity
  obtain ⟨he, heL⟩ := criticalSourceError_le_inv N
  change 0 ≤ e at he
  change e ≤ C / L at heL
  have heC := heL.trans (div_le_self hC hL)
  calc
    _ ≤ (m : ℝ) * ((C / L) * (4 + C)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul heL (by linarith) (by linarith) (by positivity))
        (Nat.cast_nonneg m)
    _ = C * (4 + C) * ((m : ℝ) / L) := by ring
    _ ≤ C * (4 + C) * ((m : ℝ) / Real.log L) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (Nat.cast_nonneg m) hlog hlogL) (by positivity)
    _ = _ := by dsimp only [C, L]; ring

private theorem criticalLog_nonneg (N : ℕ) : 0 ≤ Real.log ((N : ℝ) + 1) :=
  Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])

private theorem harmonic_cast_nonneg (n : ℕ) : 0 ≤ (harmonic n : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact Finset.sum_nonneg fun _ _ => by positivity

/-- A single height, count and signed gap budget suffices for the moving
certificate law. The multiples-source budget is automatic at this scale. -/
theorem moving_critical_certificate_of_spacing (κ : ℕ → Type*) [∀ j, Fintype (κ j)]
    (γ : ∀ j, κ j → ℝ) (N : ℕ → ℕ) (T δ : ℕ → ℝ)
    (hN : ∀ᶠ j in atTop, 0 < N j)
    (hT : ∀ j, 0 ≤ T j) (hγT : ∀ j i, |γ j i| ≤ T j) (hδ : ∀ j, 0 < δ j)
    (hpos : ∀ j i, 0 < γ j i)
    (hgap : ∀ j i k, i ≠ k → δ j ≤
      |signedCriticalOrdinate (γ j) i - signedCriticalOrdinate (γ j) k|)
    (hz : ∀ j i, riemannZeta (criticalPoint (γ j i)) = 0)
    (hbudget : Tendsto (fun j => criticalSpacingBudget (Fintype.card (κ j)) (T j) (δ j) (N j))
      atTop (𝓝 0))
    (B : ℝ) (hB : ∀ j, (∑ i, 1 / ‖criticalPoint (γ j i)‖ ^ 2) ≤ B) :
    Tendsto (fun j => Real.log ((N j : ℝ) + 1) *
      certificateEnergy (N j) (fun i => criticalPoint (γ j i)) -
      2 * ∑ i, 1 / ‖criticalPoint (γ j i)‖ ^ 2) atTop (𝓝 0) := by
  let q j := criticalSpacingBudget (Fintype.card (κ j)) (T j) (δ j) (N j)
  let A := 2 * criticalHeightConstant + 4
  let d j := A * q j
  have hA : 0 ≤ A := by dsimp only [A]; linarith [criticalHeightConstant_nonneg]
  have hq (j : ℕ) : 0 ≤ q j := by
    have hlog : 0 ≤ Real.log ((N j : ℝ) + 1) := (criticalLog_nonneg (N j))
    dsimp only [q, criticalSpacingBudget]
    positivity [hlog, hT j, hδ j, harmonic_cast_nonneg (2 * Fintype.card (κ j))]
  have hinj (j : ℕ) : Function.Injective (γ j) := by
    intro i k h
    by_contra hne
    have hne' : (i, false) ≠ (k, false) := fun he => hne (congrArg Prod.fst he)
    have hh := hgap j (i, false) (k, false) hne'
    simp [signedCriticalOrdinate, h] at hh
    linarith only [hh, hδ j]
  refine moving_critical_certificate_tendsto κ γ N hN hinj hpos hz d
    (fun j => mul_nonneg hA (hq j)) ?_ ?_ ?_ B hB
  · simpa only [d, mul_zero] using (tendsto_const_nhds (x := A)).mul hbudget
  · filter_upwards [hN] with j hj i
    have hlog : 0 ≤ Real.log ((N j : ℝ) + 1) := (criticalLog_nonneg (N j))
    refine (criticalRowBudget_le_height_harmonic (γ j) (T j) (δ j)
      (hT j) (hγT j) (hδ j) (hgap j) (N j) hj i).trans ?_
    dsimp only [d, A, q, criticalSpacingBudget]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hlog
    let a := (Fintype.card (κ j) : ℝ) * (1 + T j)
    let b := (harmonic (2 * Fintype.card (κ j)) : ℝ) / δ j
    have ha : 0 ≤ a := by dsimp only [a]; positivity [hT j]
    have hb : 0 ≤ b := div_nonneg (harmonic_cast_nonneg _) (hδ j).le
    calc
      _ = 2 * criticalHeightConstant * a + 4 * b := by dsimp only [a, b]; ring
      _ ≤ _ := by
        change 2 * criticalHeightConstant * a + 4 * b ≤ (2 * criticalHeightConstant + 4) * (a + b)
        nlinarith only [ha, mul_nonneg criticalHeightConstant_nonneg hb]
  · let C := (1 + criticalTailMass) * (5 + criticalTailMass)
    have hC : 0 ≤ C := by
      have ht : 0 ≤ criticalTailMass := tsum_nonneg (fun _ => by unfold criticalScale; positivity)
      dsimp only [C]; positivity
    have hlim : Tendsto (fun j => C * q j) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hbudget
    refine squeeze_zero' (Eventually.of_forall fun j => by
      positivity [(criticalSourceError_le_inv (N j)).1]) ?_ hlim
    filter_upwards [hN] with j hj
    refine (criticalSource_card_bound (Fintype.card (κ j)) (N j) hj).trans ?_
    apply mul_le_mul_of_nonneg_left _ hC
    unfold q criticalSpacingBudget
    apply div_le_div_of_nonneg_right _ ((criticalLog_nonneg (N j)))
    have h : 0 ≤ (harmonic (2 * Fintype.card (κ j)) : ℝ) / δ j :=
      div_nonneg (harmonic_cast_nonneg _) (hδ j).le
    nlinarith only [h, mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card (κ j))) (hT j)]

open RiemannResearch.Analysis.ActualZeroHorizontalEnergy (ActualZero)
open RiemannResearch.Analysis.ActualZeroReciprocalConstant
  (reciprocalConstant paired_reciprocal_summable paired_reciprocal_tsum
    ordinateTerm_le_reciprocal_re)
open RiemannResearch.RH.ParetoHorizontalZeroBridge
  (ordinateInverseSquareTerm_nonneg)
open MellinFrequency (criticalPoint_ne_one criticalPoint_re)

private theorem criticalPoint_im (t : ℝ) : (criticalPoint t).im = t := by
  simp [MellinFrequency.criticalPoint, Complex.mul_im]

private theorem criticalPoint_neg_eq_star (t : ℝ) :
    criticalPoint (-t) = star (criticalPoint t) := by
  apply Complex.ext
  · simp [criticalPoint_re]
  · simp [criticalPoint_im]

/-- The checked all-sign reciprocal sum bounds every distinct critical family. -/
theorem criticalReciprocalSum_le_constant (γ : ι → ℝ) (hγ : Function.Injective γ)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) :
    (∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2) ≤ reciprocalConstant := by
  let z := fun i => criticalPoint (γ i)
  let f (i : ι) : ActualZero :=
    ⟨z i, hz i, by norm_num [z, criticalPoint_re], by norm_num [z, criticalPoint_re]⟩
  have hf : Function.Injective f := by
    intro i j h
    apply hγ
    simpa only [f, z, criticalPoint_im] using congrArg (fun ρ : ActualZero => (ρ : ℂ).im) h
  let g (ρ : ActualZero) := ((Zeta23.zeroMult (ρ : ℂ) : ℂ) / ((ρ : ℂ) * (1 - (ρ : ℂ)))).re
  have hg : HasSum g reciprocalConstant := by
    have hs := Complex.hasSum_re paired_reciprocal_summable.hasSum
    rwa [paired_reciprocal_tsum, Complex.ofReal_re] at hs
  have hgn (ρ : ActualZero) : 0 ≤ g ρ :=
    (ordinateInverseSquareTerm_nonneg ρ).trans (ordinateTerm_le_reciprocal_re ρ)
  calc
    _ ≤ ∑ i, g (f i) := by
      apply Finset.sum_le_sum
      intro i _
      have hc : 1 - z i = (starRingEnd ℂ) (z i) := by
        apply Complex.ext
        · norm_num [z, criticalPoint_re]
        · simp [z, criticalPoint_im]
      have he : z i * (1 - z i) = ((‖z i‖ ^ 2 : ℝ) : ℂ) := by
        rw [hc, Complex.mul_conj, Complex.sq_norm]
      change 1 / ‖z i‖ ^ 2 ≤ ((Zeta23.zeroMult (z i) : ℂ) / (z i * (1 - z i))).re
      rw [he, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast Zeta23.ZetaSeam.one_le_mult_holds (z i) (f i).property
    _ = ∑ ρ ∈ Finset.univ.map ⟨f, hf⟩, g ρ := by
      rw [Finset.sum_map]
      rfl
    _ ≤ _ := (hg.summable.sum_le_tsum _ (fun ρ _ => hgn ρ)).trans_eq hg.tsum_eq

/-- Both signs of a positive critical family are present in the reciprocal sum. -/
theorem criticalReciprocalSum_positive_le_half (γ : ι → ℝ) (hγ : Function.Injective γ)
    (hpos : ∀ i, 0 < γ i) (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0) :
    (∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2) ≤ reciprocalConstant / 2 := by
  let f := signedCriticalOrdinate γ
  have hf : Function.Injective f := by
    rintro ⟨i, b⟩ ⟨j, c⟩ h
    cases b <;> cases c
    · change γ i = γ j at h
      exact Prod.ext (hγ h) rfl
    · change γ i = -γ j at h
      linarith [hpos i, hpos j]
    · change -γ i = γ j at h
      linarith [hpos i, hpos j]
    · change -γ i = -γ j at h
      exact Prod.ext (hγ (neg_injective h)) rfl
  have hzf (i : ι × Bool) : riemannZeta (criticalPoint (f i)) = 0 := by
    rcases i with ⟨i, b⟩
    cases b
    · exact hz i
    · change riemannZeta (criticalPoint (-γ i)) = 0
      rw [criticalPoint_neg_eq_star]
      change riemannZeta ((starRingEnd ℂ) (criticalPoint (γ i))) = 0
      rw [Zeta23.riemannZeta_conj (criticalPoint_ne_one (γ i)), hz i, map_zero]
  have h := criticalReciprocalSum_le_constant f hf hzf
  rw [Fintype.sum_prod_type] at h
  have he : (∑ i : ι, ∑ b : Bool, 1 / ‖criticalPoint (f (i, b))‖ ^ 2) =
      2 * ∑ i, 1 / ‖criticalPoint (γ i)‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fintype.sum_bool]
    change 1 / ‖criticalPoint (-γ i)‖ ^ 2 + 1 / ‖criticalPoint (γ i)‖ ^ 2 = _
    rw [criticalPoint_neg_eq_star, norm_star, two_mul]
  rw [he] at h
  linarith only [h]

private theorem harmonic_le_log_multiple (m : ℕ) :
    (harmonic (2 * m) : ℝ) ≤
      (1 + (Real.log 2)⁻¹) * Real.log ((2 * m : ℕ) : ℝ) := by
  by_cases hm : m = 0
  · simp [hm, harmonic]
  have h2 : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * m by omega)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2
  have h : 1 ≤ Real.log ((2 * m : ℕ) : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlog).mpr (by simpa only [one_mul] using hL)
  rw [add_mul, one_mul, mul_comm (Real.log 2)⁻¹, ← div_eq_mul_inv]
  linarith only [harmonic_le_one_add_log (2 * m), h]

/-- The logarithmic spacing criterion on the actual running LCM tower.
The reciprocal source bound comes from the checked actual-zero sum. -/
theorem lcm_moving_critical_certificate_of_log_spacing
    (κ : ℕ → Type*) [∀ j, Fintype (κ j)] (γ : ∀ j, κ j → ℝ)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (T δ : ℕ → ℝ)
    (hT : ∀ j, 0 ≤ T j) (hγT : ∀ j i, |γ j i| ≤ T j) (hδ : ∀ j, 0 < δ j)
    (hpos : ∀ j i, 0 < γ j i)
    (hgap : ∀ j i k, i ≠ k → δ j ≤
      |signedCriticalOrdinate (γ j) i - signedCriticalOrdinate (γ j) k|)
    (hz : ∀ j i, riemannZeta (criticalPoint (γ j i)) = 0)
    (hbudget : Tendsto (fun j => ((Fintype.card (κ j) : ℝ) * (1 + T j) +
      Real.log ((2 * Fintype.card (κ j) : ℕ) : ℝ) / δ j) / Chebyshev.psi (M j : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun j => Chebyshev.psi (M j : ℝ) *
      certificateEnergy (lcmResidueIndex (M j)) (fun i => criticalPoint (γ j i)) -
      2 * ∑ i, 1 / ‖criticalPoint (γ j i)‖ ^ 2) atTop (𝓝 0) := by
  let N j := lcmResidueIndex (M j)
  have hN : ∀ᶠ j in atTop, 0 < N j :=
    (lcmResidueIndex_tendsto.comp hM).eventually (eventually_gt_atTop 0)
  have hL (j : ℕ) : Real.log ((N j : ℝ) + 1) = Chebyshev.psi (M j : ℝ) := lcm_log_eq_psi _
  have hinj (j : ℕ) : Function.Injective (γ j) := by
    intro i k h
    by_contra hne
    have hh := hgap j (i, false) (k, false) (fun he => hne (congrArg Prod.fst he))
    simp [signedCriticalOrdinate, h] at hh
    linarith only [hh, hδ j]
  have hB (j : ℕ) := criticalReciprocalSum_positive_le_half (γ j) (hinj j) (hpos j) (hz j)
  have hsp : Tendsto (fun j => criticalSpacingBudget (Fintype.card (κ j)) (T j) (δ j) (N j))
      atTop (𝓝 0) := by
    let A := 1 + (Real.log 2)⁻¹
    have hA : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr (Real.log_nonneg (by norm_num))
    refine squeeze_zero' (Eventually.of_forall fun j => by
      have hlog : 0 ≤ Real.log ((N j : ℝ) + 1) := (criticalLog_nonneg (N j))
      unfold criticalSpacingBudget
      positivity [hlog, hT j, hδ j, harmonic_cast_nonneg (2 * Fintype.card (κ j))]) ?_
      (by simpa only [mul_zero] using (tendsto_const_nhds (x := A)).mul hbudget)
    filter_upwards with j
    unfold criticalSpacingBudget
    rw [← hL, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ ((criticalLog_nonneg (N j)))
    have hh := div_le_div_of_nonneg_right (harmonic_le_log_multiple (Fintype.card (κ j))) (hδ j).le
    have hh' : (harmonic (2 * Fintype.card (κ j)) : ℝ) / δ j ≤
        A * (Real.log ((2 * Fintype.card (κ j) : ℕ) : ℝ) / δ j) := by
      rw [← mul_div_assoc]
      exact hh
    have hp := mul_nonneg hA (show 0 ≤ (Fintype.card (κ j) : ℝ) * (1 + T j) by positivity [hT j])
    dsimp only [A] at hh' ⊢
    nlinarith only [hh', hp]
  have h := moving_critical_certificate_of_spacing κ γ N T δ hN hT hγT hδ hpos hgap hz hsp
    (reciprocalConstant / 2) hB
  simpa only [hL, N] using h

end RiemannResearch.RH.Pareto.ResidueMellin
