/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PhysicalSourceProjection
import RiemannResearch.RH.ParetoAtomPhysicalNorm
import RiemannResearch.RH.SquarefreeStageExhaustion

/-!
# Unconditional physical source limits and vanishing signed correction

Large prime packets force the positive shifted source determinant to zero.
The exact actual projection bound then forces the logarithmic charge to zero,
and the complete signed determinant forces the mixed charge to -2*pi.
The primorial chain supplies every legal, inertia, charge-bound and prime-
exhaustion hypothesis. These actual source limits discharge the corresponding
premises of PhysicalSchurCoupling.physical_source_limit_bound.

The normalized signed-source square tends to zero, and the actual projection
charge tends to 4*pi/(-Cinf). The actual limiting charge Cinf is still
unidentified: this module does not prove Cinf=-4*pi or RH.

Source: user-directed continuation of PhysicalArithmeticObservations20261008.md;
large-prime mean dual argument developed here using the complete covariance
identity in ParetoAtomPhysicalNorm and the exact signed Schur coupling.
-/

noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PhysicalSourceLimits
open PhysicalPacketCore PhysicalSchurCoupling PhysicalSourceProjection

theorem primePacket_norm_lt (p : ℕ) (hp : p.Prime) :
    paretoInner (ramanujanPacket p) (ramanujanPacket p) < 4 * (p : ℝ) / 3 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have he : residue p = fun k => (p : ℝ) * normalizedAtom p k := by
    funext k
    unfold normalizedAtom
    field_simp [ne_of_gt hpR]
  have hg := fun k => normalizedAtom_abs_le_one p k hp.pos
  have hpg := bounded_const_mul hg (p : ℝ)
  rw [ramanujanPacket_prime_eq_residue p hp, he,
    paretoInner_const_mul_left hg hpg, paretoInner_const_mul_right hg hg]
  calc
    _ = (p : ℝ) * (p : ℝ) * paretoInner (normalizedAtom p) (normalizedAtom p) := by ring
    _ < (p : ℝ) * (p : ℝ) * (4 / (3 * (p : ℝ))) :=
      mul_lt_mul_of_pos_left (normalizedAtom_norm_lt_four_thirds p hp.pos)
        (mul_pos hpR hpR)
    _ = _ := by field_simp [ne_of_gt hpR]

/-- Actual prime packet norm controls the full shifted determinant. -/
theorem determinant_prime_bound (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (p : ℕ) (hp : p.Prime) (hps : p ∈ s) :
    shiftedDeterminant s <
      16 * Real.pi * (-inverseCharge s) * (p : ℝ) / (3 * ((p : ℝ) - 1) ^ 2) := by
  classical
  let i : s := ⟨p, hps⟩
  have h := totient_cauchy s hs ho (Pi.single i 1)
  have hphi : ramanujanTotientVector s ⬝ᵥ Pi.single i 1 = (p : ℝ) - 1 := by
    rw [dotProduct_single_one]
    change (Nat.totient p : ℝ) = (p : ℝ) - 1
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]
    norm_num
  have hquad : (Pi.single i (1 : ℝ)) ⬝ᵥ
      (ramanujanGramMatrix s *ᵥ Pi.single i 1) =
        paretoInner (ramanujanPacket p) (ramanujanPacket p) := by
    simp only [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col,
      Matrix.transpose_apply, ramanujanGramMatrix]
    rfl
  rw [hphi, hquad] at h
  have hT : 0 < shiftedDeterminant s := shiftedDeterminant_pos s hs ho
  have hC : inverseCharge s < 0 := inverseCharge_neg s hs ho
  have hdual : 0 < -4 * Real.pi * inverseCharge s / shiftedDeterminant s := by
    apply div_pos _ hT
    nlinarith [Real.pi_pos]
  have hlt := h.trans_lt (mul_lt_mul_of_pos_left (primePacket_norm_lt p hp) hdual)
  have hfrac : (-4 * Real.pi * inverseCharge s / shiftedDeterminant s) *
      (4 * (p : ℝ) / 3) =
        (16 * Real.pi * (-inverseCharge s) * (p : ℝ) / 3) / shiftedDeterminant s := by ring
  rw [hfrac] at hlt
  have hm := (lt_div_iff₀ hT).mp hlt
  have hp1 : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  apply (lt_div_iff₀ (by positivity : 0 < 3 * ((p : ℝ) - 1) ^ 2)).mpr
  nlinarith only [hm]

theorem determinant_prime_inv_bound (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (p : ℕ) (hp : p.Prime) (hps : p ∈ s) :
    shiftedDeterminant s < 64 * Real.pi * (-inverseCharge s) / (3 * (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hC : inverseCharge s < 0 := inverseCharge_neg s hs ho

  apply (determinant_prime_bound s hs ho p hp hps).trans_le
  apply (div_le_div_iff₀ (by positivity : 0 < 3 * ((p : ℝ) - 1) ^ 2)
    (by positivity : 0 < 3 * (p : ℝ))).mpr
  have hsq : (p : ℝ) ^ 2 ≤ 4 * ((p : ℝ) - 1) ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 48 * Real.pi * (-inverseCharge s) from
    (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 48) Real.pi_pos) (neg_pos.mpr hC)).le)
  nlinarith only [hh]

theorem determinant_tendsto_zero_of_prime_exhaustion (packets : ℕ → Finset ℕ)
    (hlegal : ∀ n, ∀ q ∈ packets n, 1 < q)
    (hodd : ∀ n, ∃ p ∈ packets n, p.Prime ∧ 2 < p)
    (K : ℝ) (hbound : ∀ n, -inverseCharge (packets n) ≤ K)
    (hexhaust : ∀ p : ℕ, p.Prime → ∀ᶠ n in atTop, p ∈ packets n) :
    Tendsto (fun n => shiftedDeterminant (packets n)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (64 * Real.pi * K / (3 * ε))
  obtain ⟨p, hkp, hp⟩ := Nat.exists_infinite_primes k
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hlarge : 64 * Real.pi * K / (3 * (p : ℝ)) < ε := by
    have hpk : (k : ℝ) ≤ p := by exact_mod_cast hkp
    have hl : 64 * Real.pi * K / (3 * ε) < (p : ℝ) := hk.trans_le hpk
    have hl' := (div_lt_iff₀ (by positivity : 0 < 3 * ε)).mp hl
    apply (div_lt_iff₀ (by positivity : 0 < 3 * (p : ℝ))).mpr
    nlinarith only [hl']
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hexhaust p hp)
  refine ⟨N, ?_⟩
  intro n hn
  have hb : 64 * Real.pi * (-inverseCharge (packets n)) / (3 * (p : ℝ)) ≤
      64 * Real.pi * K / (3 * (p : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (hbound n) (by positivity)
  have ht := (determinant_prime_inv_bound (packets n) (hlegal n) (hodd n)
    p hp (hN n hn)).trans_le hb
  simpa only [Real.dist_eq, sub_zero,
    abs_of_pos (shiftedDeterminant_pos (packets n) (hlegal n) (hodd n))] using ht.trans hlarge

theorem logarithmicCharge_tendsto_zero_of_determinant (packets : ℕ → Finset ℕ)
    (hlegal : ∀ n, ∀ q ∈ packets n, 1 < q)
    (hodd : ∀ n, ∃ p ∈ packets n, p.Prime ∧ 2 < p)
    (hT : Tendsto (fun n => shiftedDeterminant (packets n)) atTop (𝓝 0)) :
    Tendsto (fun n => logarithmicCharge (packets n)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n => shiftedDeterminant (packets n) / (4 * Real.pi))
      atTop (𝓝 0) := by simpa using hT.div_const (4 * Real.pi)
  have hneg := squeeze_zero
    (fun n => (neg_pos.mpr (logarithmicCharge_neg (packets n) (hlegal n) (hodd n))).le)
    (fun n => (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mpr
      (by nlinarith only [logarithmicCharge_control (packets n) (hlegal n) (hodd n)])) hupper
  simpa only [neg_neg, neg_zero] using hneg.neg

theorem mixedCharge_tendsto_neg_two_pi_of_logarithmic (packets : ℕ → Finset ℕ)
    (hlegal : ∀ n, ∀ q ∈ packets n, 1 < q)
    (hodd : ∀ n, ∃ p ∈ packets n, p.Prime ∧ 2 < p)
    (K : ℝ) (hK : 0 < K) (hbound : ∀ n, -inverseCharge (packets n) ≤ K)
    (hA : Tendsto (fun n => logarithmicCharge (packets n)) atTop (𝓝 0)) :
    Tendsto (fun n => mixedCharge (packets n)) atTop (𝓝 (-2 * Real.pi)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hthreshold : 0 < ε ^ 2 / K := div_pos (sq_pos_of_pos hε) hK
  have ha := hA.neg
  have hev : ∀ᶠ n in atTop, -logarithmicCharge (packets n) < ε ^ 2 / K :=
    ha.eventually (gt_mem_nhds (by simpa using hthreshold))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, ?_⟩
  intro n hn
  have hAn := logarithmicCharge_neg (packets n) (hlegal n) (hodd n)
  have hdet := shiftedDeterminant_pos (packets n) (hlegal n) (hodd n)
  unfold shiftedDeterminant at hdet
  have hprod := mul_le_mul_of_nonneg_left (hbound n) (neg_nonneg.mpr hAn.le)
  have hε' := (lt_div_iff₀ hK).mp (hN n hn)
  have hsq : (2 * Real.pi + mixedCharge (packets n)) ^ 2 < ε ^ 2 := by
    nlinarith only [hdet, hprod, hε']
  rw [Real.dist_eq]
  have heq : mixedCharge (packets n) - -2 * Real.pi = 2 * Real.pi + mixedCharge (packets n) := by ring
  rw [heq]
  nlinarith [sq_abs (2 * Real.pi + mixedCharge (packets n)),
    abs_nonneg (2 * Real.pi + mixedCharge (packets n))]

def primorialPackets (n : ℕ) : Finset ℕ :=
  divisorPackets (SquarefreeStageExhaustion.primorialPeriod n)

theorem primorialPackets_legal (n : ℕ) : ∀ q ∈ primorialPackets n, 1 < q :=
  divisorPackets_legal _

theorem primorialPackets_odd (n : ℕ) : ∃ p ∈ primorialPackets n, p.Prime ∧ 2 < p :=
  divisorPackets_odd _ (SquarefreeStageExhaustion.primorialPeriod_gt_two n)
    (SquarefreeStageExhaustion.primorialPeriod_squarefree n)

theorem primorialPackets_charge_bound (n : ℕ) :
    -inverseCharge (primorialPackets n) ≤ 8 * Real.sqrt 3 := by
  have h := MeanOneChargeBounds.inverseCharge_ge_six _
    (SquarefreeStageExhaustion.primorialPeriod_six_dvd n)
    (SquarefreeStageExhaustion.primorialPeriod_gt_two n)
  dsimp only [primorialPackets]
  linarith

theorem prime_eventually_mem_primorialPackets (p : ℕ) (hp : p.Prime) :
    ∀ᶠ n in atTop, p ∈ primorialPackets n := by
  filter_upwards [SquarefreeStageExhaustion.squarefree_eventually_dvd_primorialPeriod
    p hp.squarefree] with n hn
  apply Finset.mem_filter.mpr
  exact ⟨Nat.mem_divisors.mpr ⟨hn, ne_of_gt (SquarefreeStageExhaustion.primorialPeriod_pos n)⟩,
    hp.one_lt⟩

theorem primorial_determinant_tendsto_zero :
    Tendsto (fun n => shiftedDeterminant (primorialPackets n)) atTop (𝓝 0) :=
  determinant_tendsto_zero_of_prime_exhaustion primorialPackets
    primorialPackets_legal primorialPackets_odd (8 * Real.sqrt 3)
    primorialPackets_charge_bound prime_eventually_mem_primorialPackets

theorem primorial_logarithmicCharge_tendsto_zero :
    Tendsto (fun n => logarithmicCharge (primorialPackets n)) atTop (𝓝 0) :=
  logarithmicCharge_tendsto_zero_of_determinant primorialPackets
    primorialPackets_legal primorialPackets_odd primorial_determinant_tendsto_zero

theorem primorial_mixedCharge_tendsto_neg_two_pi :
    Tendsto (fun n => mixedCharge (primorialPackets n)) atTop (𝓝 (-2 * Real.pi)) :=
  mixedCharge_tendsto_neg_two_pi_of_logarithmic primorialPackets
    primorialPackets_legal primorialPackets_odd (8 * Real.sqrt 3) (by positivity)
    primorialPackets_charge_bound primorial_logarithmicCharge_tendsto_zero

theorem primorialPackets_nested {n m : ℕ} (h : n ≤ m) :
    primorialPackets n ⊆ primorialPackets m :=
  PhysicalCoreMonotonicity.divisorPackets_subset_of_dvd _ _
    (SquarefreeStageExhaustion.primorialPeriod_nested h)
    (ne_of_gt (SquarefreeStageExhaustion.primorialPeriod_pos m))

def signedSourceCorrection (s : Finset ℕ) : ℝ :=
  (2 * Real.pi + mixedCharge s) ^ 2 / (-logarithmicCharge s)

/-- Signed coupling controls the full normalized square by the remaining charge gap. -/
theorem primorial_signedCorrection_le_charge_gap (Cinf : ℝ)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) (n : ℕ) :
    signedSourceCorrection (primorialPackets n) ≤ Cinf - inverseCharge (primorialPackets n) := by
  have h := physical_source_limit_bound primorialPackets n Cinf
    (fun _ h => primorialPackets_nested h) primorialPackets_legal (primorialPackets_odd n)
    primorial_logarithmicCharge_tendsto_zero primorial_mixedCharge_tendsto_neg_two_pi hC
  unfold signedSourceCorrection
  linarith only [h]

theorem primorial_signedCorrection_tendsto_zero (Cinf : ℝ)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) :
    Tendsto (fun n => signedSourceCorrection (primorialPackets n)) atTop (𝓝 0) := by
  have hu : Tendsto (fun n => Cinf - inverseCharge (primorialPackets n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => Cinf) atTop (𝓝 Cinf)).sub hC
  exact squeeze_zero (fun n => div_nonneg (sq_nonneg _)
    (neg_nonneg.mpr (logarithmicCharge_neg _ (primorialPackets_legal n) (primorialPackets_odd n)).le))
    (primorial_signedCorrection_le_charge_gap Cinf hC) hu

theorem primorial_sourceCorrectedCharge_tendsto (Cinf : ℝ)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) :
    Tendsto (fun n => sourceCorrectedCharge (primorialPackets n)) atTop (𝓝 (-Cinf)) := by
  simpa only [sub_zero, sourceCorrectedCharge, signedSourceCorrection] using
    hC.neg.sub (primorial_signedCorrection_tendsto_zero Cinf hC)

theorem sourceProjectionCharge_eq_div_corrected (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    sourceProjectionCharge s = 4 * Real.pi / sourceCorrectedCharge s := by
  rw [physical_correctedCharge_eq_projectionBound s hs ho]
  field_simp [Real.pi_ne_zero, ne_of_gt (sourceProjectionCharge_pos s hs ho)]

theorem primorial_projectionCharge_tendsto (Cinf : ℝ) (hCneg : Cinf < 0)
    (hC : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf)) :
    Tendsto (fun n => sourceProjectionCharge (primorialPackets n))
      atTop (𝓝 (4 * Real.pi / (-Cinf))) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => 4 * Real.pi) atTop (𝓝 (4 * Real.pi))).div
    (primorial_sourceCorrectedCharge_tendsto Cinf hC) (neg_ne_zero.mpr (ne_of_lt hCneg))
  have he : (fun n => sourceProjectionCharge (primorialPackets n)) =
      (fun n => 4 * Real.pi / sourceCorrectedCharge (primorialPackets n)) := by
    funext n
    exact sourceProjectionCharge_eq_div_corrected _ (primorialPackets_legal n) (primorialPackets_odd n)
  rw [he]
  exact h

/-- All source limits and vanishing of the complete normalized signed square
are actual unconditional physical facts. The charge limit remains unidentified. -/
theorem exists_primorial_complete_source_limits :
    ∃ Cinf : ℝ, Cinf ∈ Set.Icc (-8 * Real.sqrt 3) (-4 * Real.pi) ∧
      Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf) ∧
      Tendsto (fun n => logarithmicCharge (primorialPackets n)) atTop (𝓝 0) ∧
      Tendsto (fun n => mixedCharge (primorialPackets n)) atTop (𝓝 (-2 * Real.pi)) ∧
      Tendsto (fun n => shiftedDeterminant (primorialPackets n)) atTop (𝓝 0) ∧
      Tendsto (fun n => signedSourceCorrection (primorialPackets n)) atTop (𝓝 0) ∧
      Tendsto (fun n => sourceProjectionCharge (primorialPackets n))
        atTop (𝓝 (4 * Real.pi / (-Cinf))) := by
  obtain ⟨Cinf, hbound, hC⟩ := SquarefreeStageExhaustion.exists_primorial_charge_limit
  have hC' : Tendsto (fun n => inverseCharge (primorialPackets n)) atTop (𝓝 Cinf) := hC
  have hCneg : Cinf < 0 := hbound.2.trans_lt (by nlinarith [Real.pi_pos])
  exact ⟨Cinf, hbound, hC', primorial_logarithmicCharge_tendsto_zero,
    primorial_mixedCharge_tendsto_neg_two_pi, primorial_determinant_tendsto_zero,
    primorial_signedCorrection_tendsto_zero Cinf hC', primorial_projectionCharge_tendsto Cinf hCneg hC'⟩

end RiemannResearch.RH.Pareto.PhysicalSourceLimits
