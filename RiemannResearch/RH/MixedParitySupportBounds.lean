import RiemannResearch.RH.MixedMobiusWindow
import RiemannResearch.RH.MixedConductorPrimeSupport
import RiemannResearch.RH.MixedConductorCaptureGains
import RiemannResearch.RH.MixedCaptureLegalTrials
import RiemannResearch.RH.CenteredMeanSnake
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.ParetoPrimePackets
import RiemannResearch.RH.ThresholdHilbertDilation
import RiemannResearch.RH.ExactHeadCharges
import RiemannResearch.Analysis.NestedProjectionEnergy
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Prime-support restrictions on mixed approximants to centered parity

The support-layer Parseval identity in the mixed closure leaves a separate
ambient boundary term. A centered Möbius test gives a positive error floor
on each fixed support stage. For the fresh-prime family used to solve finite
heads, even the order-two observation forces the complete energy to grow with
the chosen prime. These estimates use the original Pareto inner product.
-/

noncomputable section
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedMobiusTesting

open CoefficientStabilization CaptureGains MixedConductorBasis

/-- Finite Parseval with the ambient boundary and the remaining mixed-layer
energy both visible. -/
theorem parity_variance_eq_boundary_add_layers (k : ℕ) :
    let p := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)
    Real.log 2 - (Real.log 2)^2 =
      (Real.log 2)^2 * ‖CenteredMeanSnake.boundary‖^2 +
      (∑ j ∈ Finset.range k, ‖(supportLayer j).starProjection p‖^2) +
      ‖p - (supportSpace k).starProjection p‖^2 := by
  intro p
  rw [sum_supportLayer_energy, add_assoc,
    ← RiemannResearch.Analysis.NestedProjectionEnergy.norm_sq_eq_projection_add_residual,
    CenteredMeanSnake.boundary_norm_sq_eq_energy]
  change _ = _ + ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖^2
  rw [full_mixed_capture_eq_limitEnergy]
  field_simp [one_sub_limitEnergy_pos.ne']
  ring

/-- A centered Riesz representer gives a lower bound on the complete error at a
fixed prime-support level. Subtracting its mean improves the dual norm. -/
theorem support_error_floor (k : ℕ) (q : Index) (hq : k < q.val.primeFactors.card)
    (y : mixedClosure) (hy : y ∈ supportSpace k) :
    target q.val ^ 2 ≤
      (‖mobiusDifferenceCLM q.val‖ ^ 2 - (ArithmeticFunction.moebius q.val : ℝ) ^ 2) *
        ‖centeredParity - (y : ThresholdHilbert)‖ ^ 2 := by
  let m := q.val
  let a : ℝ := ArithmeticFunction.moebius m
  let z := centeredParity - (y : ThresholdHilbert)
  let r := mobiusRieszHilbert m - a • hilbertOne
  have hm : 0 < m := Nat.zero_lt_one.trans q.property.1
  have hmean : inner ℝ centeredParity hilbertOne = 0 := by
    rw [centeredParity, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      hilbertOne_norm_sq, hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
      paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    simp
  have hmu : inner ℝ (mobiusRieszHilbert m) hilbertOne = a :=
    (mobiusRieszHilbert_inner _ _).trans (mobius_coordinate_one _ hm)
  have hym : inner ℝ (y : ThresholdHilbert) hilbertOne = 0 :=
    mixedClosure.inner_right_of_mem_orthogonal y.property one_mem_mixedClosure_orthogonal
  have hz : inner ℝ hilbertOne z = 0 := by
    rw [real_inner_comm, inner_sub_left, hmean, hym, sub_zero]
  have hdy : mobiusDifferenceCLM m (y : ThresholdHilbert) = 0 :=
    supportSpace_le_coordinate_ker q hq hy
  have hpair : inner ℝ r z = target m := by
    rw [inner_sub_left, real_inner_smul_left, hz, mul_zero, sub_zero,
      mobiusRieszHilbert_inner, map_sub, hdy, sub_zero, target_eq_coordinate _ q.property.1]
  have hnorm : ‖r‖ ^ 2 = ‖mobiusDifferenceCLM m‖ ^ 2 - a ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, hmu, mobiusRieszHilbert_norm,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hilbertOne_norm_sq]
    ring
  have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (abs_real_inner_le_norm r z)
  rw [sq_abs, hpair, mul_pow, hnorm] at h
  exact h

/-- The complete two-prime space leaves a positive squared error, even with
unbounded conductors in that space. The denominator is the centered dual energy. -/
theorem two_prime_error_floor (y : mixedClosure) (hy : y ∈ supportSpace 2) :
    (Real.log 2) ^ 2 / 2651 ≤ ‖centeredParity - (y : ThresholdHilbert)‖ ^ 2 := by
  let q : Index := ⟨30, by decide, by decide⟩
  have hq : 2 < q.val.primeFactors.card := by decide +kernel
  have h := support_error_floor 2 q hq y hy
  have hn : ‖mobiusDifferenceCLM 30‖ ^ 2 = 2652 := by
    rw [mobiusDifferenceCLM_norm_sq _ (by decide)]
    have hZ : (∑ j ∈ Finset.Icc (1 : ℕ) 30,
        (j : ℤ) * (j + 1 : ℤ) * dualCoeff 30 j ^ 2) = 2652 := by decide +kernel
    exact_mod_cast hZ
  have hmu : ArithmeticFunction.moebius 30 = (-1 : ℤ) := by decide +kernel
  change target 30 ^ 2 ≤ (‖mobiusDifferenceCLM 30‖ ^ 2 -
    (ArithmeticFunction.moebius 30 : ℝ) ^ 2) * _ at h
  rw [target, incidence, if_neg (by decide : ¬30 ∣ 2), hmu, hn] at h
  norm_num at h
  linarith

private theorem exists_squarefree_card (r : ℕ) :
    ∃ n : ℕ, n ≠ 0 ∧ Squarefree n ∧ n.primeFactors.card = r := by
  induction r with
  | zero => exact ⟨1, one_ne_zero, squarefree_one, by simp⟩
  | succ r ih =>
    obtain ⟨n, hn, hs, hc⟩ := ih
    obtain ⟨p, hp, hp'⟩ := Nat.exists_infinite_primes (n + 1)
    have hpn : ¬ p ∣ n := fun h => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h; omega
    have hf : p ∉ n.primeFactors := fun h => hpn (Nat.dvd_of_mem_primeFactors h)
    refine ⟨p * n, Nat.mul_ne_zero hp'.ne_zero hn,
      (Nat.squarefree_mul (hp'.coprime_iff_not_dvd.mpr hpn)).mpr ⟨hp'.squarefree, hs⟩, ?_⟩
    rw [Nat.primeFactors_mul hp'.ne_zero hn, hp'.primeFactors, Finset.singleton_union,
      Finset.card_insert_of_notMem hf, hc]

/-- A fresh squarefree row gives one positive lower bound for the entire closed
support stage, independent of the largest conductor allowed there. -/
theorem fixed_support_positive_floor (k : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : mixedClosure, y ∈ supportSpace k →
      δ ≤ ‖centeredParity - (y : ThresholdHilbert)‖ ^ 2 := by
  obtain ⟨n, hn, hs, hc⟩ := exists_squarefree_card (k + 2)
  have hn2 : 2 < n := by
    by_contra! hle
    interval_cases n <;> norm_num [Nat.prime_two.primeFactors] at *
  let q : Index := ⟨n, by omega, fun hp => by
    have h1 := isPrimePow_iff_card_primeFactors_eq_one.mp hp
    omega⟩
  have hq : k < q.val.primeFactors.card := by change k < n.primeFactors.card; omega
  have ht : target n ≠ 0 := by
    have hnd : ¬n ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide : 0 < 2) h; omega
    have hμ : (ArithmeticFunction.moebius n : ℝ) ≠ 0 := by
      exact_mod_cast ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hs
    simp [target, incidence, hnd, hμ, (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne']
  let D := ‖mobiusDifferenceCLM n‖ ^ 2 - (ArithmeticFunction.moebius n : ℝ) ^ 2
  have hf (y : mixedClosure) (hy : y ∈ supportSpace k) :
      target n ^ 2 ≤ D * ‖centeredParity - (y : ThresholdHilbert)‖ ^ 2 :=
    support_error_floor k q hq y hy
  have hD : 0 < D := by
    have hp := (sq_pos_of_ne_zero ht).trans_le (hf 0 ((supportSpace k).zero_mem))
    exact (pos_of_mul_pos_left hp (sq_nonneg _))
  exact ⟨_, div_pos (sq_pos_of_ne_zero ht) hD, fun y hy =>
    (div_le_iff₀ hD).mpr (by simpa only [mul_comm D] using hf y hy)⟩

/-- At a fresh prime the whole packet combination is one dilation difference. -/
theorem fresh_packet_combination (s : ℕ) (hs : s.Prime) (F : Finset ℕ) (a : ℕ → ℝ)
    (hF : ∀ d ∈ F, 1 < d ∧ ¬s ∣ d) :
    let f := ∑ d ∈ F, a d • ramanujanPacketHilbert d
    (∑ d ∈ F, a d • ramanujanPacketHilbert (s*d)) = hilbertDilation s hs.pos f - f := by
  intro f
  have hp (d : ℕ) (hd : d ∈ F) : ramanujanPacketHilbert (s*d) =
      hilbertDilation s hs.pos (ramanujanPacketHilbert d) - ramanujanPacketHilbert d := by
    apply hilbertSequence_injective
    funext n
    simpa only [hilbertSequence_sub, Pi.sub_apply, hilbertDilation_sequence,
      hilbertSequence_ramanujanPacketHilbert] using
      ramanujanPacket_mul_prime_of_not_dvd s d n hs (hF d hd).1 (hF d hd).2
  change _ = hilbertDilationLinear s hs.pos (∑ d ∈ F, a d • ramanujanPacketHilbert d) -
    ∑ d ∈ F, a d • ramanujanPacketHilbert d
  rw [map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hp d hd, smul_sub, map_smul]
  rfl

/-- Matching the order-two observation using a single delayed dilation
has a squared cost that grows at least linearly with the dilation scale. -/
theorem fresh_dilation_cost_floor (s : ℕ) (hs : 2 < s) (f : ThresholdHilbert)
    (hmatch : mobiusDifferenceCLM 2 (hilbertDilation s (by omega) f - f) = target 2) :
    (Real.sqrt (s : ℝ) - 1)^2 * (2 - Real.log 2)^2 ≤
      14 * ‖hilbertDilation s (by omega) f - f‖^2 := by
  let d := hilbertDilation s (by omega) f
  have hd : mobiusDifferenceCLM 2 d = 0 := by
    calc
      _ = mobiusDifferenceCLM 2 (0 : ThresholdHilbert) := by
        simp only [mobiusDifferenceCLM_apply]
        apply mobiusDifference_congr_initial (N := 2) le_rfl
        intro k hk
        rw [← anchoredEvaluationCLM_apply k (0 : ThresholdHilbert), map_zero]
        simp [d, hilbertDilation_sequence, dilation, Nat.div_eq_of_lt (hk.trans_lt hs)]
      _ = 0 := map_zero _
  have ht : target 2 = -2 + Real.log 2 := by
    simp [target, incidence, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  change mobiusDifferenceCLM 2 (d-f) = target 2 at hmatch
  rw [map_sub, hd, zero_sub, ht] at hmatch
  have hp : mobiusDifferenceCLM 2 f = 2 - Real.log 2 := by linarith
  have hn : ‖mobiusDifferenceCLM 2‖^2 = 14 := by
    rw [mobiusDifferenceCLM_norm_sq 2 (by decide)]
    have hZ : (∑ j ∈ Finset.Icc (1 : ℕ) 2,
        (j : ℤ) * (j + 1 : ℤ) * dualCoeff 2 j ^ 2) = 14 := by decide +kernel
    exact_mod_cast hZ
  have hb := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    ((mobiusDifferenceCLM 2).le_opNorm f)
  rw [Real.norm_eq_abs, sq_abs, hp, mul_pow, hn] at hb
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (show 1 ≤ s by omega)
  have hroot : 0 ≤ Real.sqrt (s : ℝ) - 1 := by
    have h := Real.sqrt_le_sqrt hsR
    simpa only [Real.sqrt_one, sub_nonneg] using h
  have hr : (Real.sqrt (s : ℝ) - 1) * ‖f‖ ≤ ‖d-f‖ := by
    calc
      _ = Real.sqrt (s : ℝ) * ‖f‖ - ‖f‖ := by ring
      _ = ‖d‖ - ‖f‖ := by rw [show ‖d‖ = _ from hilbertDilation_norm s _ f]
      _ ≤ _ := norm_sub_norm_le d f
  have hr2 := (sq_le_sq₀ (mul_nonneg hroot (norm_nonneg f)) (norm_nonneg _)).mpr hr
  calc
    _ ≤ (Real.sqrt (s : ℝ) - 1)^2 * (14 * ‖f‖^2) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = 14 * ((Real.sqrt (s : ℝ) - 1) * ‖f‖)^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr2 (by norm_num)

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedMobiusTesting
