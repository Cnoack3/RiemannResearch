/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ExactHeadResidualTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Hilbert tail rates compatible with sublinear divergent head energy

Source: the user's request to combine the residual/energy dichotomy with PNT,
24 September 2026; the explicit compatibility construction developed in this
audit. No novelty claim is made.

The actual arithmetic input in CanonicalMobiusPNT gives sublinear canonical
energy. ParetoResidualTailDichotomy uses that input to obtain divergence of
normalized tails in the positive residual branch. These facts supply no
opposing upper bound on those tails.

This module realizes any decreasing zero-limit sequence as an exact Hilbert
tail energy. It then constructs a hyperplane orthogonal to a unit vector in
the same Pareto Hilbert space, and exact constant-head vectors in that
hyperplane whose full error energy is c^2 * sqrt(N+1), for c>0.

This is a counterexample to the inference from these analytic properties
alone. The hyperplane is not identified with the arithmetic legal space;
the module does not refute RH or assert an arithmetic counterexample.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto

/-- Nonnegative differences of any decreasing sequence tending to zero are
the squared coordinates of a Hilbert vector with exactly that tail energy. -/
theorem exists_hilbert_of_tail_energy
    (t : ℕ → ℝ) (ht : Antitone t)
    (hzero : Tendsto t atTop (𝓝 0)) :
    ∃ f : ThresholdHilbert,
      (∀ n, f n = Real.sqrt (t n - t (n + 1))) ∧
      ∀ N, ‖hilbertTailShift f N‖ ^ 2 = t N := by
  have hd (n : ℕ) : 0 ≤ t n - t (n + 1) :=
    sub_nonneg.mpr (ht (Nat.le_succ n))
  have hsum (N : ℕ) :
      (∑ n ∈ Finset.range N, (Real.sqrt (t n - t (n + 1))) ^ 2) =
        t 0 - t N := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, Real.sq_sqrt (hd N)]
      ring
  have hhas : HasSum (fun n => (Real.sqrt (t n - t (n + 1))) ^ 2) (t 0) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => sq_nonneg _) _).2
    simp_rw [hsum]
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := t 0)).sub hzero
  let f : ThresholdHilbert := ⟨fun n => Real.sqrt (t n - t (n + 1)), by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
      using hhas.summable⟩
  refine ⟨f, fun _ => rfl, ?_⟩
  intro N
  rw [hilbertTailShift_norm_sq, hilbert_norm_sq]
  change (∑' n, (Real.sqrt (t n - t (n + 1))) ^ 2) -
    (∑ n ∈ Finset.range N, (Real.sqrt (t n - t (n + 1))) ^ 2) = t N
  rw [hhas.tsum_eq, hsum]
  ring

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto

/-- The physical tail, retaining its original coordinate indices. -/
def hilbertTailMask (f : ThresholdHilbert) (N : ℕ) : ThresholdHilbert :=
  ⟨fun n => if n < N then 0 else f n, by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      (hilbert_coordinate_square_summable f)
    split_ifs <;> simp [sq_nonneg]⟩

theorem hilbertTailMask_head (f : ThresholdHilbert) (N : ℕ) {n : ℕ}
    (hn : n < N) : hilbertTailMask f N n = 0 := by
  change (if n < N then 0 else f n) = 0
  simp [hn]

theorem hilbertTailMask_shift (f : ThresholdHilbert) (N : ℕ) :
    hilbertTailShift (hilbertTailMask f N) N = hilbertTailShift f N := by
  ext n
  change (if n + N < N then 0 else f (n + N)) = f (n + N)
  simp [show ¬ n + N < N by omega]

theorem hilbertTailMask_norm_sq (f : ThresholdHilbert) (N : ℕ) :
    ‖hilbertTailMask f N‖ ^ 2 = ‖hilbertTailShift f N‖ ^ 2 := by
  have h := hilbertTailShift_inner (hilbertTailMask f N) (hilbertTailMask f N) N
    (fun _ hn => hilbertTailMask_head f N hn)
  simp only [hilbertTailMask_shift, real_inner_self_eq_norm_sq] at h
  exact h.symm

theorem hilbertTailMask_pairing (f : ThresholdHilbert) (N : ℕ) :
    inner ℝ f (hilbertTailMask f N) = ‖hilbertTailShift f N‖ ^ 2 := by
  have h := hilbertTailShift_inner f (hilbertTailMask f N) N
    (fun _ hn => hilbertTailMask_head f N hn)
  simp only [hilbertTailMask_shift, real_inner_self_eq_norm_sq] at h
  exact h.symm

/-- Exact-head approximation within the hyperplane orthogonal to a fixed
residual. The complete error energy realizes equality in the tail-product
bound; this does not identify that hyperplane with the arithmetic legal span. -/
theorem exists_hyperplane_exact_head_error
    (r g : ThresholdHilbert) (N : ℕ)
    (hT : 0 < ‖hilbertTailShift r N‖ ^ 2) :
    ∃ f : ThresholdHilbert,
      inner ℝ r f = 0 ∧
      (∀ n < N, f n = g n) ∧
      ‖g - f‖ ^ 2 = (inner ℝ r g) ^ 2 / ‖hilbertTailShift r N‖ ^ 2 ∧
      ‖hilbertTailShift r N‖ ^ 2 * ‖g - f‖ ^ 2 = (inner ℝ r g) ^ 2 := by
  let T : ℝ := ‖hilbertTailShift r N‖ ^ 2
  let c : ℝ := inner ℝ r g
  let e : ThresholdHilbert := (c / T) • hilbertTailMask r N
  let f : ThresholdHilbert := g - e
  have hTne : T ≠ 0 := ne_of_gt hT
  have he : g - f = e := by dsimp [f]; abel
  have hnorm : ‖e‖ ^ 2 = c ^ 2 / T := by
    dsimp [e]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hilbertTailMask_norm_sq]
    change (c / T) ^ 2 * T = c ^ 2 / T
    field_simp [hTne]
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · change inner ℝ r (g - (c / T) • hilbertTailMask r N) = 0
    rw [inner_sub_right, inner_smul_right, hilbertTailMask_pairing]
    change c - (c / T) * T = 0
    field_simp [hTne]
    ring
  · intro n hn
    change g n - (c / T) * hilbertTailMask r N n = g n
    rw [hilbertTailMask_head r N hn, mul_zero, sub_zero]
  · rw [he, hnorm]
  · rw [he, hnorm]
    change T * (c ^ 2 / T) = c ^ 2
    field_simp [hTne]

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto

theorem hilbertOne_coordinate_pos (n : ℕ) : 0 < hilbertOne n := by
  change 0 < Real.sqrt (paretoWeight n) * (if n + 1 = 0 then 0 else 1)
  simp only [if_neg (show n + 1 ≠ 0 by omega), mul_one]
  apply Real.sqrt_pos.mpr
  unfold paretoWeight
  positivity

theorem inner_hilbertOne_pos_of_nonneg
    (g : ThresholdHilbert) (hg : ∀ n, 0 ≤ g n) (hg0 : 0 < g 0) :
    0 < inner ℝ g hilbertOne := by
  have he : inner ℝ g hilbertOne = ∑' n, g n * hilbertOne n := by
    simp only [lp.inner_eq_tsum, RCLike.inner_apply, conj_trivial, mul_comm]
  rw [he]
  exact (hilbert_coordinate_mul_summable g hilbertOne).tsum_pos
    (fun n => mul_nonneg (hg n) (hilbertOne_coordinate_pos n).le) 0
    (mul_pos hg0 (hilbertOne_coordinate_pos 0))

end RiemannResearch.RH.Pareto


namespace RiemannResearch.RH.Pareto.TailRateCompatibility

def modelEnergy (N : ℕ) : ℝ := Real.sqrt ((N : ℝ) + 1)
def modelTail (N : ℕ) : ℝ := (modelEnergy N)⁻¹

theorem modelEnergy_pos (N : ℕ) : 0 < modelEnergy N := by
  apply Real.sqrt_pos.mpr
  positivity

theorem modelEnergy_sq (N : ℕ) : (modelEnergy N)^2 = (N : ℝ) + 1 :=
  Real.sq_sqrt (by positivity)

theorem modelTail_energy_product (N : ℕ) : modelTail N * modelEnergy N = 1 := by
  exact inv_mul_cancel₀ (modelEnergy_pos N).ne'

theorem modelTail_antitone : Antitone modelTail := by
  intro M N hMN
  exact inv_anti₀ (modelEnergy_pos M)
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hMN 1))

theorem modelEnergy_tendsto_atTop : Tendsto modelEnergy atTop atTop := by
  apply Real.tendsto_sqrt_atTop.comp
  exact tendsto_atTop_mono (fun N => by linarith)
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)

theorem modelTail_tendsto_zero : Tendsto modelTail atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp modelEnergy_tendsto_atTop

theorem modelEnergy_div_succ (N : ℕ) :
    modelEnergy N / ((N : ℝ) + 1) = modelTail N := by
  rw [← modelEnergy_sq]
  unfold modelTail
  field_simp

theorem modelEnergy_div_nat_tendsto_zero :
    Tendsto (fun N : ℕ => modelEnergy N / (N : ℝ)) atTop (𝓝 0) := by
  have hu : Tendsto (fun N => 2 * modelTail N) atTop (𝓝 0) := by
    simpa using modelTail_tendsto_zero.const_mul 2
  apply squeeze_zero' (Eventually.of_forall (fun N => by
    exact div_nonneg (modelEnergy_pos N).le (Nat.cast_nonneg N))) _ hu
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he := modelEnergy_pos N
  have hsq := modelEnergy_sq N
  unfold modelTail
  apply (div_le_iff₀ hNR).mpr
  rw [show 2 * (modelEnergy N)⁻¹ * (N : ℝ) = (modelEnergy N)⁻¹ * (2 * (N : ℝ)) by ring]
  apply (le_inv_mul_iff₀ he).mpr
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

theorem model_normalized_tail_tendsto_atTop :
    Tendsto (fun N : ℕ => (N : ℝ) * modelTail N) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  have hB := modelEnergy_tendsto_atTop.eventually (eventually_ge_atTop (2 * max B 0))
  filter_upwards [hB, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have he := modelEnergy_pos N
  have hsq := modelEnergy_sq N
  change B ≤ (N : ℝ) * (modelEnergy N)⁻¹
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ he).mpr
  have hprod := mul_le_mul_of_nonneg_right hN he.le
  have hmax := le_max_left B 0
  nlinarith


theorem exists_hilbert_model :
    ∃ f : ThresholdHilbert,
      ‖f‖ ^ 2 = 1 ∧
      (∀ N, ‖hilbertTailShift f N‖ ^ 2 = modelTail N) ∧
      (∀ N, ‖hilbertTailShift f N‖ ^ 2 * modelEnergy N = 1) ∧
      Tendsto (fun N : ℕ => (N : ℝ) * ‖hilbertTailShift f N‖ ^ 2) atTop atTop ∧
      Tendsto (fun N => modelEnergy N / (N : ℝ)) atTop (𝓝 0) := by
  obtain ⟨f, hf, ht⟩ := exists_hilbert_of_tail_energy modelTail
    modelTail_antitone modelTail_tendsto_zero
  refine ⟨f, ?_, ht, fun N => ?_, ?_, modelEnergy_div_nat_tendsto_zero⟩
  · have h := ht 0
    simpa [hilbertTailShift_norm_sq, modelTail, modelEnergy] using h
  · rw [ht N]
    exact modelTail_energy_product N
  · simpa only [ht] using model_normalized_tail_tendsto_atTop


/-- A hyperplane admits exact constant-head vectors with divergent but
sublinear error energy. This is a countermodel to an inference from these
analytic properties alone, not a model of the arithmetic legal span. -/
theorem exists_hyperplane_exact_head_sublinear_divergence :
    ∃ r : ThresholdHilbert, ∃ c : ℝ, 0 < c ∧
      inner ℝ r hilbertOne = c ∧
      ‖r‖ ^ 2 = 1 ∧
      (∀ N, ‖hilbertTailShift r N‖ ^ 2 = modelTail N) ∧
      ∃ F : ℕ → ThresholdHilbert,
        (∀ N, inner ℝ r (F N) = 0 ∧
          (∀ k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1) ∧
          ‖hilbertOne - F N‖ ^ 2 = c ^ 2 * modelEnergy N) ∧
        Tendsto (fun N => ‖hilbertOne - F N‖ ^ 2) atTop atTop ∧
        Tendsto (fun N : ℕ => ‖hilbertOne - F N‖ ^ 2 / (N : ℝ))
          atTop (𝓝 0) := by
  obtain ⟨r, hr, ht⟩ := exists_hilbert_of_tail_energy modelTail
    modelTail_antitone modelTail_tendsto_zero
  have hr0 : 0 < r 0 := by
    rw [hr]
    apply Real.sqrt_pos.mpr
    have he : 1 < modelEnergy 1 := by
      have hs := modelEnergy_sq 1
      have hp := modelEnergy_pos 1
      norm_num at hs
      nlinarith
    have hi : (modelEnergy 1)⁻¹ < 1 := (inv_lt_one₀ (modelEnergy_pos 1)).mpr he
    have hz : modelTail 0 = 1 := by norm_num [modelTail, modelEnergy]
    rw [hz]
    change 0 < 1 - (modelEnergy 1)⁻¹
    linarith
  let c := inner ℝ r hilbertOne
  have hc : 0 < c := inner_hilbertOne_pos_of_nonneg r
    (fun n => by rw [hr]; exact Real.sqrt_nonneg _) hr0
  have hn : ‖r‖ ^ 2 = 1 := by
    have hh := ht 0
    simpa [hilbertTailShift_norm_sq, modelTail, modelEnergy] using hh
  have htailpos (N : ℕ) : 0 < ‖hilbertTailShift r N‖ ^ 2 := by
    rw [ht]
    exact inv_pos.mpr (modelEnergy_pos N)
  choose F horth hhead herr hproduct using
    fun N => exists_hyperplane_exact_head_error r hilbertOne N (htailpos N)
  have herr' (N : ℕ) : ‖hilbertOne - F N‖ ^ 2 = c ^ 2 * modelEnergy N := by
    rw [herr, ht]
    change c ^ 2 / (modelEnergy N)⁻¹ = c ^ 2 * modelEnergy N
    simp [div_eq_mul_inv]
  refine ⟨r, c, hc, rfl, hn, ht, F, ?_, ?_, ?_⟩
  · intro N
    refine ⟨horth N, ?_, herr' N⟩
    intro k hk hkN
    have hsame : hilbertSequence (F N) k = hilbertSequence hilbertOne k := by
      cases k with
      | zero => simp
      | succ n =>
        simp only [hilbertSequence_succ, hhead N n (by omega)]
    rw [hsame, hilbertOne_sequence]
    simp [zeroAnchor, Nat.ne_of_gt hk]
  · have h := Filter.Tendsto.atTop_mul_const (sq_pos_of_pos hc)
      modelEnergy_tendsto_atTop
    simpa only [herr', mul_comm] using h
  · have h := modelEnergy_div_nat_tendsto_zero.const_mul (c ^ 2)
    simpa only [herr', mul_div_assoc, mul_zero] using h

end RiemannResearch.RH.Pareto.TailRateCompatibility
