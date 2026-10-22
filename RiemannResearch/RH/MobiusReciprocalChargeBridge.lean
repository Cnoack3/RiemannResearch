import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.NumberTheory.MobiusReciprocalSum

/-!
# Finite reciprocal-charge Riesz bridge

Source: Balazard, arXiv:1812.04309, Proposition 7, for the reciprocal
Möbius-charge kernel. The finite divisor reindexing is proved explicitly.
This module identifies the Riesz vector; convergence requires a separate
uniform norm bound and weak-limit argument.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative

/-- Reindex a reciprocal sum over positive multiples of a fixed modulus. -/
theorem reciprocal_dilation_sum (N d : ℕ) (hd : 0 < d) (F : ℕ → ℝ) :
    (∑ m ∈ Finset.Icc 1 N,
      (if d ∣ m then F (m / d) else 0) / (m : ℝ)) =
      (1 / (d : ℝ)) * ∑ r ∈ Finset.Icc 1 (N / d), F r / (r : ℝ) := by
  classical
  simp only [ite_div, zero_div]
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_bij (fun m _ => m / d) ?_ ?_ ?_ ?_
  · intro m hm
    have hmI := Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1
    have hdm := (Finset.mem_filter.mp hm).2
    apply Finset.mem_Icc.mpr
    constructor
    · apply (Nat.le_div_iff_mul_le hd).mpr
      simpa using Nat.le_of_dvd (show 0 < m by omega) hdm
    · exact Nat.div_le_div_right hmI.2
  · intro m hm n hn he
    have hmdiv := Nat.div_mul_cancel (Finset.mem_filter.mp hm).2
    have hndiv := Nat.div_mul_cancel (Finset.mem_filter.mp hn).2
    calc
      m = (m / d) * d := hmdiv.symm
      _ = (n / d) * d := by rw [he]
      _ = n := hndiv
  · intro r hr
    have hrI := Finset.mem_Icc.mp hr
    have hrN : r * d ≤ N := (Nat.le_div_iff_mul_le hd).mp hrI.2
    have hdvd : d ∣ r * d := ⟨r, by ring⟩
    have hq : (r * d) / d = r := by
      apply Nat.eq_of_mul_eq_mul_left hd
      simpa only [Nat.mul_comm] using Nat.div_mul_cancel hdvd
    refine ⟨r * d, Finset.mem_filter.mpr ⟨?_, hdvd⟩, hq⟩
    exact Finset.mem_Icc.mpr ⟨by nlinarith, hrN⟩
  · intro m hm
    have hdm := (Finset.mem_filter.mp hm).2
    have hmR : (m : ℝ) = ((m / d : ℕ) : ℝ) * (d : ℝ) := by
      exact_mod_cast (Nat.div_mul_cancel hdm).symm
    rw [hmR]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Exact finite reciprocal sum of the full, overlapping divisor coefficients. -/
theorem reciprocal_dualCoeff_sum (N k : ℕ) (hk : 0 < k) :
    (∑ m ∈ Finset.Icc 1 N, (dualCoeff m k : ℝ) / (m : ℝ)) =
      mobiusReciprocalSum (N / k) / (k : ℝ) -
        mobiusReciprocalSum (N / (k + 1)) / ((k : ℝ) + 1) := by
  have hdual (m : ℕ) : (dualCoeff m k : ℝ) =
      (if k ∣ m then (ArithmeticFunction.moebius (m / k) : ℝ) else 0) -
        (if k + 1 ∣ m then (ArithmeticFunction.moebius (m / (k + 1)) : ℝ) else 0) := by
    unfold dualCoeff
    split_ifs <;> push_cast <;> ring
  simp_rw [hdual, sub_div]
  rw [Finset.sum_sub_distrib,
    reciprocal_dilation_sum N k hk (fun n => (ArithmeticFunction.moebius n : ℝ)),
    reciprocal_dilation_sum N (k + 1) (by omega) (fun n => (ArithmeticFunction.moebius n : ℝ))]
  simp only [mobiusReciprocalSum, Nat.cast_add, Nat.cast_one]
  ring

/-- Riesz vector representing the ordered reciprocal-charge functional. -/
def reciprocalChargeRiesz (N : ℕ) : ThresholdHilbert :=
  ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)) • mobiusRieszHilbert m

theorem reciprocalChargeRiesz_inner (N : ℕ) (f : ThresholdHilbert) :
    inner ℝ (reciprocalChargeRiesz N) f =
      ∑ m ∈ Finset.Icc 1 N, mobiusDifferenceCLM m f / (m : ℝ) := by
  simp only [reciprocalChargeRiesz, sum_inner, inner_smul_left,
    mobiusRieszHilbert_inner, conj_trivial]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Physical coordinates of the reciprocal-charge Riesz vector, with signs retained. -/
theorem reciprocalChargeRiesz_sequence (N k : ℕ) (hk : 0 < k) :
    hilbertSequence (reciprocalChargeRiesz N) k =
      (k : ℝ) * ((k : ℝ) + 1) *
        (mobiusReciprocalSum (N / k) / (k : ℝ) -
          mobiusReciprocalSum (N / (k + 1)) / ((k : ℝ) + 1)) := by
  rw [← anchoredEvaluationCLM_apply]
  simp only [reciprocalChargeRiesz, map_sum, map_smul, smul_eq_mul,
    anchoredEvaluationCLM_apply]
  calc
    _ = (k : ℝ) * ((k : ℝ) + 1) *
        (∑ m ∈ Finset.Icc 1 N, (dualCoeff m k : ℝ) / (m : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [mobiusRieszHilbert_sequence m k (by have := (Finset.mem_Icc.mp hm).1; omega)]
      ring
    _ = _ := by rw [reciprocal_dualCoeff_sum N k hk]

/-- The last physical coordinate remains large despite fixed-coordinate decay. -/
theorem reciprocalChargeRiesz_endpoint (N : ℕ) (hN : 0 < N) :
    hilbertSequence (reciprocalChargeRiesz N) N = (N : ℝ) + 1 := by
  rw [reciprocalChargeRiesz_sequence N N hN,
    Nat.div_self hN, Nat.div_eq_of_lt (by omega)]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  norm_num [mobiusReciprocalSum]
  field_simp [hNR] <;> ring

/-- A single escaping endpoint supplies a persistent lower norm bound. -/
theorem reciprocalChargeRiesz_norm_sq_lower (N : ℕ) (hN : 0 < N) :
    ((N : ℝ) + 1) / (N : ℝ) ≤ ‖reciprocalChargeRiesz N‖ ^ 2 := by
  have hb := (hilbertSequence_square_summable (reciprocalChargeRiesz N)).le_tsum N
    (fun k _ => by unfold positiveWeight; positivity)
  rw [← hilbert_norm_weighted_sq, reciprocalChargeRiesz_endpoint N hN] at hb
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  have hN1R : (N : ℝ) + 1 ≠ 0 := by positivity
  have he : positiveWeight N * ((N : ℝ) + 1) ^ 2 = ((N : ℝ) + 1) / (N : ℝ) := by
    unfold positiveWeight
    field_simp [hNR, hN1R]
  rwa [he] at hb

/-- Reciprocal-charge Riesz vectors cannot converge to zero in norm. -/
theorem reciprocalChargeRiesz_not_tendsto_zero :
    ¬ Tendsto reciprocalChargeRiesz atTop (𝓝 (0 : ThresholdHilbert)) := by
  intro ht
  have hs : Tendsto (fun N => ‖reciprocalChargeRiesz N‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using ht.norm.pow 2
  have hl : (1 : ℝ) ≤ 0 := by
    apply ge_of_tendsto hs
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hratio : (1 : ℝ) ≤ ((N : ℝ) + 1) / (N : ℝ) := by
      apply (le_div_iff₀ hNR).mpr
      linarith
    exact hratio.trans (reciprocalChargeRiesz_norm_sq_lower N (by omega))
  norm_num at hl


end RiemannResearch.RH.Pareto
