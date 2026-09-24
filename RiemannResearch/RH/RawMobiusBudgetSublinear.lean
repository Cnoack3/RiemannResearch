import RiemannResearch.RH.RawMobiusSubpowerCriterion
import RiemannResearch.RH.CanonicalMobiusPNT

/-!
# Unconditional sublinear growth of the finite raw Mobius budget

The actual PNT provider makes B_N/N tend to zero. This does not supply
the cofinal estimates at every positive exponent required by the subpower
RH criterion. Every physical tail is retained in the norm comparisons.

Source: the user's Nyman--Beurling research request, September 24, 2026.
The unconditional analytic inputs are the catalogued theorems
`canonicalMobiusHilbert_sublinear` and `mobiusReciprocalSum_tendsto_zero`
from `CanonicalMobiusPNT`; the finite-energy comparisons are proved here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

private theorem norm_add_sq_sublinear (f g : ThresholdHilbert) :
    ‖f+g‖^2 ≤ 2*‖f‖^2+2*‖g‖^2 := by
  have hh := mul_self_le_mul_self (norm_nonneg (f+g)) (norm_add_le f g)
  nlinarith [sq_nonneg (‖f‖-‖g‖)]

/-- The finite middle interval is part of the complete nonnegative energy. -/
theorem rawMobiusMiddleEnergy_square_le_norm_sq (N : ℕ) (hN : 0 < N) :
    rawMobiusMiddleEnergy N (N^2) ≤ ‖hilbertOne-rawMobiusHilbert N‖^2 := by
  have he := rawMobius_energy_three_regions N (N^2) (by nlinarith)
  have hh : 0 ≤ (mobiusReciprocalSum N)^2 *
      (∑ k ∈ Finset.range (N+1), (k : ℝ)/((k : ℝ)+1)) := by positivity
  have hf := rawMobiusFarEnergy_nonneg N (N^2)
  linarith

/-- Reverse comparison: the finite budget is bounded by the exact-head energy
    and its already known reciprocal-Mobius correction. -/
theorem rawMobiusSquareBudget_le_canonical_energy (N : ℕ) (hN : 0 < N) :
    rawMobiusSquareBudget N ≤
      4*‖canonicalMobiusHilbert N‖^2+4+
        9*(N : ℝ)*(mobiusReciprocalSum N)^2 := by
  let c := (((N+1 : ℕ) : ℝ)*mobiusReciprocalSum N) •
    normalizedResidueHilbert (N+1) (Nat.succ_pos N)
  have hc := canonicalMobius_correction_norm_sq_le_head N hN
  change ‖c‖^2 ≤ _ at hc
  have hres := norm_add_sq_sublinear hilbertOne (-canonicalMobiusHilbert N)
  simp only [norm_neg, hilbertOne_norm_sq, ← sub_eq_add_neg] at hres
  have heq : hilbertOne-rawMobiusHilbert N =
      (hilbertOne-canonicalMobiusHilbert N)+c := by
    rw [canonicalMobiusHilbert_eq_raw_add]
    change hilbertOne-rawMobiusHilbert N = (hilbertOne-(rawMobiusHilbert N+c))+c
    abel
  have hU := norm_add_sq_sublinear (hilbertOne-canonicalMobiusHilbert N) c
  rw [← heq] at hU
  have hm := rawMobiusMiddleEnergy_square_le_norm_sq N hN
  unfold rawMobiusSquareBudget
  nlinarith

theorem rawMobiusSquareBudget_div_le (N : ℕ) (hN : 0 < N) :
    rawMobiusSquareBudget N/(N : ℝ) ≤
      4*(‖canonicalMobiusHilbert N‖^2/(N : ℝ))+4/(N : ℝ)+
        9*(mobiusReciprocalSum N)^2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := div_le_div_of_nonneg_right
    (rawMobiusSquareBudget_le_canonical_energy N hN) hNR.le
  calc
    _ ≤ (4*‖canonicalMobiusHilbert N‖^2+4+
        9*(N : ℝ)*(mobiusReciprocalSum N)^2)/(N : ℝ) := hb
    _ = _ := by field_simp [hNR.ne']

/-- Actual unconditional endpoint: the finite arithmetic budget divided by N
    tends to zero, using only the already verified PNT cancellation. -/
theorem rawMobiusSquareBudget_sublinear :
    Tendsto (fun N => rawMobiusSquareBudget N/(N : ℝ)) atTop (𝓝 0) := by
  have hF := canonicalMobiusHilbert_sublinear.const_mul 4
  have hm := (mobiusReciprocalSum_tendsto_zero.pow 2).const_mul 9
  have hi := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 4
  have ht : Tendsto (fun N : ℕ =>
      4*(‖canonicalMobiusHilbert N‖^2/(N : ℝ))+4/(N : ℝ)+
        9*(mobiusReciprocalSum N)^2) atTop (𝓝 0) := by
    have h := (hF.add hi).add hm
    simpa only [mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add,
      mul_one_div] using h
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun N => ha.trans_le
      (div_nonneg (rawMobiusSquareBudget_nonneg N) (Nat.cast_nonneg N)))
  · intro b hb
    filter_upwards [ht.eventually (gt_mem_nhds hb), eventually_ge_atTop 1]
      with N hNb hN
    exact (rawMobiusSquareBudget_div_le N (by omega)).trans_lt hNb

end RiemannResearch.RH.Pareto
