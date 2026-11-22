import RiemannResearch.Analysis.WeightedTailSqueeze
import RiemannResearch.RH.CanonicalMobiusPNT
import RiemannResearch.RH.ThresholdHilbertAdjoint
import RiemannResearch.RH.ThresholdHilbertL1
import RiemannResearch.RH.MixedConductorRankOne

/-!
# One-sided bounds for Pareto annihilators

Dyadic dilations of the parity packet bound the absolute mass of each dyadic
shell for a legal annihilator bounded on one side. A complete absolute tail of
order 1/N forces zero mean by the prime number theorem applied to the canonical
Möbius approximants on fixed-ratio windows.

Source: the screened parity approximation question and the repository's
unconditional Möbius cancellation and exact-head results.
-/

open Filter
open scoped Topology BigOperators InnerProductSpace

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

private noncomputable def physicalError (N : ℕ) : ℕ → ℝ :=
  hilbertSequence (hilbertOne - canonicalMobiusHilbert N)

private lemma physicalError_pos {j : ℕ} (hj : 0 < j) (N : ℕ) :
    physicalError N j = 1 - canonicalMobiusHead N j := by
  have hs : hilbertSequence (hilbertOne - canonicalMobiusHilbert N) =
      hilbertSequence hilbertOne - hilbertSequence (canonicalMobiusHilbert N) :=
    hilbertSequenceLinear.map_sub _ _
  simp [physicalError, hs, hilbertOne_sequence, canonicalMobiusHilbert_sequence,
    zeroAnchor, Nat.ne_of_gt hj]

private theorem physicalError_cutoff_facts {N K : ℕ} (hN : 0 < N) {b : ℝ}
    (hmid : ∀ j, N < j → j ≤ K * N → |canonicalMobiusHead N j| ≤ b * (N : ℝ)) :
    (∀ j, j ≤ N → physicalError N j = 0) ∧
    (∀ j, N < j → j ≤ K * N → |physicalError N j| ≤ 1 + b * (N : ℝ)) ∧
    (∀ j, |physicalError N j| ≤ 1 + 2 * (N : ℝ)) := by
  have herr {j : ℕ} (hj : 0 < j) : |physicalError N j| ≤ 1 + |canonicalMobiusHead N j| := by
    rw [physicalError_pos hj]
    simpa [Real.norm_eq_abs] using norm_sub_le (1 : ℝ) (canonicalMobiusHead N j)
  refine ⟨?_,?_,?_⟩
  · intro j hj
    by_cases h : j=0
    · subst j; exact hilbertSequence_zero _
    · rw [physicalError_pos (Nat.pos_of_ne_zero h),
          canonicalMobiusHead_exact N j (Nat.pos_of_ne_zero h) hj, sub_self]
  · intro j hj hj'
    exact (herr (hN.trans hj)).trans (add_le_add le_rfl (hmid _ hj hj'))
  · intro j
    by_cases h : j=0
    · subst j
      have he : physicalError N 0 = 0 := hilbertSequence_zero _
      rw [he, abs_zero]
      positivity
    · exact (herr (Nat.pos_of_ne_zero h)).trans
        (add_le_add le_rfl (canonicalMobiusHead_abs_le_two_mul N hN j))

private lemma annihilator_mean_eq_mobius_error (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ)
    (N : ℕ) :
    inner ℝ z hilbertOne =
      ∑' j : ℕ, positiveWeight j * (hilbertSequence z j * physicalError N j) := by
  have ho : inner ℝ z (canonicalMobiusHilbert N) = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal (canonicalMobiusHilbert_mem_closedSpace N) hz
  calc
    inner ℝ z hilbertOne = inner ℝ z (hilbertOne - canonicalMobiusHilbert N) := by
      rw [inner_sub_right, ho, sub_zero]
    _ = _ := hilbert_inner_weighted _ _


/-- Finite two-window estimate with the actual absolute masses. Both cutoffs
and the canonical head bound may vary together. -/
theorem annihilator_mean_abs_le_window_tails (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ)
    (N K : ℕ) (hN : 0 < N) (b : ℝ) (hb : 0 ≤ b)
    (hmid : ∀ j, N < j → j ≤ K * N → |canonicalMobiusHead N j| ≤ b * (N : ℝ)) :
    |inner ℝ z hilbertOne| ≤
      (1 + b * (N : ℝ)) * (∑' k : ℕ, positiveWeight (k+N) * |hilbertSequence z (k+N)|) +
      (1 + 2 * (N : ℝ)) * (∑' k : ℕ, positiveWeight (k+K*N) * |hilbertSequence z (k+K*N)|) := by
  let a : ℕ → ℝ := fun j => positiveWeight j * |hilbertSequence z j|
  have ha : Summable a := hilbertL1Norm_summable z
  have hapos (j : ℕ) : 0 ≤ a j := mul_nonneg (positiveWeight_nonneg j) (abs_nonneg _)
  let f : ℕ → ℝ := fun j => positiveWeight j * (hilbertSequence z j * physicalError N j)
  obtain ⟨hhead, hsmall, hglobal⟩ := physicalError_cutoff_facts hN hmid
  have hpoint (j : ℕ) : |f j| ≤ a j * |physicalError N j| := by
    simp [f, a, abs_mul, abs_of_nonneg (positiveWeight_nonneg j), mul_assoc]
  have hnB : 0 ≤ 1 + b * (N : ℝ) := by positivity
  rw [annihilator_mean_eq_mobius_error z hz N]
  calc
    |∑' j, f j| ≤ (1 + b * (N : ℝ)) * (∑' k, a (k + N)) +
        (1 + 2 * (N : ℝ)) * (∑' k, a (k + (K * N))) :=
      RiemannResearch.Analysis.WeightedTail.abs_tsum_le_two_tails a (physicalError N) f N
        (K * N) _ _ ha hapos hnB hhead hsmall hglobal hpoint

/-- A Pareto annihilator with a complete absolute first-moment tail of order 1/N
has zero mean. The Möbius cancellation used here is unconditional. -/
theorem annihilator_mean_zero_of_absolute_tail (z : ThresholdHilbert)
    (hz : z ∈ closedSpaceᗮ) (A : ℝ) (hA : 0 ≤ A)
    (htail : ∀ N : ℕ, 0 < N →
      (∑' k : ℕ, positiveWeight (k + N) * |hilbertSequence z (k + N)|) ≤ A / (N : ℝ)) :
    inner ℝ z hilbertOne = 0 := by
  have hw := canonicalMobiusHead_windows_of_mobius_cancellation
    (mobius_sum_div_tendsto_zero_of_reciprocal_tendsto mobiusReciprocalSum_tendsto_zero)
    mobiusReciprocalSum_tendsto_zero
  apply abs_eq_zero.mp
  apply RiemannResearch.Analysis.weighted_tail_squeeze _ A hA (abs_nonneg _)
  intro K hK b hb
  filter_upwards [hw K hK b hb, eventually_gt_atTop 0] with N hmid hN
  have hnB : 0 ≤ 1 + b * (N : ℝ) := by positivity
  have hnC : 0 ≤ 1 + 2 * (N : ℝ) := by positivity
  calc
    |inner ℝ z hilbertOne| ≤
        (1+b*(N : ℝ)) * (∑' k : ℕ, positiveWeight (k+N) * |hilbertSequence z (k+N)|) +
        (1+2*(N : ℝ)) * (∑' k : ℕ, positiveWeight (k+K*N) * |hilbertSequence z (k+K*N)|) :=
      annihilator_mean_abs_le_window_tails z hz N K hN b hb.le hmid
    _ ≤ (1 + b * (N : ℝ)) * (A / (N : ℝ)) + (1 + 2 * (N : ℝ)) * (A / ((K : ℝ) * (N : ℝ))) := by
      have hfar := htail (K * N) (Nat.mul_pos (by omega) hN)
      rw [Nat.cast_mul] at hfar
      exact add_le_add (mul_le_mul_of_nonneg_left (htail N hN) hnB)
        (mul_le_mul_of_nonneg_left hfar hnC)

end RiemannResearch.RH.Pareto.CoefficientStabilization

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open PrimePowerSchur

private theorem absolute_dyadic_shell_of_upper (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ)
    {C : ℝ} (hC : 0 ≤ C) (hu : ∀ n : ℕ, 0 < n → hilbertSequence z n ≤ C)
    (N : ℕ) (hN : 0 < N) :
    (∑ k ∈ Finset.range N, positiveWeight (k+N) * |hilbertSequence z (k+N)|) ≤
      2 * C * Real.log 2 / (N : ℝ) := by
  let d := hilbertDilation N hN (ramanujanPacketHilbert 2)
  let f := (2*C) • hilbertOne - z
  have hd (j : ℕ) : hilbertSequence d j = (N : ℝ) * ((j/N % 2 : ℕ) : ℝ) := by
    dsimp only [d]
    rw [hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert]
    change (N : ℝ) * ramanujanPacket 2 (j/N) = _
    rw [ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
    rfl
  have hf (j : ℕ) : |hilbertSequence z j| ≤ hilbertSequence f j := by
    by_cases hj : j = 0
    · subst j
      simp only [hilbertSequence_zero, abs_zero, le_refl]
    · have hfj : hilbertSequence f j = 2*C - hilbertSequence z j := by
        simp only [f, hilbertSequence_sub, hilbertSequence_smul, Pi.sub_apply,
          Pi.smul_apply, smul_eq_mul, hilbertOne_sequence, zeroAnchor, if_neg hj, mul_one]
      rw [hfj, abs_le]
      constructor <;> linarith [hu j (Nat.pos_of_ne_zero hj)]
  have hdin : d ∈ closedSpace :=
    closedSpace_dilation (packet_mem_closedSpace 2 (by norm_num)) N hN
  have hdmean : inner ℝ d hilbertOne = Real.log 2 := by
    rw [hilbert_inner_one, hilbertDilation_mean, hilbertSequence_ramanujanPacketHilbert,
      paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  let v := fun j : ℕ => positiveWeight j * (hilbertSequence d j * hilbertSequence f j)
  have hv : Summable v := weighted_product_summable_of_square
    (hilbertSequence_square_summable d) (hilbertSequence_square_summable f)
  have hv0 (j : ℕ) : 0 ≤ v j := by
    have hj := (abs_nonneg (hilbertSequence z j)).trans (hf j)
    dsimp only [v]
    rw [hd]
    exact mul_nonneg (positiveWeight_nonneg _) (mul_nonneg (by positivity) hj)
  have hval : ∑' j, v j = 2*C*Real.log 2 := by
    change paretoInner (hilbertSequence d) (hilbertSequence f) = _
    rw [← hilbert_inner_weighted]
    change inner ℝ d ((2*C) • hilbertOne-z) = _
    rw [inner_sub_right, real_inner_smul_right, hdmean, hz d hdin, sub_zero]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ hNR).mpr
  calc
    _ = ∑ k ∈ Finset.range N,
        positiveWeight (k+N) * ((N : ℝ) * |hilbertSequence z (k+N)|) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ∑ k ∈ Finset.range N, v (k+N) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN := Finset.mem_range.mp hk
      have hdiv : (k + N)/N = 1 := by
        rw [Nat.add_div_right _ hN, Nat.div_eq_of_lt hkN, zero_add]
      dsimp only [v]
      rw [hd, hdiv]
      norm_num only [Nat.one_mod, Nat.cast_one, mul_one]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hf (k+N)) hNR.le) (positiveWeight_nonneg _)
    _ ≤ ∑' k, v (k+N) := Summable.sum_le_tsum _ (fun _ _ => hv0 _) ((summable_nat_add_iff N).mpr hv)
    _ ≤ ∑' j, v j := by
      have he := hv.sum_add_tsum_nat_add N
      have hh : 0 ≤ ∑ k ∈ Finset.range N, v k := Finset.sum_nonneg (fun k _ => hv0 k)
      linarith
    _ = _ := hval

private theorem abs_tail_bound_of_shell {F : ℕ → ℝ} (hs : Summable F) {B : ℝ}
    (hb : ∀ N : ℕ, 0 < N → (∑ k ∈ Finset.range N, F (k+N)) ≤ B / (N : ℝ)) :
    ∀ N : ℕ, 0 < N → (∑' k, F (k+N)) ≤ 2 * B / (N : ℝ) := by
  let T := fun N : ℕ => ∑' k, F (k+N)
  let g := fun N : ℕ => T N - 2 * B / (N : ℝ)
  have hstep (N : ℕ) (hN : 0 < N) : g N ≤ g (2*N) := by
    have he := ((summable_nat_add_iff N).mpr hs).sum_add_tsum_nat_add N
    have hidx (k : ℕ) : k+N+N=k+2*N := by omega
    simp only [hidx] at he
    change T N - 2*B/(N : ℝ) ≤ T (2*N) - 2*B/((2*N : ℕ) : ℝ)
    have he' : (∑ k ∈ Finset.range N, F (k+N)) + T (2*N) = T N := he
    have h2 : 2*B/((2*N : ℕ) : ℝ) = B/(N : ℝ) := by
      push_cast
      ring
    rw [h2]
    have hmain := hb N hN
    linarith [show 2*B/(N:ℝ)=2*(B/(N:ℝ)) by ring]
  have hT : Tendsto T atTop (𝓝 0) := by
    have he : T = fun n => (∑' k, F k) - ∑ k ∈ Finset.range n, F k := by
      funext n
      change (∑' k, F (k+n)) = _
      linarith [hs.sum_add_tsum_nat_add n]
    rw [he]
    have hc : Tendsto (fun _ : ℕ => ∑' k, F k) atTop (𝓝 (∑' k, F k)) := tendsto_const_nhds
    simpa only [sub_self] using hc.sub hs.hasSum.tendsto_sum_nat
  have hg : Tendsto g atTop (𝓝 0) := by
    have hr := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*B)
    simpa only [g, mul_zero, sub_zero, div_eq_mul_inv, one_mul] using hT.sub hr
  intro N hN
  have hiter (k : ℕ) : g N ≤ g (2^k*N) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hp : 0 < 2^k*N := Nat.mul_pos (pow_pos (by decide) _) hN
      rw [show 2^(k+1)*N = 2*(2^k*N) by rw [pow_succ]; ring]
      exact ih.trans (hstep _ hp)
  have hpow (k : ℕ) : k+1 ≤ 2^k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; omega
  have hlim : Tendsto (fun k : ℕ => 2^k*N) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_succ k).trans ((hpow k).trans
      (Nat.le_mul_of_pos_right _ hN))) tendsto_id
  have hle : g N ≤ 0 := ge_of_tendsto (hg.comp hlim) (Eventually.of_forall hiter)
  exact sub_nonpos.mp hle

theorem annihilator_absolute_tail_le_of_upper (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ)
    {C : ℝ} (hC : 0 ≤ C) (hu : ∀ n : ℕ, 0 < n → hilbertSequence z n ≤ C)
    (N : ℕ) (hN : 0 < N) :
    (∑' k : ℕ, positiveWeight (k+N) * |hilbertSequence z (k+N)|) ≤
      2 * (2*C*Real.log 2) / (N : ℝ) :=
  abs_tail_bound_of_shell (hilbertL1Norm_summable z)
    (absolute_dyadic_shell_of_upper z hz hC hu) N hN

/-- A one-sided tail estimate at a single scale controls the absolute mass
on that scale's first dyadic shell. -/
private theorem annihilator_shell_le_of_positive_tail_at (z : ThresholdHilbert)
    (hz : z ∈ closedSpaceᗮ) (C : ℝ) (n : ℕ) (hn : 0 < n)
    (hp : (∑' k : ℕ, positiveWeight (k+n) * max (hilbertSequence z (k+n)) 0) ≤ C / (n : ℝ)) :
    (∑ k ∈ Finset.range n, positiveWeight (k+n) * |hilbertSequence z (k+n)|) ≤ 2*C/(n : ℝ) := by
  let d := hilbertDilation n hn (ramanujanPacketHilbert 2)
  let f := hilbertAbs z + z
  have hd (j : ℕ) : hilbertSequence d j = (n : ℝ) * ((j/n % 2 : ℕ) : ℝ) := by
    dsimp only [d]
    rw [hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert]
    change (n : ℝ) * ramanujanPacket 2 (j/n) = _
    rw [ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
    rfl
  have hf (j : ℕ) : hilbertSequence f j = 2*max (hilbertSequence z j) 0 := by
    simp only [f, hilbertSequence_add, Pi.add_apply, hilbertAbs_sequence]
    by_cases h : 0 ≤ hilbertSequence z j
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_neg (lt_of_not_ge h), max_eq_right (le_of_not_ge h)]; ring
  let v (a : ThresholdHilbert) (j : ℕ) :=
    positiveWeight j * (hilbertSequence d j * hilbertSequence a j)
  have hs (a : ThresholdHilbert) : Summable (v a) :=
    weighted_product_summable_of_square (hilbertSequence_square_summable d)
      (hilbertSequence_square_summable a)
  have he (a : ThresholdHilbert) : (∑' j, v a j) = inner ℝ d a :=
    (hilbert_inner_weighted d a).symm
  have hbefore (a : ThresholdHilbert) : (∑' j, v a j) = ∑' k, v a (k+n) := by
    rw [← (hs a).sum_add_tsum_nat_add n]
    have hz0 : ∑ k ∈ Finset.range n, v a k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [v, hd, Nat.div_eq_of_lt (Finset.mem_range.mp hk), Nat.zero_mod,
        Nat.cast_zero, mul_zero, zero_mul]
    rw [hz0, zero_add]
  have hz' : inner ℝ d z = 0 :=
    hz d (closedSpace_dilation (packet_mem_closedSpace 2 (by norm_num)) n hn)
  have hspos : Summable (fun j => positiveWeight j * max (hilbertSequence z j) 0) := by
    have heq : (fun j => positiveWeight j * max (hilbertSequence z j) 0) =
        (fun j => (positiveWeight j * hilbertSequence f j) * (1 / 2 : ℝ)) := by
      funext j
      rw [hf]
      ring
    rw [heq]
    exact (weighted_summable_of_square (hilbertSequence_square_summable f)).mul_right _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ hnR).mpr
  calc
    _ = ∑ k ∈ Finset.range n, v (hilbertAbs z) (k+n) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hdiv : (k+n)/n = 1 := by
        rw [Nat.add_div_right _ hn, Nat.div_eq_of_lt (Finset.mem_range.mp hk), zero_add]
      dsimp only [v]
      rw [hd, hdiv, hilbertAbs_sequence]
      norm_num only [Nat.one_mod, Nat.cast_one, mul_one]
      ring
    _ ≤ ∑' k, v (hilbertAbs z) (k+n) := by
      apply Summable.sum_le_tsum _ _ ((summable_nat_add_iff n).mpr (hs _))
      intro k hk
      dsimp only [v]
      rw [hd, hilbertAbs_sequence]
      exact mul_nonneg (positiveWeight_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))
    _ = ∑' k, v f (k+n) := by
      rw [← hbefore, ← hbefore, he, he, show f = hilbertAbs z + z from rfl, inner_add_right,
        hz', add_zero]
    _ ≤ ∑' k, (positiveWeight (k+n) * max (hilbertSequence z (k+n)) 0) * (2*(n:ℝ)) := by
      apply Summable.tsum_le_tsum _ ((summable_nat_add_iff n).mpr (hs _))
        (((summable_nat_add_iff n).mpr hspos).mul_right _)
      intro k
      have hmod : (((k+n)/n % 2 : ℕ) : ℝ) ≤ 1 := by
        exact_mod_cast Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 2))
      have hmax := le_max_right (hilbertSequence z (k+n)) 0
      dsimp only [v]
      rw [hd, hf]
      calc
        _ ≤ positiveWeight (k+n) * ((n:ℝ) * (2*max (hilbertSequence z (k+n)) 0)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            ((mul_le_mul_of_nonneg_left hmod hnR.le).trans_eq (mul_one _))
            (mul_nonneg (by norm_num) hmax)) (positiveWeight_nonneg _)
        _ = _ := by ring
    _ ≤ 2*C := by
      rw [tsum_mul_right]
      calc
        _ ≤ C/(n:ℝ)*(2*n) := mul_le_mul_of_nonneg_right hp (by positivity)
        _ = _ := by field_simp

/-- At each cutoff the controlled sign may be selected anew. Parity
orthogonality converts either estimate into the same dyadic-shell bound. -/
theorem annihilator_absolute_tail_le_of_oneSided_tails
    (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ) (C : ℝ)
    (h : ∀ n : ℕ, 0 < n →
      (∑' k : ℕ, positiveWeight (k+n) * max (hilbertSequence z (k+n)) 0) ≤ C/(n : ℝ) ∨
      (∑' k : ℕ, positiveWeight (k+n) * max (-hilbertSequence z (k+n)) 0) ≤ C/(n : ℝ))
    (N : ℕ) (hN : 0 < N) :
    (∑' k : ℕ, positiveWeight (k+N) * |hilbertSequence z (k+N)|) ≤ 2*(2*C)/(N : ℝ) := by
  apply abs_tail_bound_of_shell (hilbertL1Norm_summable z) _ N hN
  intro n hn
  rcases h n hn with hp | hm
  · exact annihilator_shell_le_of_positive_tail_at z hz C n hn hp
  · have hneg (k : ℕ) : hilbertSequence (-z) k = -hilbertSequence z k := by
      rw [← anchoredEvaluationCLM_apply, map_neg, anchoredEvaluationCLM_apply]
    simpa only [hneg, abs_neg] using
      annihilator_shell_le_of_positive_tail_at (-z) (closedSpace.orthogonal.neg_mem hz) C n hn
        (by simpa only [hneg] using hm)

/-- A bound on just the positive part controls the complete absolute first-moment tail. -/
theorem annihilator_absolute_tail_le_of_positive_tail
    (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ) (C : ℝ)
    (hp : ∀ n : ℕ, 0 < n →
      (∑' k : ℕ, positiveWeight (k+n) * max (hilbertSequence z (k+n)) 0) ≤ C/(n : ℝ))
    (N : ℕ) (hN : 0 < N) :
    (∑' k : ℕ, positiveWeight (k+N) * |hilbertSequence z (k+N)|) ≤ 2*(2*C)/(N : ℝ) :=
  annihilator_absolute_tail_le_of_oneSided_tails z hz C (fun n hn => Or.inl (hp n hn)) N hN

/-- One-sided boundedness forces the constant pairing of a legal annihilator to vanish. -/
theorem annihilator_mean_zero_of_upper_bound (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ)
    (hbound : ∃ C : ℝ, ∀ n : ℕ, 0 < n → hilbertSequence z n ≤ C) :
    inner ℝ z hilbertOne = 0 := by
  obtain ⟨C, hC⟩ := hbound
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hu (n : ℕ) (hn : 0 < n) : hilbertSequence z n ≤ D :=
    (hC n hn).trans (le_max_left _ _)
  have ha : 0 ≤ 2 * (2 * D * Real.log 2) := by positivity
  exact annihilator_mean_zero_of_absolute_tail z hz _ ha
    (annihilator_absolute_tail_le_of_upper z hz hD hu)

/-- An upper bound on a legal annihilator persists under every dilation adjoint.
Their means recover each coordinate, hence the annihilator vanishes. -/
theorem annihilator_eq_zero_of_upper_bound (z : ThresholdHilbert) (hz : z ∈ closedSpaceᗮ)
    (hbound : ∃ C : ℝ, ∀ k : ℕ, 0 < k → hilbertSequence z k ≤ C) : z = 0 := by
  obtain ⟨C, hC⟩ := hbound
  have hmean (m : ℕ) (hm : 0 < m) :
      inner ℝ hilbertOne (hilbertDilationAdjoint m hm z) = 0 := by
    rw [real_inner_comm]
    apply annihilator_mean_zero_of_upper_bound _ ?_ ⟨C, ?_⟩
    · intro v hv
      change inner ℝ v ((hilbertDilationContinuous m hm).adjoint z) = 0
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact hz _ (closedSpace_dilation hv m hm)
    · intro k hk
      calc
        hilbertSequence (hilbertDilationAdjoint m hm z) k ≤
            hilbertSequence (hilbertDilationAdjoint m hm (C • hilbertOne)) k := by
          rw [hilbertDilationAdjoint_coordinate m k hm hk z,
            hilbertDilationAdjoint_coordinate m k hm hk (C • hilbertOne)]
          apply mul_le_mul_of_nonneg_left _
            (div_nonneg (Nat.cast_nonneg _) (positiveWeight_nonneg _))
          apply Finset.sum_le_sum
          intro n hn
          have hn' := (Nat.mul_pos hm hk).trans_le (Finset.mem_Ico.mp hn).1
          apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
          simpa [hilbertSequence_smul, hilbertOne_sequence, zeroAnchor, hn'.ne'] using hC n hn'
        _ = C := by simp [hilbertDilationAdjoint_one, zeroAnchor, hk.ne']
  apply hilbertSequence_injective
  funext k
  change hilbertSequence z k = hilbertSequenceLinear (0 : ThresholdHilbert) k
  rw [map_zero]
  cases k with
  | zero => exact hilbertSequence_zero z
  | succ k =>
    rw [hilbert_coordinate_recovery z _ (Nat.succ_pos k), hmean _ _, hmean _ _]
    simp

end RiemannResearch.RH.Pareto.CoefficientStabilization
