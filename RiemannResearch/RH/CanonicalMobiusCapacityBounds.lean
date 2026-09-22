/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusCovarianceMinimum
import RiemannResearch.RH.CanonicalMobiusCesaro

/-!
# Quantitative bounds for signed Möbius capacity

Source: user-provided Pareto direct-attempt handoff, Sections 4 and 10,
for the residual orthogonality argument and actual covariance optimizer.
All energies are complete infinite Pareto energies. No asymptotic
capacity lower bound is assumed or established in this module.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The finite pairing of the actual residual with the constant head. -/
def residualHeadPairing (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, limitResidual n * hilbertOne n

theorem residualHeadPairing_tendsto :
    Tendsto residualHeadPairing atTop (𝓝 limitEnergy) := by
  have h := (hilbert_coordinate_mul_summable limitResidual hilbertOne).hasSum.tendsto_sum_nat
  have he : (∑' n, limitResidual n * hilbertOne n) = limitEnergy := by
    simpa only [lp.inner_eq_tsum, RCLike.inner_apply, conj_trivial, mul_comm] using
      limitResidual_inner_one
  change Tendsto (fun N => ∑ n ∈ Finset.range N, limitResidual n * hilbertOne n)
    atTop (𝓝 limitEnergy)
  rwa [he] at h

theorem exact_head_coordinate_eq {f : ThresholdHilbert} (N : ℕ)
    (hhead : ∀ j, 0 < j → j ≤ N → hilbertSequence f j = 1)
    (n : ℕ) (hn : n < N) : f n = hilbertOne n := by
  have hs := hhead (n+1) (by omega) (by omega)
  have hone : hilbertSequence hilbertOne (n+1) = 1 := by
    rw [hilbertOne_sequence]
    simp [zeroAnchor]
  have hw : Real.sqrt (paretoWeight n) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    unfold paretoWeight
    positivity
  exact (div_left_inj' hw).mp (hs.trans hone.symm)

/-- Orthogonality determines the full tail pairing, including its sign. -/
theorem residual_tail_pairing_eq_neg_head (N : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ closedSpace)
    (hhead : ∀ j, 0 < j → j ≤ N → hilbertSequence f j = 1) :
    inner ℝ (hilbertTailShift limitResidual N) (hilbertTailShift f N) =
      -residualHeadPairing N := by
  have ho : inner ℝ limitResidual f = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hf
  have ht := (hilbert_coordinate_mul_summable limitResidual f).sum_add_tsum_nat_add N
  have hh : (∑ n ∈ Finset.range N, limitResidual n * f n) =
      residualHeadPairing N := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [exact_head_coordinate_eq N hhead n (Finset.mem_range.mp hn)]
  have hz : (∑' n, limitResidual n * f n) = 0 := by
    simpa only [lp.inner_eq_tsum, RCLike.inner_apply, conj_trivial, mul_comm] using ho
  rw [hh, hz] at ht
  have he : inner ℝ (hilbertTailShift limitResidual N) (hilbertTailShift f N) =
      ∑' n, limitResidual (n+N) * f (n+N) := by
    simp only [lp.inner_eq_tsum, RCLike.inner_apply, conj_trivial,
      hilbertTailShift, mul_comm]
  rw [he]
  linarith

theorem residual_head_sq_le_tail_product (N : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ closedSpace)
    (hhead : ∀ j, 0 < j → j ≤ N → hilbertSequence f j = 1) :
    residualHeadPairing N ^ 2 ≤ residualTailEnergy N * ‖hilbertTailShift f N‖^2 := by
  have h := abs_real_inner_le_norm (hilbertTailShift limitResidual N) (hilbertTailShift f N)
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [sq_abs, mul_pow, residual_tail_pairing_eq_neg_head N hf hhead, neg_sq] at hs
  exact hs

namespace SignedCovariance
open RiemannResearch.Analysis.FiniteHilbertGram
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- One bound simultaneously applies to every finite family at cutoff N. -/
theorem capacity_mul_residual_head_sq_le (N : ℕ) (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (hindex : ∀ i, N ≤ k i) :
    capacity N k hk * residualHeadPairing N ^ 2 ≤ residualTailEnergy N := by
  have h := residual_head_sq_le_tail_product N
    (optimizedAverage_mem_closedSpace N k hk) (optimizedAverage_exact N k hk hindex)
  rw [optimizedAverage_tail_energy] at h
  have hp := capacity_pos N k hk
  have hm := mul_le_mul_of_nonneg_left h hp.le
  have he : capacity N k hk * (residualTailEnergy N * (capacity N k hk)⁻¹) =
      residualTailEnergy N := by field_simp
  rwa [he] at hm

/-- If the residual is nonzero, every finite family obeys the same eventual
quantitative bound. The cutoff threshold is independent of its size or horizon. -/
theorem capacity_uniform_residual_bound (hpos : 0 < limitEnergy) :
    ∀ᶠ N in atTop, ∀ (J : Type) [Fintype J] [Nonempty J]
      (k : J → ℕ) (hk : ∀ i, 0 < k i),
      (∀ i, N ≤ k i) →
      capacity N k hk ≤ (4 / limitEnergy^2) * residualTailEnergy N := by
  have hh : ∀ᶠ N in atTop, limitEnergy / 2 < residualHeadPairing N :=
    residualHeadPairing_tendsto.eventually_const_lt (by linarith)
  filter_upwards [hh] with N hN J _ _ k hk hindex
  have hb := capacity_mul_residual_head_sq_le N k hk hindex
  have hp := capacity_pos N k hk
  have hs : limitEnergy^2 / 4 ≤ residualHeadPairing N ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs hp.le
  have he : capacity N k hk * limitEnergy^2 ≤ 4 * residualTailEnergy N := by nlinarith
  calc
    capacity N k hk ≤ (4 * residualTailEnergy N) / limitEnergy^2 :=
      (le_div_iff₀ (sq_pos_of_pos hpos)).2 he
    _ = (4 / limitEnergy^2) * residualTailEnergy N := by ring

/-- Under failure of RH, decay is uniform even when the number of indices and
their horizon are allowed to vary arbitrarily with the cutoff. -/
theorem capacity_uniform_tendsto_zero_of_not_RH (hRH : ¬ RiemannHypothesis)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (J : Type) [Fintype J] [Nonempty J]
      (k : J → ℕ) (hk : ∀ i, 0 < k i),
      (∀ i, N ≤ k i) → capacity N k hk < ε := by
  have hb := capacity_uniform_residual_bound (not_RH_limitEnergy_pos hRH)
  have ht : Tendsto (fun N => (4 / limitEnergy^2) * residualTailEnergy N)
      atTop (𝓝 0) := by
    simpa using residualTailEnergy_tendsto_zero.const_mul (4 / limitEnergy^2)
  filter_upwards [hb, ht.eventually_lt_const hε] with N hN hsmall J _ _ k hk hindex
  exact lt_of_le_of_lt (hN J k hk hindex) hsmall

omit [Nonempty ι] in
theorem capacity_mul_tail_energy_ge_one (N : ℕ) (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (i : ι) :
    1 ≤ capacity N k hk * ‖tailFamily N k i‖ ^ 2 := by
  have hz := normal_equations N k hk
  have hi := congrFun hz i
  change inner ℝ (tailFamily N k i)
    (Fintype.linearCombination ℝ (tailFamily N k) (normal N k hk)) = 1 at hi
  have he : ‖Fintype.linearCombination ℝ (tailFamily N k) (normal N k hk)‖ ^ 2 =
      capacity N k hk := by
    rw [gram_quadratic, hz]
    simp only [mul_one, capacity]
  have hcs := real_inner_mul_inner_self_le (tailFamily N k i)
    (Fintype.linearCombination ℝ (tailFamily N k) (normal N k hk))
  rw [hi, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, he] at hcs
  nlinarith

theorem capacity_mul_full_energy_ge_one (N : ℕ) (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (i : ι) :
    1 ≤ capacity N k hk * ‖canonicalMobiusHilbert (k i)‖ ^ 2 := by
  have ht : ‖tailFamily N k i‖ ^ 2 ≤ ‖canonicalMobiusHilbert (k i)‖ ^ 2 := by
    rw [tailFamily, hilbertTailShift_norm_sq]
    exact sub_le_self _ (Finset.sum_nonneg (fun j hj => sq_nonneg _))
  exact (capacity_mul_tail_energy_ge_one N k hk i).trans
    (mul_le_mul_of_nonneg_left ht (le_of_lt (capacity_pos N k hk)))

/-- Every family member supplies an unconditional quantitative capacity lower bound. -/
theorem reciprocal_four_mul_lt_capacity (N : ℕ) (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (i : ι) :
    1 / (4 * (k i : ℝ)) < capacity N k hk := by
  have hki : (0 : ℝ) < (k i : ℝ) := by exact_mod_cast hk i
  have hp : 1 < capacity N k hk * (4 * (k i : ℝ)) :=
    lt_of_le_of_lt (capacity_mul_full_energy_ge_one N k hk i)
      (mul_lt_mul_of_pos_left
        (canonicalMobiusHilbert_norm_sq_lt_four_mul (k i) (hk i))
        (capacity_pos N k hk))
  exact (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * (k i : ℝ))).2 hp

/-- Conditional arithmetic result: inclusion of the cutoff candidate transfers
its sublinear full energy to divergence of normalized capacity. This does not
give a fixed positive lower bound for unnormalized capacity. -/
theorem normalized_capacity_tendsto_atTop_of_reciprocal_cancellation
    {I : ℕ → Type*} [∀ N, Fintype (I N)] [∀ N, Nonempty (I N)]
    (k : ∀ N, I N → ℕ) (hk : ∀ N i, 0 < k N i)
    (hcontains : ∀ᶠ N in atTop, ∃ i, k N i = N)
    (hm : Tendsto mobiusReciprocalSum atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℝ) * capacity N (k N) (hk N)) atTop atTop := by
  apply RiemannResearch.Analysis.tendsto_atTop_of_pos_le_mul_tendsto_zero
    (c := (1 : ℝ))
    (b := fun N => ‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ))
    (by norm_num)
    (Eventually.of_forall (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg N)))
    (canonicalMobiusHilbert_sublinear_of_reciprocal_cancellation hm)
  filter_upwards [hcontains, eventually_gt_atTop (0 : ℕ)] with N hN hpos
  obtain ⟨i, hi⟩ := hN
  have hp := capacity_mul_full_energy_ge_one N (k N) (hk N) i
  rw [hi] at hp
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hpos
  have he : (N : ℝ) * capacity N (k N) (hk N) *
      (‖canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ)) =
      capacity N (k N) (hk N) * ‖canonicalMobiusHilbert N‖ ^ 2 := by
    field_simp [hN0]
  rwa [he]


end SignedCovariance
end RiemannResearch.RH.Pareto.CoefficientStabilization
