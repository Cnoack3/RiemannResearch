import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.NearbyDilationGram
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega


/-!
# Exact-head repairs and the canonical residual-tail obstruction

Source: user-provided
RH_Weighted_Telescoping_Construction_and_Tail_Repair_2026-09-19.md, Sections 5-6,
and RH_Equivalent_Formulations_Lean_Audit_2026-09-19(1)(1).md.
These support the statements and the projection/Cauchy-Schwarz proof strategy.
No claim of mathematical novelty is made.

The actual closed residue span, actual canonical residual, and complete weighted
Hilbert norm are retained. The shifted l2 realization is exactly the physical
tail beyond N, not a truncated replacement for the full error energy.

Established: tail energy tends to zero; its product with any exact-head legal
error is at least the square of the canonical residual energy. Under not RH,
every such error family diverges. Orthogonal repair preserves the head and gives
an exact energy split and a compatible lower bound on the remaining Schur error.

CONDITIONAL RESEARCH REDUCTIONS: product decay, arbitrarily small products, or
bounded exact-head errors imply Mathlib RH. Their arithmetic upper bounds remain
OPEN. The existence of finite optimum corrections does not supply these bounds.
Neither a density-from-RH provider nor an assumed RH equivalence is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto

def hilbertTailShift (f : ThresholdHilbert) (N : ℕ) : ThresholdHilbert :=
  ⟨fun n => f (n + N), by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, Function.comp_def] using
      (hilbert_coordinate_square_summable f).comp_injective
        (fun _ _ h => Nat.add_right_cancel h)⟩

theorem hilbert_coordinate_mul_summable (f g : ThresholdHilbert) :
    Summable (fun n => f n * g n) := by
  have h := (((hilbert_coordinate_square_summable (f + g)).sub
    (hilbert_coordinate_square_summable f)).sub
    (hilbert_coordinate_square_summable g)).div_const 2
  apply h.congr
  intro n
  change ((f n + g n)^2 - (f n)^2 - (g n)^2) / 2 = f n * g n
  ring

theorem hilbertTailShift_inner (f g : ThresholdHilbert) (N : ℕ)
    (hg : ∀ n < N, g n = 0) :
    inner ℝ (hilbertTailShift f N) (hilbertTailShift g N) = inner ℝ f g := by
  have h := (hilbert_coordinate_mul_summable f g).sum_add_tsum_nat_add N
  have hp : (∑ n ∈ Finset.range N, f n * g n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [hg n (Finset.mem_range.mp hn), mul_zero]
  rw [hp, zero_add] at h
  simpa only [lp.inner_eq_tsum, RCLike.inner_apply, conj_trivial, mul_comm, hilbertTailShift] using h

theorem hilbertTailShift_norm_sq (f : ThresholdHilbert) (N : ℕ) :
    ‖hilbertTailShift f N‖^2 = ‖f‖^2 - ∑ n ∈ Finset.range N, (f n)^2 := by
  have h := (hilbert_coordinate_square_summable f).sum_add_tsum_nat_add N
  rw [hilbert_norm_sq, hilbert_norm_sq]
  change (∑' n, (f (n+N))^2) = (∑' n, (f n)^2) -
    ∑ n ∈ Finset.range N, (f n)^2
  linarith

theorem hilbertTailShift_energy_tendsto_zero (f : ThresholdHilbert) :
    Tendsto (fun N => ‖hilbertTailShift f N‖^2) atTop (𝓝 0) := by
  have h := (hilbert_coordinate_square_summable f).hasSum.tendsto_sum_nat
  have ht := (tendsto_const_nhds (x := ‖f‖^2)).sub h
  simpa only [hilbertTailShift_norm_sq, ← hilbert_norm_sq, sub_self] using ht

theorem hilbertTailShift_inner_sq_le (r e : ThresholdHilbert) (N : ℕ)
    (he : ∀ n < N, e n = 0) :
    (inner ℝ r e)^2 ≤ ‖hilbertTailShift r N‖^2 * ‖e‖^2 := by
  have h := abs_real_inner_le_norm (hilbertTailShift r N) (hilbertTailShift e N)
  have hn : ‖hilbertTailShift e N‖^2 = ‖e‖^2 := by
    simpa only [real_inner_self_eq_norm_sq] using hilbertTailShift_inner e e N he
  rw [hilbertTailShift_inner r e N he] at h
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  rw [sq_abs, mul_pow, hn] at hs
  exact hs

/-- A bounded physical sequence has a complete Pareto tail of energy at most
`A² / (N+1)`. The proof starts from the exact weighted tail and telescoping mass. -/
theorem hilbertTailShift_norm_sq_le_of_bounded (f : ThresholdHilbert) (N : ℕ)
    (A : ℝ) (hA : 0 ≤ A)
    (hf : ∀ n, 0 < n → |hilbertSequence f n| ≤ A) :
    ‖hilbertTailShift f N‖ ^ 2 ≤ A ^ 2 / ((N : ℝ) + 1) := by
  have hs : Summable (fun k : ℕ => positiveWeight (k + N + 1) *
      hilbertSequence f (k + N + 1) ^ 2) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (N + 1)).mpr (hilbertSequence_square_summable f)
  have hw : Summable (fun k : ℕ => positiveWeight (k + N + 1)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (N + 1)).mpr positiveWeight_summable
  calc
    ‖hilbertTailShift f N‖ ^ 2 =
        ∑' k : ℕ, positiveWeight (k + N + 1) *
          hilbertSequence f (k + N + 1) ^ 2 := by
      rw [hilbert_norm_sq]
      apply tsum_congr
      intro k
      exact (hilbertSequence_weighted_square f (k + N)).symm
    _ ≤ ∑' k : ℕ, positiveWeight (k + N + 1) * A ^ 2 := by
      apply Summable.tsum_le_tsum _ hs (hw.mul_right _)
      intro k
      apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (hilbertSequence f (k + N + 1))) hA).mpr
          (hf (k + N + 1) (by omega))
    _ = A ^ 2 / ((N : ℝ) + 1) := by
      rw [tsum_mul_right]
      have ht : (∑' k : ℕ, positiveWeight (k + N + 1)) =
          1 / ((N + 1 : ℕ) : ℝ) := by
        simpa only [Nat.add_assoc] using
          positiveWeight_tail_tsum (N + 1) (Nat.succ_pos _)
      rw [ht]
      push_cast
      ring

namespace CoefficientStabilization

def residualTailEnergy (N : ℕ) : ℝ := ‖hilbertTailShift limitResidual N‖^2

theorem residualTailEnergy_nonneg (N : ℕ) : 0 ≤ residualTailEnergy N := sq_nonneg _

theorem residualTailEnergy_tendsto_zero :
    Tendsto residualTailEnergy atTop (𝓝 0) :=
  hilbertTailShift_energy_tendsto_zero limitResidual

theorem residual_error_pairing {f : ThresholdHilbert} (hf : f ∈ closedSpace) :
    inner ℝ limitResidual (hilbertOne - f) = limitEnergy := by
  have ho : inner ℝ limitResidual f = 0 := by
    rw [real_inner_comm]
    exact (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hf
  rw [inner_sub_right, limitResidual_inner_one, ho, sub_zero]

theorem residual_tail_product_lower (N : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ closedSpace)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    limitEnergy^2 ≤ residualTailEnergy N * ‖hilbertOne - f‖^2 := by
  have he : ∀ n < N, (hilbertOne - f) n = 0 := by
    intro n hn
    have hs := hhead (n+1) (by omega) (by omega)
    have hone : hilbertSequence hilbertOne (n+1) = 1 := by
      rw [hilbertOne_sequence]
      simp [zeroAnchor]
    have hsame : hilbertSequence hilbertOne (n+1) = hilbertSequence f (n+1) :=
      hone.trans hs.symm
    have hw : Real.sqrt (paretoWeight n) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      unfold paretoWeight
      positivity
    have hc : hilbertOne n = f n := (div_left_inj' hw).mp hsame
    change hilbertOne n - f n = 0
    exact sub_eq_zero.mpr hc
  simpa only [residual_error_pairing hf, residualTailEnergy] using
    hilbertTailShift_inner_sq_le limitResidual (hilbertOne - f) N he

theorem riemannHypothesis_of_residual_tail_product
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (hprod : Tendsto (fun N => residualTailEnergy N * ‖hilbertOne - F N‖^2)
      atTop (𝓝 0)) : RiemannHypothesis := by
  have hle : limitEnergy^2 ≤ 0 := ge_of_tendsto' hprod
    (fun N => residual_tail_product_lower N (hlegal N) (hhead N))
  have hz : limitEnergy = 0 := by nlinarith [sq_nonneg limitEnergy]
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (limitEnergy_zero_iff_mem.mp hz))



/-- The shifted l2 norm is exactly the physical infinite weighted tail. -/
theorem residualTailEnergy_eq_weighted (N : ℕ) :
    residualTailEnergy N = ∑' n : ℕ, positiveWeight (n+N+1) *
      hilbertSequence limitResidual (n+N+1)^2 := by
  unfold residualTailEnergy
  rw [hilbert_norm_sq]
  change (∑' n : ℕ, (limitResidual (n+N))^2) = _
  apply tsum_congr
  intro n
  exact (hilbertSequence_weighted_square limitResidual (n+N)).symm

theorem not_RH_limitEnergy_pos (hRH : ¬ RiemannHypothesis) : 0 < limitEnergy := by
  have hn : limitEnergy ≠ 0 := by
    intro hz
    apply hRH
    exact riemannHypothesis_of_limitCoefficients
      (limitCoefficients_eq_mobius_iff_mem.mpr (limitEnergy_zero_iff_mem.mp hz))
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)

/-- Only arbitrarily small products are required; a prescribed decay rate is not. -/
theorem riemannHypothesis_of_small_residual_tail_product
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ f : ThresholdHilbert,
      f ∈ closedSpace ∧
      (∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) ∧
      residualTailEnergy N * ‖hilbertOne - f‖^2 < ε) : RiemannHypothesis := by
  by_contra hRH
  have hp := sq_pos_of_pos (not_RH_limitEnergy_pos hRH)
  obtain ⟨N, f, hf, hh, hlt⟩ := hsmall (limitEnergy^2) hp
  exact (not_lt_of_ge (residual_tail_product_lower N hf hh)) hlt

theorem riemannHypothesis_of_bounded_exact_head_errors
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (C : ℝ) (hbound : ∀ N, ‖hilbertOne - F N‖^2 ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_residual_tail_product F hlegal hhead
  have hupper : Tendsto (fun N => residualTailEnergy N * C) atTop (𝓝 0) := by
    simpa using residualTailEnergy_tendsto_zero.mul_const C
  exact squeeze_zero
    (fun N => mul_nonneg (residualTailEnergy_nonneg N) (sq_nonneg _))
    (fun N => mul_le_mul_of_nonneg_left (hbound N) (residualTailEnergy_nonneg N))
    hupper

/-- Under not RH, every growing exact-head legal family has divergent error. -/
theorem not_RH_exact_head_errors_tendsto_atTop
    (hRH : ¬ RiemannHypothesis) (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1) :
    Tendsto (fun N => ‖hilbertOne - F N‖^2) atTop atTop := by
  have hE : 0 < limitEnergy^2 := sq_pos_of_pos (not_RH_limitEnergy_pos hRH)
  apply tendsto_atTop.mpr
  intro B
  let D : ℝ := max B 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have ht := residualTailEnergy_tendsto_zero.eventually_lt_const (div_pos hE hD)
  filter_upwards [ht] with N hN
  by_contra hn
  have hsmall : ‖hilbertOne - F N‖^2 ≤ D := by
    dsimp [D]
    linarith [lt_of_not_ge hn, le_max_left B 0]
  have hm := mul_le_mul_of_nonneg_left hsmall (residualTailEnergy_nonneg N)
  have hh := residual_tail_product_lower N (hlegal N) (hhead N)
  have hstrict := (lt_div_iff₀ hD).mp hN
  nlinarith




/-- Simultaneous orthogonal correction in a complete head-preserving subspace.
For a finite correction basis this is the full Gram-matrix optimum. -/
def orthogonalTailRepair (K : Submodule ℝ ThresholdHilbert) [CompleteSpace K]
    (f : ThresholdHilbert) : ThresholdHilbert :=
  f + K.starProjection (hilbertOne - f)

theorem orthogonalTailRepair_error (K : Submodule ℝ ThresholdHilbert) [CompleteSpace K]
    (f : ThresholdHilbert) :
    hilbertOne - orthogonalTailRepair K f =
      (hilbertOne - f) - K.starProjection (hilbertOne - f) := by
  unfold orthogonalTailRepair
  abel

theorem orthogonalTailRepair_mem (K : Submodule ℝ ThresholdHilbert) [CompleteSpace K]
    (hK : K ≤ closedSpace) {f : ThresholdHilbert} (hf : f ∈ closedSpace) :
    orthogonalTailRepair K f ∈ closedSpace :=
  closedSpace.add_mem hf (hK (K.starProjection_apply_mem _))

theorem orthogonalTailRepair_head (K : Submodule ℝ ThresholdHilbert) [CompleteSpace K]
    (N : ℕ)
    (hKhead : ∀ g ∈ K, ∀ k, 0 < k → k ≤ N → hilbertSequence g k = 0)
    {f : ThresholdHilbert}
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    ∀ k, 0 < k → k ≤ N → hilbertSequence (orthogonalTailRepair K f) k = 1 := by
  intro k hk hkN
  change hilbertSequenceLinear (f + K.starProjection (hilbertOne - f)) k = 1
  rw [map_add]
  change hilbertSequence f k +
    hilbertSequence (K.starProjection (hilbertOne - f)) k = 1
  rw [hhead k hk hkN,
    hKhead _ (K.starProjection_apply_mem _) k hk hkN, add_zero]

/-- Pythagoras retains the complete correction energy, including mixed terms. -/
theorem orthogonalTailRepair_energy_split (K : Submodule ℝ ThresholdHilbert)
    [CompleteSpace K] (f : ThresholdHilbert) :
    ‖hilbertOne - f‖^2 = ‖hilbertOne - orthogonalTailRepair K f‖^2 +
      ‖K.starProjection (hilbertOne - f)‖^2 := by
  let e := hilbertOne - f
  let p := K.starProjection e
  have ho : inner ℝ (e - p) p = 0 :=
    Submodule.starProjection_inner_eq_zero e p (K.starProjection_apply_mem e)
  have ho' : inner ℝ p (e-p) = 0 := by rw [real_inner_comm]; exact ho
  rw [orthogonalTailRepair_error]
  change ‖e‖^2 = ‖e-p‖^2 + ‖p‖^2
  have he : e = (e-p) + p := by abel
  calc
    ‖e‖^2 = inner ℝ ((e-p)+p) ((e-p)+p) := by
      rw [real_inner_self_eq_norm_sq, ← he]
    _ = ‖e-p‖^2 + ‖p‖^2 := by
      rw [inner_add_left, inner_add_right, inner_add_right, ho, ho',
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      ring

/-- No exact finite repair can cross this canonical residual barrier. -/
theorem residual_tail_repair_gain_bound (K : Submodule ℝ ThresholdHilbert)
    [CompleteSpace K] (hK : K ≤ closedSpace) (N : ℕ)
    (hKhead : ∀ g ∈ K, ∀ k, 0 < k → k ≤ N → hilbertSequence g k = 0)
    {f : ThresholdHilbert} (hf : f ∈ closedSpace)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    limitEnergy^2 ≤ residualTailEnergy N *
      (‖hilbertOne - f‖^2 - ‖K.starProjection (hilbertOne - f)‖^2) := by
  have he := orthogonalTailRepair_energy_split K f
  have hb := residual_tail_product_lower N (orthogonalTailRepair_mem K hK hf)
    (orthogonalTailRepair_head K N hKhead hhead)
  have he' : ‖hilbertOne - f‖^2 - ‖K.starProjection (hilbertOne - f)‖^2 =
      ‖hilbertOne - orthogonalTailRepair K f‖^2 := by linarith
  rwa [he']


end CoefficientStabilization
end RiemannResearch.RH.Pareto
