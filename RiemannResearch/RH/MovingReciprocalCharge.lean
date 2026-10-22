import RiemannResearch.RH.BalazardReciprocalCharge
import RiemannResearch.RH.ResidueGramMobiusCorrection

/-!
# Moving reciprocal charge sums

Source: assembly of the project's proved Balazard reciprocal-charge theorem
(Michel Balazard, arXiv:1812.04309, Propositions 6--7) with strong convergence
of the actual residue projections. No additional arithmetic hypothesis is
introduced. Uniform boundedness of the reciprocal-charge Riesz vectors is
essential when both the tested vector and the conductor cutoff move.

The resulting limit is minus the first physical residual coordinate. The
result does not assert that this coordinate vanishes.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

/-- Balazard's actual reciprocal-charge vectors remain weakly null when
paired with any strongly convergent moving Hilbert vector. -/
theorem reciprocalChargeRiesz_inner_moving_tendsto_zero
    (f : ℕ → ThresholdHilbert) (g : ThresholdHilbert)
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun N => inner ℝ (reciprocalChargeRiesz N) (f N)) atTop (𝓝 0) := by
  have hdiff : Tendsto (fun N => ‖f N - g‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hf.sub_const g).norm
  have herr : Tendsto (fun N => inner ℝ (reciprocalChargeRiesz N) (f N - g))
      atTop (𝓝 0) := by
    have hupper : Tendsto (fun N => 7 * ‖f N - g‖) atTop (𝓝 0) := by
      simpa using hdiff.const_mul 7
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hupper
    intro N
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul_of_nonneg_right (reciprocalChargeRiesz_norm_le N) (norm_nonneg _))
  have hfixed : Tendsto (fun N => inner ℝ (reciprocalChargeRiesz N) g)
      atTop (𝓝 0) := by
    simpa only [real_inner_comm] using reciprocalChargeRiesz_weak_zero g
  have he (N : ℕ) : inner ℝ (reciprocalChargeRiesz N) (f N) =
      inner ℝ (reciprocalChargeRiesz N) (f N - g) +
        inner ℝ (reciprocalChargeRiesz N) g := by
    rw [inner_sub_right]
    ring
  simpa only [← he, add_zero] using herr.add hfixed

/-- Exact removal of the index-one charge, for an arbitrary moving head. -/
theorem mobiusDifference_reciprocal_from_two_eq_inner (N : ℕ) (hN : 1 ≤ N)
    (f : ThresholdHilbert) :
    (∑ m ∈ Finset.Icc 2 N, mobiusDifferenceCLM m f / (m : ℝ)) =
      inner ℝ (reciprocalChargeRiesz N) f - hilbertSequence f 1 := by
  have hfirst : mobiusDifferenceCLM 1 f = hilbertSequence f 1 := by
    simp [mobiusDifferenceCLM_apply, mobiusDifference]
  have hu : ({1} : Finset ℕ) ∪ Finset.Icc 2 N = Finset.Icc 1 N := by
    ext m
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hd : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 N) := by simp
  rw [reciprocalChargeRiesz_inner, ← hu, Finset.sum_union hd]
  simp only [Finset.sum_singleton, Nat.cast_one, div_one, hfirst]
  ring

/-- An unconditional arithmetic sum rule with a strongly convergent moving
vector. The norm bound in Balazard's theorem justifies the joint limit. -/
theorem mobiusDifference_reciprocal_moving_from_two_tendsto
    (f : ℕ → ThresholdHilbert) (g : ThresholdHilbert)
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun N => ∑ m ∈ Finset.Icc 2 N,
      mobiusDifferenceCLM m (f N) / (m : ℝ)) atTop
        (𝓝 (-hilbertSequence g 1)) := by
  have hfirst : Tendsto (fun N => hilbertSequence (f N) 1) atTop
      (𝓝 (hilbertSequence g 1)) := by
    simpa only [Function.comp_def, anchoredEvaluationCLM_apply] using
      (anchoredEvaluationCLM 1).continuous.tendsto g |>.comp hf
  have ht := (reciprocalChargeRiesz_inner_moving_tendsto_zero f g hf).sub hfirst
  simp only [zero_sub] at ht
  exact ht.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact (mobiusDifference_reciprocal_from_two_eq_inner N hN (f N)).symm)

/-- The normalized last charge vanishes even when the tested vector moves
strongly. This controls a growing conductor, rather than a fixed coordinate. -/
theorem mobiusDifference_moving_endpoint_div_tendsto_zero
    (f : ℕ → ThresholdHilbert) (g : ThresholdHilbert)
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun N => mobiusDifferenceCLM (N + 1) (f N) / ((N + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hbase := mobiusDifference_reciprocal_moving_from_two_tendsto f g hf
  have hshift := mobiusDifference_reciprocal_moving_from_two_tendsto
    (fun N => f (N - 1)) g (hf.comp (tendsto_sub_atTop_nat 1))
  have hnext : Tendsto (fun N => ∑ m ∈ Finset.Icc 2 (N + 1),
      mobiusDifferenceCLM m (f N) / (m : ℝ)) atTop
        (𝓝 (-hilbertSequence g 1)) := by
    simpa only [Function.comp_def, Nat.add_sub_cancel] using
      hshift.comp (tendsto_add_atTop_nat 1)
  have hdiff := hnext.sub hbase
  simp only [sub_self] at hdiff
  exact hdiff.congr' (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1)]
    ring)

namespace CoefficientStabilization.GramMobiusCorrection

/-- Any diverging projection stage may accompany the increasing conductor
head. This includes the same-stage sum, with its terminal conductor omitted. -/
theorem truncated_reciprocalCorrection_tendsto (s : ℕ → ℕ)
    (hs : Tendsto s atTop atTop) :
    Tendsto (fun N => ∑ m ∈ Finset.Icc 2 N,
      correction (s N) m / (m : ℝ)) atTop
        (𝓝 (-hilbertSequence limitResidual 1)) := by
  have hf : Tendsto (fun N => hilbertOne - projection (s N)) atTop
      (𝓝 limitResidual) := by
    simpa only [limitResidual, Function.comp_def] using
      tendsto_const_nhds.sub (projection_tendsto.comp hs)
  have ht := mobiusDifference_reciprocal_moving_from_two_tendsto
    (fun N => hilbertOne - projection (s N)) limitResidual hf
  apply ht.congr'
  exact Eventually.of_forall (fun N => by
    apply Finset.sum_congr rfl
    intro m hm
    rw [correction_eq_residual_coordinate (s N) m
      (by have := (Finset.mem_Icc.mp hm).1; omega)])

/-- The actual growing inverse-Gram correction is sublinear in its conductor
along every projection-stage sequence tending to infinity. -/
theorem correction_moving_endpoint_div_tendsto_zero (s : ℕ → ℕ)
    (hs : Tendsto s atTop atTop) :
    Tendsto (fun N => correction (s N) (N + 1) / ((N + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hf : Tendsto (fun N => hilbertOne - projection (s N)) atTop
      (𝓝 limitResidual) := by
    simpa only [limitResidual, Function.comp_def] using
      tendsto_const_nhds.sub (projection_tendsto.comp hs)
  have ht := mobiusDifference_moving_endpoint_div_tendsto_zero
    (fun N => hilbertOne - projection (s N)) limitResidual hf
  apply ht.congr'
  exact Eventually.of_forall (fun N => by
    dsimp only
    rw [correction_eq_residual_coordinate (s N) (N + 1) (by omega)])

/-- In particular, the terminal inverse-Gram output at stage N is o(N). -/
theorem correction_terminal_div_tendsto_zero :
    Tendsto (fun N => correction N (N + 1) / ((N + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  simpa only [id_eq] using correction_moving_endpoint_div_tendsto_zero id tendsto_id

/-- The actual last optimal projection coefficient is also o(N). -/
theorem coefficient_terminal_div_tendsto_zero :
    Tendsto (fun N => coefficient N (N + 1) / ((N + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hmu : Tendsto (fun N : ℕ =>
      (ArithmeticFunction.moebius (N + 1) : ℝ) / ((N + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    have ht := (mobiusReciprocalSum_tendsto_zero.comp (tendsto_add_atTop_nat 1)).sub
      mobiusReciprocalSum_tendsto_zero
    simpa only [Function.comp_def, mobiusReciprocalSum_succ, add_sub_cancel_left,
      sub_self] using ht
  have ht := correction_terminal_div_tendsto_zero.sub hmu
  simpa only [correction, add_div, add_sub_cancel_right, sub_self] using ht

end CoefficientStabilization.GramMobiusCorrection
end RiemannResearch.RH.Pareto
