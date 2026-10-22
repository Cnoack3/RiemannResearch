import RiemannResearch.RH.ParetoGibbsHilbertEnergy
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Unconditional strong convergence of the actual Gibbs iterates

This proof uses self-adjoint contraction, the exact two-step norm identity,
and density of the range of I-P² in the orthogonal complement of constants.
It does not assume the external sharp pi/4 spectral theorem or RH.
-/

open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

def hilbertGibbsIterate : ℕ → ThresholdHilbert → ThresholdHilbert
  | 0, f => f
  | n+1, f => hilbertGibbs (hilbertGibbsIterate n f)

@[simp] theorem hilbertGibbsIterate_zero (f : ThresholdHilbert) :
    hilbertGibbsIterate 0 f = f := rfl

@[simp] theorem hilbertGibbsIterate_succ (n : ℕ) (f : ThresholdHilbert) :
    hilbertGibbsIterate (n+1) f = hilbertGibbs (hilbertGibbsIterate n f) := rfl

theorem hilbertGibbsIterate_comm (n : ℕ) (f : ThresholdHilbert) :
    hilbertGibbsIterate n (hilbertGibbs f) = hilbertGibbs (hilbertGibbsIterate n f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [hilbertGibbsIterate_succ, ih]

theorem hilbertGibbsIterate_sub (n : ℕ) (f g : ThresholdHilbert) :
    hilbertGibbsIterate n (f-g) = hilbertGibbsIterate n f - hilbertGibbsIterate n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [hilbertGibbsIterate_succ, ih]
      exact map_sub hilbertGibbsLinear _ _

theorem hilbertGibbsIterate_const (n : ℕ) (c : ℝ) :
    hilbertGibbsIterate n (c • hilbertOne) = c • hilbertOne := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [hilbertGibbsIterate_succ, ih]
      exact (hilbertGibbs_fixed_iff (c • hilbertOne)).mpr ⟨c, rfl⟩

theorem hilbertGibbsIterate_norm_le (n : ℕ) (f : ThresholdHilbert) :
    ‖hilbertGibbsIterate n f‖ ≤ ‖f‖ := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hilbertGibbs_norm_le _).trans ih

theorem hilbertGibbsIterate_sq_antitone (f : ThresholdHilbert) :
    Antitone (fun n => ‖hilbertGibbsIterate n f‖ ^ 2) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := hilbertGibbs_norm_le (hilbertGibbsIterate n f)
  change ‖hilbertGibbs (hilbertGibbsIterate n f)‖ ^ 2 ≤ ‖hilbertGibbsIterate n f‖ ^ 2
  nlinarith [norm_nonneg (hilbertGibbsIterate n f),
    norm_nonneg (hilbertGibbs (hilbertGibbsIterate n f))]

/-- Exact second difference of the decreasing squared orbit norms. -/
theorem hilbertGibbsIterate_two_step_identity (n : ℕ) (f : ThresholdHilbert) :
    ‖hilbertGibbsIterate n f - hilbertGibbsIterate (n+2) f‖ ^ 2 =
      ‖hilbertGibbsIterate n f‖ ^ 2 -
        2 * ‖hilbertGibbsIterate (n+1) f‖ ^ 2 +
          ‖hilbertGibbsIterate (n+2) f‖ ^ 2 := by
  rw [norm_sub_sq_real]
  have hi : inner ℝ (hilbertGibbsIterate n f) (hilbertGibbsIterate (n+2) f) =
      ‖hilbertGibbsIterate (n+1) f‖ ^ 2 := by
    change inner ℝ (hilbertGibbsIterate n f)
      (hilbertGibbs (hilbertGibbs (hilbertGibbsIterate n f))) = _
    rw [← hilbertGibbs_pairing_symm, real_inner_self_eq_norm_sq]
    rfl
  rw [hi]

/-- Strong decay on the actual range of I-P², without a uniform spectral gap. -/
theorem hilbertGibbsIterate_defect_tendsto (f : ThresholdHilbert) :
    Tendsto (fun n => hilbertGibbsIterate n (f-hilbertGibbs (hilbertGibbs f)))
      atTop (nhds 0) := by
  have hb : BddBelow (Set.range (fun n => ‖hilbertGibbsIterate n f‖ ^ 2)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact sq_nonneg _
  have ht := tendsto_atTop_ciInf (hilbertGibbsIterate_sq_antitone f) hb
  have ht1 := ht.comp (tendsto_add_atTop_nat 1)
  have ht2 := ht.comp (tendsto_add_atTop_nat 2)
  have hs : Tendsto (fun n =>
      ‖hilbertGibbsIterate n f - hilbertGibbsIterate (n+2) f‖ ^ 2) atTop (nhds 0) := by
    simp_rw [hilbertGibbsIterate_two_step_identity]
    convert (ht.sub (ht1.const_mul 2)).add ht2 using 1 <;>
      first | rfl | ring
  have hn : Tendsto (fun n =>
      ‖hilbertGibbsIterate n f - hilbertGibbsIterate (n+2) f‖) atTop (nhds 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs.sqrt
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [hilbertGibbsIterate_sub, hilbertGibbsIterate_comm,
    hilbertGibbsIterate_succ] using hn

private theorem hilbertGibbsIterate_equicontinuous : Equicontinuous hilbertGibbsIterate := by
  apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => r) tendsto_id
  intro f g n
  simp only [dist_eq_norm]
  rw [← hilbertGibbsIterate_sub]
  exact hilbertGibbsIterate_norm_le n (f-g)

/-- Every mean-zero vector lies in the closure of the genuine decaying range. -/
theorem hilbertGibbsIterate_mean_zero_tendsto (f : ThresholdHilbert)
    (hf : inner ℝ f hilbertOne = 0) :
    Tendsto (fun n => hilbertGibbsIterate n f) atTop (nhds 0) := by
  let A : ThresholdHilbert →L[ℝ] ThresholdHilbert := 1 - hilbertGibbsContinuous ^ 2
  have hA (g : ThresholdHilbert) : A g = g - hilbertGibbs (hilbertGibbs g) := by
    simp [A, pow_two, ContinuousLinearMap.mul_apply]
  have hself : IsSelfAdjoint A :=
    (show IsSelfAdjoint (1 : ThresholdHilbert →L[ℝ] ThresholdHilbert) by simp [IsSelfAdjoint]).sub
      (hilbertGibbsContinuous_isSelfAdjoint.pow 2)
  have hadj : ContinuousLinearMap.adjoint A = A := hself
  have horth : f ∈ (A.toLinearMap.ker)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro g hg
    change A g = 0 at hg
    rw [hA] at hg
    have hsq : hilbertGibbs (hilbertGibbs g) = g := (sub_eq_zero.mp hg).symm
    obtain ⟨c, rfl⟩ := (hilbertGibbs_fixed_iff g).mp
      ((hilbertGibbs_sq_fixed_iff g).mp hsq)
    rw [real_inner_smul_left]
    rw [real_inner_comm]
    rw [hf, mul_zero]
  rw [A.orthogonal_ker, hadj] at horth
  have hclosed : IsClosed {g : ThresholdHilbert |
      Tendsto (fun n => hilbertGibbsIterate n g) atTop (nhds 0)} :=
    hilbertGibbsIterate_equicontinuous.isClosed_setOf_tendsto continuous_const
  have hsub : (A.toLinearMap.range : Set ThresholdHilbert) ⊆
      {g | Tendsto (fun n => hilbertGibbsIterate n g) atTop (nhds 0)} := by
    rintro _ ⟨g, rfl⟩
    change Tendsto (fun n => hilbertGibbsIterate n (A g)) atTop (nhds 0)
    rw [hA]
    exact hilbertGibbsIterate_defect_tendsto g
  exact (closure_minimal hsub hclosed) horth

/-- Unconditional infinite-dimensional convergence to the exact weighted mean. -/
theorem hilbertGibbsIterate_tendsto (f : ThresholdHilbert) :
    Tendsto (fun n => hilbertGibbsIterate n f) atTop
      (nhds ((inner ℝ f hilbertOne) • hilbertOne)) := by
  let c : ℝ := inner ℝ f hilbertOne
  have hm : inner ℝ (f - c • hilbertOne) hilbertOne = 0 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
    dsimp [c]
    ring
  have h := hilbertGibbsIterate_mean_zero_tendsto (f - c • hilbertOne) hm
  have hadd := h.add_const (c • hilbertOne)
  simpa only [hilbertGibbsIterate_sub, hilbertGibbsIterate_const,
    sub_add_cancel, zero_add] using hadd

end
end RiemannResearch.RH.Pareto
