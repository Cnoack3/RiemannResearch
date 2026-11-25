import RiemannResearch.RH.PhysicalHeadSectionGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # A single cofinal sequence of finite physical-head sections

The cutoff and the finite window may vary independently. RH is equivalent to
the existence of one sequence for which logarithmic norm growth has exponent
zero. In the RH direction the cutoffs may be all positive integers in order.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadSectionGrowth
open CoefficientStabilization AffineHeadTower CenteredMeanSnake.PhysicalHeadSections

private theorem one_le_norm_of_mem_fiber {v : ThresholdHilbert} {N : ℕ} (hv : v ∈ fiber N) :
    1 ≤ ‖v‖ := by
  have h1 : ‖hilbertOne‖ = 1 := by nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  have h := real_inner_le_norm v hilbertOne
  rwa [hv.2.1, h1, mul_one] at h

/-- A single sequence of legal finite mixed corrections and physical head cutoffs.
The numerator is the logarithm of the norm of the actual mean-one section. -/
def CofinalLogSections (g : ThresholdHilbert) : Prop :=
  ∃ N B : ℕ → ℕ, ∃ m : ℕ → ThresholdHilbert, Tendsto N atTop atTop ∧
    (∀ j, m j ∈ mixedSpace (Finset.Icc 2 (B j)) ∧ g+m j ∈ fiber (N j)) ∧
    Tendsto (fun j => Real.log ‖g+m j‖ / Real.log ((N j : ℝ)+1)) atTop (𝓝 0)

theorem cofinalLogSections_iff_rh (g : ThresholdHilbert) (hg : g ∈ closedSpace)
    (hm : inner ℝ g hilbertOne = 1) : CofinalLogSections g ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨N,B,m,hN,hlegal,hlog⟩
    apply (finiteSectionSubpower_iff_rh g hg hm).mp
    intro ε hε
    refine ⟨1, Filter.frequently_atTop.2 ?_⟩
    intro K
    have hsmall := hlog.eventually_lt_const (show (0 : ℝ) < ε/2 by linarith)
    obtain ⟨j,hj,hjN⟩ := (hsmall.and (hN.eventually_ge_atTop (max K 1))).exists
    have hK : K ≤ N j := (le_max_left _ _).trans hjN
    have hN1 : 1 ≤ N j := (le_max_right _ _).trans hjN
    have hbase : 1 < (N j : ℝ)+1 := by
      have : (1 : ℝ) ≤ (N j : ℝ) := by exact_mod_cast hN1
      linarith
    have hpos : 0 < ‖g+m j‖ := lt_of_lt_of_le zero_lt_one
      (one_le_norm_of_mem_fiber (hlegal j).2)
    have hlogs : Real.log ‖g+m j‖ < (ε/2) * Real.log ((N j : ℝ)+1) :=
      (div_lt_iff₀ (Real.log_pos hbase)).mp hj
    have hsq : ‖g+m j‖^2 ≤ ((N j : ℝ)+1)^ε := by
      apply (Real.log_le_log_iff (pow_pos hpos 2) (Real.rpow_pos_of_pos (by linarith) _)).mp
      rw [Real.log_pow, Real.log_rpow (by linarith : 0 < (N j : ℝ)+1)]
      push_cast
      linarith
    exact ⟨N j, hK, B j, m j, (hlegal j).1, (hlegal j).2, by simpa only [one_mul] using hsq⟩
  · intro hRH
    have he := BaezDuarte.naturalApproximation_iff_one_mem.mp
      (CenteredMeanSnake.riemannHypothesis_iff_naturalApproximation.mp hRH)
    choose B m hB hf hnear using
      fun N : ℕ => exists_finite_section_near_one g hg hm he N (by norm_num : (0:ℝ)<1)
    refine ⟨id, B, m, tendsto_id, fun N => ⟨hB N, hf N⟩, ?_⟩
    have h1 : ‖hilbertOne‖ = 1 := by nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
    have hbound (N : ℕ) : ‖g+m N‖ ≤ 2 := by
      calc ‖g+m N‖ = ‖((g+m N)-hilbertOne)+hilbertOne‖ := by rw [sub_add_cancel]
           _ ≤ ‖(g+m N)-hilbertOne‖+‖hilbertOne‖ := norm_add_le _ _
           _ ≤ 2 := by rw [norm_sub_rev, h1]; linarith [hnear N]
    have htop : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
      tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
    have hz : Tendsto (fun N : ℕ => Real.log 2 / Real.log ((N : ℝ)+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp htop)
    apply squeeze_zero _ _ hz
    · intro N
      exact div_nonneg (Real.log_nonneg (one_le_norm_of_mem_fiber (hf N)))
        (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N]))
    · intro N
      apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N]))
      exact Real.log_le_log (lt_of_lt_of_le zero_lt_one (one_le_norm_of_mem_fiber (hf N))) (hbound N)

/-- Specialization to the mean-one parity packet and finite mixed conductor corrections. -/
theorem parity_cofinalLogSections_iff_rh :
    CofinalLogSections ((Real.log 2)⁻¹ • ramanujanPacketHilbert 2) ↔ RiemannHypothesis := by
  apply cofinalLogSections_iff_rh
  · exact closedSpace.smul_mem _ (packet_mem_closedSpace 2 (by decide))
  · rw [real_inner_smul_left, hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
      paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
      Nat.cast_ofNat, inv_mul_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

end RiemannResearch.RH.Pareto.PrimePowerSchur.PhysicalHeadSectionGrowth
