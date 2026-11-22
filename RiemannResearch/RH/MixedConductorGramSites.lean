import RiemannResearch.RH.MixedConductorProjectedGram
import RiemannResearch.RH.FirstCoordinateEndpoint
import RiemannResearch.RH.IntegratedRamanujanMarkedArithmetic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Exact finite tests using a site of the Pareto projection

The determinant lemma evaluates an actual finite projection at a physical
site. At the first site its test vector is the negative Möbius vector.
The one-packet projection takes the target value exactly. The two-packet
projection overshoots it. Both evaluations use the original Pareto Gram
matrix. Only a cofinal assertion supplies a boundary criterion.
-/

noncomputable section
open Filter
open scoped Topology BigOperators Matrix

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary

open CoefficientStabilization RamanujanCanonicalOptimizer MixedConductorBasis

/-- The row of physical packet values at site `k`. -/
def siteVector (n k : ℕ) (i : Fin n) : ℝ := ramanujanPacket (i.val + 2) k

/-- A rank-one update using only the raw Gram matrix, logarithmic means, and packet values. -/
def siteGram (n k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  finitePacketGram n + Matrix.vecMulVec (meanVector n) (siteVector n k)

theorem siteVector_one (n : ℕ) : siteVector n 1 = -finiteMoebiusSource n := by
  funext i
  exact ramanujanPacket_at_one_moebius _ (by omega)

/-- The signed arithmetic determinant computes the actual finite projection at one site. -/
theorem det_siteGram (n k : ℕ) : (siteGram n k).det =
    (finitePacketGram n).det * (1 + hilbertSequence (projection n) k) := by
  rw [siteGram, Matrix.det_add_outer _ (isUnit_iff_ne_zero.mpr (finitePacketGram_det_pos n).ne')]
  congr 2
  rw [← packetCandidate_eq_projection, ← anchoredEvaluationCLM_apply]
  change dotProduct (siteVector n k) ((finitePacketGram n)⁻¹.mulVec (meanVector n)) =
    anchoredEvaluationCLM k (∑ i : Fin n, packetCoefficients n i • ramanujanPacketHilbert (i.val + 2))
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, anchoredEvaluationCLM_apply,
    hilbertSequence_ramanujanPacketHilbert, packetCoefficients_eq_inverseGram]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

private theorem projection_site_tendsto (k : ℕ) :
    Tendsto (fun n => hilbertSequence (projection n) k) atTop
      (𝓝 ((1 - limitEnergy) * hilbertSequence normalizedScreenedTwo k)) := by
  have h := ((anchoredEvaluationCLM k).continuous.tendsto limitProjection).comp projection_tendsto
  simpa only [Function.comp_def, limitProjection_eq_scaled_screenedTwo, map_smul,
    smul_eq_mul, anchoredEvaluationCLM_apply] using h

/-- Arbitrarily late nonnegative physical values at each fixed positive site suffice. -/
theorem boundary_eq_zero_iff_cofinal_site_det_sign :
    CenteredMeanSnake.boundary = 0 ↔ ∀ k : ℕ, 0 < k → ∀ N : ℕ, ∃ n ≥ N,
      (finitePacketGram n).det ≤ (siteGram n k).det := by
  constructor
  · intro hb k hk N
    have hu := CenteredMeanSnake.boundary_eq_zero_iff_screened.mp hb
    have hv : hilbertSequence normalizedScreenedTwo k = 1 := by
      simp [hu, hilbertOne_sequence, zeroAnchor, hk.ne']
    have ht := projection_site_tendsto k
    rw [hv, mul_one] at ht
    obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually_const_lt packetLimitMass_pos)
    refine ⟨max M N, le_max_right _ _, ?_⟩
    rw [det_siteGram]
    nlinarith only [mul_pos (finitePacketGram_det_pos (max M N)) (hM (max M N) (le_max_left M N))]
  · intro h
    apply CenteredMeanSnake.boundary_eq_zero_iff_screened.mpr
    apply normalizedScreenedTwo_eq_one_of_oneSidedBound
    refine Or.inl ⟨0, fun k hk => ?_⟩
    by_contra! hneg
    have hp := mul_neg_of_pos_of_neg packetLimitMass_pos hneg
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((projection_site_tendsto k).eventually_lt_const hp)
    obtain ⟨n, hn, hd⟩ := h k hk N
    rw [det_siteGram] at hd
    nlinarith only [hd, mul_neg_of_pos_of_neg (finitePacketGram_det_pos n) (hN n hn)]

/-- With nonzero boundary, some fixed site eventually violates any prescribed negative floor. -/
theorem eventually_negative_site_det_of_boundary_ne (hb : CenteredMeanSnake.boundary ≠ 0)
    (B : ℝ) : ∃ k : ℕ, 0 < k ∧ ∀ᶠ n in atTop,
      (siteGram n k).det < -B * (finitePacketGram n).det := by
  have hu : normalizedScreenedTwo ≠ hilbertOne :=
    fun he => hb (CenteredMeanSnake.boundary_eq_zero_iff_screened.mpr he)
  obtain ⟨k, hk, hw⟩ := (screenedTwo_unbounded_both_sides_of_ne_one hu
    ((B + 1) / (1 - limitEnergy))).2
  have hl : (1 - limitEnergy) * hilbertSequence normalizedScreenedTwo k < -B - 1 := by
    have hw' : hilbertSequence normalizedScreenedTwo k < (-B - 1) / (1 - limitEnergy) := by
      rw [← neg_div] at hw
      convert hw using 1
      ring
    simpa only [mul_comm] using (lt_div_iff₀ packetLimitMass_pos).mp hw'
  refine ⟨k, hk, ?_⟩
  filter_upwards [(projection_site_tendsto k).eventually_lt_const hl] with n hn
  rw [det_siteGram]
  nlinarith only [mul_lt_mul_of_pos_left hn (finitePacketGram_det_pos n)]

private theorem first_site_det_budget (n : ℕ) (ε : ℝ) :
    (2 - ε) * (finitePacketGram n).det ≤
      (siteGram n 1).det + (2 - Real.sqrt 2) * (meanPencil n 1).det ↔
        1 - hilbertSequence (projection n) 1 ≤ (2 - Real.sqrt 2) * energy n + ε := by
  rw [det_siteGram, det_meanPencil, one_mul, packet_energy_eq_original]
  have hm : (finitePacketGram n).det * (1 + hilbertSequence (projection n) 1) +
        (2 - Real.sqrt 2) * ((finitePacketGram n).det * (1 - packetMass n)) =
      (1 + hilbertSequence (projection n) 1 + (2 - Real.sqrt 2) * (1 - packetMass n)) *
        (finitePacketGram n).det := by ring
  rw [hm, mul_le_mul_iff_left₀ (finitePacketGram_det_pos n)]
  constructor <;> intro h <;> linarith only [h]

/-- The dyadic first-site budget gives an arithmetic equivalence with the ambient boundary. -/
theorem boundary_eq_zero_iff_first_site_det_budget :
    CenteredMeanSnake.boundary = 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      (2 - ε) * (finitePacketGram n).det ≤
        (siteGram n 1).det + (2 - Real.sqrt 2) * (meanPencil n 1).det := by
  have he : CenteredMeanSnake.boundary = 0 ↔ limitResidual = 0 :=
    CenteredMeanSnake.boundary_eq_zero_iff_one_mem.trans
      (limitEnergy_zero_iff_mem.symm.trans limitResidual_zero_iff_energy_zero.symm)
  rw [he, ← projection_cofinal_endpoint_budget_iff_residual_zero]
  simp only [first_site_det_budget]

/-- Arbitrarily late single-stage certificates at zero slack imply RH. -/
theorem riemannHypothesis_of_cofinal_first_site_det
    (h : ∀ N : ℕ, ∃ n ≥ N, 2 * (finitePacketGram n).det ≤
      (siteGram n 1).det + (2 - Real.sqrt 2) * (meanPencil n 1).det) :
    RiemannHypothesis := by
  apply CenteredMeanSnake.riemannHypothesis_of_boundary_eq_zero
  apply boundary_eq_zero_iff_first_site_det_budget.mpr
  intro ε hε N
  obtain ⟨n, hn, hd⟩ := h N
  exact ⟨n, hn, (mul_le_mul_of_nonneg_right (by linarith : 2 - ε ≤ 2)
    (finitePacketGram_det_pos n).le).trans hd⟩

/-- At site one the determinant requires one inverse Gram solve with the mean vector. -/
theorem first_site_det_as_one_solve (n : ℕ) :
    (siteGram n 1).det = (finitePacketGram n).det *
      (1 - dotProduct (finiteMoebiusSource n) ((finitePacketGram n)⁻¹.mulVec (meanVector n))) := by
  rw [siteGram, Matrix.det_add_outer _ (isUnit_iff_ne_zero.mpr (finitePacketGram_det_pos n).ne'),
    siteVector_one]
  simp [dotProduct, sub_eq_add_neg]

/-- The same exact solve supplies both terms of the cofinal dyadic test. -/
theorem riemannHypothesis_of_cofinal_first_site_solve
    (h : ∀ N : ℕ, ∃ n ≥ N, let c := (finitePacketGram n)⁻¹.mulVec (meanVector n)
      1 ≤ -dotProduct (finiteMoebiusSource n) c +
        (2 - Real.sqrt 2) * (1 - dotProduct (meanVector n) c)) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_first_site_det
  intro N
  obtain ⟨n, hn, hc⟩ := h N
  refine ⟨n, hn, ?_⟩
  dsimp only at hc
  have hm : dotProduct (meanVector n) ((finitePacketGram n)⁻¹.mulVec (meanVector n)) =
      packetMass n := (packetMass_eq_inverseGram n).symm
  rw [hm] at hc
  rw [first_site_det_as_one_solve, det_meanPencil, one_mul]
  nlinarith only [mul_le_mul_of_nonneg_left hc (finitePacketGram_det_pos n).le]

/-- Conductor two already attains the first-site endpoint at one finite stage. -/
theorem projection_one_first_site : hilbertSequence (projection 1) 1 = 1 := by
  have h := det_siteGram 1 1
  simp only [siteGram, Matrix.det_fin_one, Matrix.add_apply] at h
  change inner ℝ (ramanujanPacketHilbert 2) (ramanujanPacketHilbert 2) +
    meanVector 1 0 * ramanujanPacket 2 1 =
      inner ℝ (ramanujanPacketHilbert 2) (ramanujanPacketHilbert 2) * (1 + _) at h
  have hm : meanVector 1 0 = Real.log 2 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have hr : ramanujanPacket 2 1 = 1 := by
    rw [ramanujanPacket_at_one_moebius _ (by decide),
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  rw [real_inner_self_eq_norm_sq, ramanujanPacketHilbert_two_norm_sq, hm, hr] at h
  exact mul_left_cancel₀ (Real.log_pos (by norm_num : (1:ℝ)<2)).ne' (by linarith only [h])

/-- The signed first-site overshoot has a closed factorization at stage two. -/
theorem projection_two_first_site_gap :
    let a := Real.log 2
    let b := Real.log 3
    let c := Real.pi / (3 * Real.sqrt 3)
    (finitePacketGram 2).det * (hilbertSequence (projection 2) 1 - 1) =
      (c - b/2) * (b/2 - a + c) := by
  dsimp only
  have h := det_siteGram 2 1
  have hh := det_two_meanPencil 0
  simp only [meanPencil, zero_smul, sub_zero, zero_mul] at hh
  have H0 : meanVector 2 0 = Real.log 2 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have H1 : meanVector 2 1 = Real.log 3 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  have s0 : siteVector 2 1 0 = 1 := by
    rw [siteVector_one]; norm_num [finiteMoebiusSource, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have s1 : siteVector 2 1 1 = 1 := by
    rw [siteVector_one]; norm_num [finiteMoebiusSource, ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  have g00 : finitePacketGram 2 0 0 = Real.log 2 :=
    (real_inner_self_eq_norm_sq _).trans ramanujanPacketHilbert_two_norm_sq
  have g11 : finitePacketGram 2 1 1 = 2 * Real.log 3 - Real.pi / (3 * Real.sqrt 3) :=
    (real_inner_self_eq_norm_sq _).trans three_packet_norm_sq
  have g01 : finitePacketGram 2 0 1 = Real.log 2 + Real.log 3 / 2 -
      Real.pi / (3 * Real.sqrt 3) := two_three_packet_inner
  have g10 : finitePacketGram 2 1 0 = finitePacketGram 2 0 1 := real_inner_comm _ _
  conv_lhs at h => rw [Matrix.det_fin_two]
  change (finitePacketGram 2 0 0 + meanVector 2 0 * siteVector 2 1 0) *
      (finitePacketGram 2 1 1 + meanVector 2 1 * siteVector 2 1 1) -
    (finitePacketGram 2 0 1 + meanVector 2 0 * siteVector 2 1 1) *
      (finitePacketGram 2 1 0 + meanVector 2 1 * siteVector 2 1 0) =
    (finitePacketGram 2).det * (1 + hilbertSequence (projection 2) 1) at h
  simp only [g10, g00, g11, g01, H0, H1, s0, s1, mul_one] at h
  linear_combination -h - 2 * hh

/-- The two-conductor projection is strictly above one at site one. -/
theorem projection_two_first_site_gt_one : 1 < hilbertSequence (projection 2) 1 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 8/7) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have hlog : Real.log 3 < 8/7 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr (by linarith)
  have hs : Real.sqrt 3 < 7/4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hc : (4/7:ℝ) < Real.pi / (3 * Real.sqrt 3) :=
    (lt_div_iff₀ (by positivity)).mpr (by linarith only [hs, Real.pi_gt_three])
  have hab := Real.strictMonoOn_log (by norm_num : (2:ℝ) ∈ Set.Ioi 0)
    (by norm_num : (3:ℝ) ∈ Set.Ioi 0) (by norm_num : (2:ℝ) < 3)
  have ha : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hf := mul_pos (show 0 < Real.pi / (3 * Real.sqrt 3) - Real.log 3/2 by linarith)
    (show 0 < Real.log 3/2 - Real.log 2 + Real.pi / (3 * Real.sqrt 3) by linarith)
  have hg := projection_two_first_site_gap
  dsimp only at hg
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (finitePacketGram_det_pos 2)).mp (hg.symm ▸ hf))

/-- Both nonempty stages through conductor three satisfy the dyadic test with strict slack. -/
theorem first_two_det_certificates (n : ℕ) (h₁ : 1 ≤ n) (h₂ : n ≤ 2) :
    2 * (finitePacketGram n).det <
      (siteGram n 1).det + (2 - Real.sqrt 2) * (meanPencil n 1).det := by
  have hp : 1 ≤ hilbertSequence (projection n) 1 := by
    rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
    · exact projection_one_first_site.ge
    · exact projection_two_first_site_gt_one.le
  have hc : 0 < 2 - Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [det_siteGram]
  nlinarith only [mul_le_mul_of_nonneg_left hp (finitePacketGram_det_pos n).le,
    mul_pos hc (centered_det_pos n)]

/-- A single finite residual certificate fixes the sign at a physical site at every later stage. -/
theorem site_positive_of_residual_lt_weight {m n k : ℕ} (hmn : m ≤ n) (hk : 0 < k)
    (hcert : 1 - packetMass m < positiveWeight k) :
    0 < hilbertSequence (projection n) k := by
  let x := hilbertOne - packetCandidate n
  have he : ‖x‖^2 = 1 - packetMass n := packet_error n
  have ht : positiveWeight k * (hilbertSequence x k)^2 ≤ ‖x‖^2 := by
    rw [hilbert_norm_weighted_sq]
    exact (hilbertSequence_square_summable x).le_tsum k
      (fun j _ => mul_nonneg (positiveWeight_nonneg j) (sq_nonneg _))
  have hv : hilbertSequence x k = 1 - hilbertSequence (projection n) k := by
    dsimp only [x]
    rw [← anchoredEvaluationCLM_apply, map_sub, packetCandidate_eq_projection,
      anchoredEvaluationCLM_apply, anchoredEvaluationCLM_apply, hilbertOne_sequence]
    simp [zeroAnchor, hk.ne']
  rw [hv, he] at ht
  by_contra! hp
  have hsq : 1 ≤ (1 - hilbertSequence (projection n) k)^2 := by
    nlinarith only [hp, sq_nonneg (hilbertSequence (projection n) k)]
  have hn := mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg k)
  linarith only [ht, hn, hcert, packetMass_monotone hmn]

/-- The two-packet arithmetic trial has an exact Pareto error. -/
theorem half_two_three_trial_error :
    ‖hilbertOne - (1/2 : ℝ) • (ramanujanPacketHilbert 2 + ramanujanPacketHilbert 3)‖^2 =
      1 - (Real.log 2 + Real.log 3 + 3 * (Real.pi / (3 * Real.sqrt 3))) / 4 := by
  have hm (p : ℕ) (hp : p.Prime) :
      inner ℝ hilbertOne (ramanujanPacketHilbert p) = Real.log (p : ℝ) :=
    (real_inner_comm (ramanujanPacketHilbert p) hilbertOne).trans
      ((RamanujanCanonicalOptimizer.packet_inner_one p).trans
        (ArithmeticFunction.vonMangoldt_apply_prime hp))
  rw [norm_sub_sq_real, hilbertOne_norm_sq, real_inner_smul_right, inner_add_right,
    hm 2 Nat.prime_two, hm 3 Nat.prime_three, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, norm_add_sq_real, ramanujanPacketHilbert_two_norm_sq, three_packet_norm_sq,
    two_three_packet_inner]
  push_cast
  ring

/-- The complete squared error after conductors 2 and 3 is strictly below the mass of site 2. -/
theorem two_stage_residual_lt_sixth : 1 - packetMass 2 < 1/6 := by
  have hh : Fintype.linearCombination ℝ (fun i : Fin 2 => ramanujanPacketHilbert (i.val + 2))
      (fun _ => (1/2 : ℝ)) =
      (1/2 : ℝ) • (ramanujanPacketHilbert 2 + ramanujanPacketHilbert 3) := by
    change (∑ i : Fin 2, (1/2 : ℝ) • ramanujanPacketHilbert (i.val + 2)) = _
    rw [Fin.sum_univ_two, smul_add]
    rfl
  have hmin : 1 - packetMass 2 ≤
      ‖hilbertOne - (1/2 : ℝ) • (ramanujanPacketHilbert 2 + ramanujanPacketHilbert 3)‖^2 := by
    rw [← hh, packet_completion]
    exact le_add_of_nonneg_right (sq_nonneg _)
  rw [half_two_three_trial_error] at hmin
  have hlo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(9/8:ℝ)⁻¹)
  rw [Real.log_inv] at hlo
  have hhi := Real.log_lt_log (by positivity : 0 < (9/8:ℝ)^15)
    (by norm_num : (9/8:ℝ)^15 < 2*3)
  rw [Real.log_pow, Real.log_mul (by norm_num) (by norm_num)] at hhi
  have hs : Real.sqrt 3 < 7/4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hc : (4/7:ℝ) < Real.pi / (3 * Real.sqrt 3) :=
    (lt_div_iff₀ (by positivity)).mpr (by linarith only [hs, Real.pi_gt_three])
  norm_num at hlo hhi
  linarith only [hmin, hlo, hhi, hc]

/-- Both of the first physical sites satisfy the strict determinant sign at every stage from two. -/
theorem first_two_sites_det_positive (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k = 1 ∨ k = 2) :
    (finitePacketGram n).det < (siteGram n k).det := by
  have hw : (1/6:ℝ) ≤ positiveWeight k := by
    rcases hk with rfl | rfl <;> norm_num [positiveWeight]
  have hpos := site_positive_of_residual_lt_weight hn (show 0 < k by omega)
    (two_stage_residual_lt_sixth.trans_le hw)
  rw [det_siteGram]
  nlinarith only [mul_pos (finitePacketGram_det_pos n) hpos]

/-- The strict finite overshoot rules out monotone extrapolation to later stages. -/
theorem projection_first_site_not_monotone :
    ¬ Monotone (fun n => hilbertSequence (projection n) 1) := by
  intro hmono
  have hle : hilbertSequence (projection 2) 1 ≤ hilbertSequence limitProjection 1 :=
    ge_of_tendsto projection_firstCoordinate_tendsto
      ((eventually_ge_atTop 2).mono (fun n hn => hmono hn))
  have hup := firstCoordinate_nonneg
  rw [limitResidual_first_eq_one_sub_projection] at hup
  linarith only [hle, hup, projection_two_first_site_gt_one]

end RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary
