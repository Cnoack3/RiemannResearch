import Mathlib.LinearAlgebra.Vandermonde
import RiemannResearch.RH.CenteredMeanFiniteDescent
import RiemannResearch.RH.MixedConductorGramZeroFree
import RiemannResearch.RH.MixedConductorDilation

/-!
# Strict descent of the finite mixed-conductor errors

Every finite mean-one fit lies in a finite legal span. The limiting screened
section lies outside each of those spans. The exact error decomposition hence
gives strict descent beyond every cutoff, including infinitely many strict
one-step gains. A finite divisor expansion gives a separate test for those
gains using the dilation of any mixed packet.
-/

noncomputable section

open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization CaptureGains

/-- The finite mixed fit of the conductor-two packet is a finite legal vector,
including the empty mixed windows. -/
theorem fixedTwoTrial_mem_finiteSpace (B : ℕ) :
    fixedTwoTrial B ∈ finiteSpace (B + 1) := by
  have hp (q : ℕ) (hlo : 2 ≤ q) (hhi : q ≤ B + 2) :
      ramanujanPacketHilbert q ∈ finiteSpace (B + 1) := by
    change ramanujanPacketHilbert q ∈
      Submodule.span ℝ (Set.range (fun i : Fin (B + 1) => residueAtom i.val))
    rw [← finitePacket_span_eq]
    let i : Fin (B + 1) := ⟨q - 2, by omega⟩
    have hi : i.val + 2 = q := by dsimp [i]; omega
    exact Submodule.subset_span ⟨i, congrArg ramanujanPacketHilbert hi⟩
  have hK : mixedSpace (Finset.Icc 2 B) ≤ finiteSpace (B + 1) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, rfl⟩
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp q.property).1
    exact hp q.val hlo (by omega)
  exact (finiteSpace (B + 1)).smul_mem _
    ((finiteSpace (B + 1)).sub_mem (hp 2 le_rfl (by omega))
      (hK ((mixedSpace (Finset.Icc 2 B)).starProjection_apply_mem _)))

theorem fixedTwoTrial_ne_screened (B : ℕ) :
    fixedTwoTrial B ≠ normalizedScreenedTwo := by
  intro he
  exact PacketGramBoundary.normalizedScreenedTwo_not_mem_finiteSpace (B + 1)
    (he ▸ fixedTwoTrial_mem_finiteSpace B)

/-- The unnormalized finite error is strictly above the actual ambient
boundary energy, whether that energy vanishes or is positive. -/
theorem boundary_energy_lt_deficit (B : ℕ) :
    ‖boundary‖ ^ 2 * (Real.log 2) ^ 2 < deficit B := by
  have ht := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (fixedTwoTrial_ne_screened B)))
  have ha : 0 < (Real.log 2) ^ 2 := by positivity
  apply (lt_div_iff₀ ha).mp
  rw [finiteWindow_deficit_eq_boundary_add_tail]
  linarith

theorem deficit_tendsto_boundary_energy :
    Tendsto deficit atTop (𝓝 (‖boundary‖ ^ 2 * (Real.log 2) ^ 2)) := by
  have ht := ((fixedTwoTrial_tendsto.sub_const normalizedScreenedTwo).norm.pow 2)
  have hzero : Tendsto (fun B => ‖fixedTwoTrial B - normalizedScreenedTwo‖ ^ 2)
      atTop (𝓝 0) := by simpa using ht
  have h := ((tendsto_const_nhds (x := ‖boundary‖ ^ 2)).add hzero).mul_const ((Real.log 2)^2)
  simp only [add_zero] at h
  apply h.congr'
  exact Eventually.of_forall fun B =>
    ((div_eq_iff (show (Real.log 2)^2 ≠ 0 by positivity)).mp
      (finiteWindow_deficit_eq_boundary_add_tail B)).symm

/-- At a sufficiently large cutoff the excess over the limiting energy falls
below any prescribed positive fraction of its value at the starting cutoff. -/
theorem eventually_contracts_excess (B : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      deficit N - ‖boundary‖ ^ 2 * (Real.log 2) ^ 2 <
        c * (deficit B - ‖boundary‖ ^ 2 * (Real.log 2) ^ 2) := by
  have h := deficit_tendsto_boundary_energy.sub_const (‖boundary‖ ^ 2 * (Real.log 2) ^ 2)
  exact h.eventually_lt_const (by
    rw [sub_self]
    exact mul_pos hc (sub_pos.mpr (boundary_energy_lt_deficit B)))

/-- Strict positive one-step gains occur after every prescribed stage. -/
theorem exists_positive_relativeGain_from (B : ℕ) :
    ∃ k ≥ B, 0 < relativeGain k := by
  by_contra! hz
  have hflat (j : ℕ) : deficit (B + j) = deficit B := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.add_succ, deficit_recurrence,
        le_antisymm (hz (B + j) (by omega)) (relativeGain_bounds _).1,
        sub_zero, mul_one, ih]
  obtain ⟨N, hBN, hlt⟩ := ((eventually_ge_atTop B).and
    (deficit_tendsto_boundary_energy.eventually_lt_const (boundary_energy_lt_deficit B))).exists
  have he := hflat (N - B)
  rw [Nat.add_sub_of_le hBN] at he
  exact (ne_of_lt hlt) he

/-- The dilation of a mixed packet of conductor q already belongs to the
finite conductor window through q m. -/
theorem dilated_mixed_packet_mem_window (m q : ℕ) (hm : 0 < m)
    (hq : 1 < q) (hmix : ¬ IsPrimePow q) :
    hilbertDilation m hm (ramanujanPacketHilbert q) ∈ mixedSpace (Finset.Icc 2 (q * m)) := by
  rw [hilbertDilation_ramanujanPacket_divisors m q hm hq]
  apply Submodule.sum_mem
  intro d hd
  have hdv := (Finset.mem_filter.mp hd).1
  have hdpos := Nat.pos_of_mem_divisors hdv
  have hqd := hq.trans_le (Nat.le_mul_of_pos_right q hdpos)
  have hdle := Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hdv)
  exact Submodule.subset_span ⟨⟨q * d, Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, Nat.mul_le_mul_left q hdle⟩,
      fun hp => hmix (hp.dvd (dvd_mul_right q d) (by omega))⟩⟩, rfl⟩

/-- A single finite arithmetic correlation lower-bounds the energy gained
between B and an enlarged window that contains the dilated packet. -/
theorem dilated_packet_correlation_le_gain (B m q : ℕ) (hm : 0 < m)
    (hq : 1 < q) (hmix : ¬ IsPrimePow q) :
    (inner ℝ (hilbertDilation m hm (ramanujanPacketHilbert q))
      (finiteScreening B centeredParity)) ^ 2 ≤
      gain B (max B (q * m)) * ((m : ℝ) * ‖ramanujanPacketHilbert q‖ ^ 2) := by
  have hsub : Finset.Icc 2 (q * m) ⊆ Finset.Icc 2 (max B (q * m)) := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (le_max_right _ _)⟩
  have h := correlation_sq_le_gain_mul_norm_sq B (max B (q * m)) _
    (mixedSpace_mono hsub (dilated_mixed_packet_mem_window m q hm hq hmix))
  rwa [hilbertDilation_norm_sq] at h


/-- On h distinct nodes away from one, the first h shifted power moments
detect every nonzero coefficient vector. Adjacent moments give an ordinary
Vandermonde system with coefficients multiplied by x - 1. -/
theorem exists_shifted_power_moment {h : ℕ} (x c : Fin h → ℝ)
    (hx : Function.Injective x) (hx1 : ∀ i, x i ≠ 1) (hc : c ≠ 0) :
    ∃ j : Fin h, (∑ i, c i * (x i ^ (j.val + 1) - 1)) ≠ 0 := by
  by_contra! hall
  let S : ℕ → ℝ := fun k => ∑ i, c i * (x i ^ k - 1)
  have hS (k : ℕ) (hk : k ≤ h) : S k = 0 := by
    cases k with
    | zero => simp [S]
    | succ k => exact hall ⟨k, by omega⟩
  have hd : (fun i => c i * (x i - 1)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hx
    intro j
    calc
      _ = S (j.val + 1) - S j.val := by
        unfold S
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_succ]
        ring
      _ = 0 := by rw [hS _ (by omega), hS _ (by omega), sub_self]
  apply hc
  funext i
  have hi := congrFun hd i
  exact (mul_eq_zero.mp hi).resolve_right (sub_ne_zero.mpr (hx1 i))

/-- For the actual normalized residue basis, some odd Taylor coefficient of
the finite fit's period transform is detected by the indicated nonzero
shifted power moment. The normalization divides the raw residue by d. -/
theorem fixedTwoTrial_exists_residue_moment (B : ℕ) :
    ∃ c : Fin (B + 1) → ℝ,
      fixedTwoTrial B = ∑ i, c i • residueAtom i.val ∧
      ∃ j : Fin (B + 1), (∑ i, (c i / (i.val + 2 : ℝ)) *
        (((i.val + 2 : ℝ) ^ 2) ^ (j.val + 1) - 1)) ≠ 0 := by
  obtain ⟨c, he⟩ := finiteSpace_expansion _ _ (fixedTwoTrial_mem_finiteSpace B)
  refine ⟨c, he, exists_shifted_power_moment _ _ ?_ ?_ ?_⟩
  · intro i j hij
    apply Fin.ext
    have hi : 0 ≤ (i.val : ℝ) + 2 := by positivity
    have hj : 0 ≤ (j.val : ℝ) + 2 := by positivity
    have heq := (sq_eq_sq₀ hi hj).mp hij
    exact_mod_cast (show (i.val : ℝ) = (j.val : ℝ) by linarith)
  · intro i
    have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    nlinarith
  · intro hz
    have hc (i : Fin (B + 1)) : c i = 0 := by
      have hi := congrFun hz i
      exact (div_eq_zero_iff.mp hi).resolve_right (by positivity)
    have ht : fixedTwoTrial B = 0 := by simpa [hc] using he
    have hm : inner ℝ (fixedTwoTrial B) hilbertOne = 1 := by
      rw [fixedTwoTrial, real_inner_smul_left, screenedPacket_inner_one,
        ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num only [Nat.cast_ofNat]
      exact inv_mul_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    simpa [ht] using hm


/-- Inside any finite mixed window, testing the old centered residual is the
same as testing the old mean-one fit and multiplying by log 2. -/
theorem finite_mixed_test_pairing (B N : ℕ) (y : ThresholdHilbert)
    (hy : y ∈ mixedSpace (Finset.Icc 2 N)) :
    inner ℝ y (finiteScreening B centeredParity) =
      Real.log 2 * inner ℝ y (fixedTwoTrial B) := by
  have ho := ((mixedSpace (Finset.Icc 2 N)).mem_orthogonal hilbertOne).mp
    (one_mem_mixed_orthogonal _) y hy
  rw [finiteScreening_apply, project_centeredParity, centeredParity,
    fixedTwoTrial, screenedPacket]
  simp only [inner_sub_right, real_inner_smul_right, ho, mul_zero, sub_zero]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

/-- A divergent series of tested fractions on successive blocks kills the
ambient boundary. Overlap among conductors inside one block is allowed. -/
theorem boundary_eq_zero_of_block_correlation_shares (B : ℕ → ℕ)
    (hB : ∀ k, B k ≤ B (k + 1)) (y : ℕ → ThresholdHilbert)
    (hy : ∀ k, y k ∈ mixedSpace (Finset.Icc 2 (B (k + 1))))
    (hs : ¬ Summable (fun k => correlationShare (B k) (y k))) : boundary = 0 := by
  let g (k : ℕ) := gain (B k) (B (k + 1)) / deficit (B k)
  have hstep (k : ℕ) := deficit_step (hB k)
  have hnn (k : ℕ) : 0 ≤ g k := div_nonneg (sq_nonneg _) (deficit_pos _).le
  have hlt (k : ℕ) : g k < 1 := by
    apply (div_lt_one (deficit_pos _)).mpr
    linarith only [hstep k, deficit_pos (B (k + 1))]
  have hrec (k : ℕ) : deficit (B (k + 1)) = deficit (B k) * (1 - g k) := by
    dsimp [g]
    field_simp [(deficit_pos (B k)).ne']
    nlinarith [hstep k]
  have hcomp (k : ℕ) : correlationShare (B k) (y k) ≤ g k := by
    apply div_le_div_of_nonneg_right _ (deficit_pos _).le
    by_cases hz : y k = 0
    · simp [hz, gain]
    · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hz))).mpr
        (correlation_sq_le_gain_mul_norm_sq (B k) (B (k + 1)) _ (hy k))
  have hg : ¬ Summable g := fun h => hs (Summable.of_nonneg_of_le
    (fun k => div_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (deficit_pos _).le)
    hcomp h)
  have hlim : Tendsto (fun k => deficit (B k)) atTop (𝓝 0) :=
    (Analysis.ResidualGain.residual_tendsto_zero_iff_not_summable
      (deficit_pos (B 0)) hnn hlt hrec).mpr hg
  have hfloor : ‖boundary‖ ^ 2 * (Real.log 2) ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
      (fun k => (boundary_energy_lt_deficit (B k)).le)
  by_contra h
  exact (not_lt_of_ge hfloor) (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr h)) (by positivity))

/-- Arithmetic block criterion using successive dilations of one fixed mixed
packet. All numerator and denominator terms refer to the original Pareto norm. -/
theorem riemannHypothesis_of_dilated_packet_block_shares (q : ℕ) (hq : 1 < q)
    (hmix : ¬ IsPrimePow q) (B m : ℕ → ℕ) (hm : ∀ k, 0 < m k)
    (hB : ∀ k, B k ≤ B (k + 1)) (hcut : ∀ k, q * m k ≤ B (k + 1))
    (hs : ¬ Summable (fun k => correlationShare (B k)
      (hilbertDilation (m k) (hm k) (ramanujanPacketHilbert q)))) : RiemannHypothesis := by
  apply riemannHypothesis_of_boundary_eq_zero
  apply boundary_eq_zero_of_block_correlation_shares B hB _ _ hs
  intro k
  have hsub : Finset.Icc 2 (q * m k) ⊆ Finset.Icc 2 (B (k + 1)) := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
      (Finset.mem_Icc.mp hd).2.trans (hcut k)⟩
  exact mixedSpace_mono hsub (dilated_mixed_packet_mem_window (m k) q (hm k) hq hmix)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
