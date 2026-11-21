import RiemannResearch.RH.MixedConductorHead
import RiemannResearch.RH.ParetoFiniteHeadRepair
import RiemannResearch.RH.CanonicalMobiusWeightedEndpoint

/-!
# Finite mixed heads for a centered legal vector

A fit to the constant on a fixed head yields a mixed fit to a centered
mean-one legal vector. A dilation supported beyond the head cancels the
mean of the error. The decreasing tail mass exactly offsets its dilation norm.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization FiniteHeadRepair

/-- A delayed mean correction takes a legal constant-head fit to a mixed
fit of the centered target, with uniform full-norm cost. -/
theorem mixed_centered_head_transfer (N : ℕ) (z u : ThresholdHilbert)
    (hz : z ∈ closedSpace) (hu : u ∈ closedSpace) (hm : inner ℝ z hilbertOne = 1)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence u k = hilbertSequence hilbertOne k) :
    ∃ x ∈ mixedClosure,
      (∀ k, 0 < k → k ≤ N → hilbertSequence x k = hilbertSequence (z-hilbertOne) k) ∧
      ‖(z-hilbertOne)-x‖ ≤ (1 + ‖z‖) * ‖u-hilbertOne‖ := by
  let e := u - hilbertOne
  let a : ℝ := inner ℝ e hilbertOne
  let d := hilbertDilation (N+1) (Nat.succ_pos N) z
  let x := z-u+a • d
  have ha : a = inner ℝ u hilbertOne - 1 := by
    change inner ℝ (u-hilbertOne) hilbertOne = _
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
  have hdmean : inner ℝ d hilbertOne = 1 := by
    dsimp only [d]
    rw [hilbert_inner_one, hilbertDilation_mean, ← hilbert_inner_one, hm]
  refine ⟨x,(mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr ⟨?_,?_⟩,?_,?_⟩
  · exact closedSpace.add_mem (closedSpace.sub_mem hz hu)
      (closedSpace.smul_mem a (closedSpace_dilation hz _ _))
  · change inner ℝ (z-u + a • d) hilbertOne = 0
    rw [inner_add_left, inner_sub_left, real_inner_smul_left, hm, hdmean, ha]
    ring
  · intro k hk hkN
    change hilbertSequence (z-u + a • d) k = _
    simp only [hilbertSequence_add, hilbertSequence_sub, hilbertSequence_smul,
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hhead k hk hkN, d,
      hilbertDilation_sequence, dilation, Nat.div_eq_of_lt (show k < N+1 by omega),
      hilbertSequence_zero, mul_zero, add_zero]
  · have hzero : paretoHeadMean N e = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      dsimp only [e]
      rw [hilbertGibbsPhysical_eq, hilbertSequence_sub, Pi.sub_apply,
        hhead _ (Nat.succ_pos _) (Finset.mem_range.mp hk), sub_self, mul_zero]
    have haTail : inner ℝ e (paretoTail N) = a := by
      rw [paretoTail_inner, hzero, sub_zero]
    have htail : ‖paretoTail N‖ * Real.sqrt ((N+1:ℕ):ℝ) = 1 := by
      apply (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) zero_le_one).mp
      rw [mul_pow, paretoTail_norm_sq, Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_add, Nat.cast_one]
      field_simp
    have hcorr : ‖a • d‖ ≤ ‖u-hilbertOne‖ * ‖z‖ := by
      dsimp only [d]
      rw [norm_smul, Real.norm_eq_abs, hilbertDilation_norm, ← haTail]
      calc
        _ ≤ (‖e‖ * ‖paretoTail N‖) * (Real.sqrt ((N+1:ℕ):ℝ) * ‖z‖) :=
          mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (by positivity)
        _ = ‖u-hilbertOne‖ * ‖z‖ := by
          calc
            _ = ‖e‖ * (‖paretoTail N‖ * Real.sqrt ((N+1:ℕ):ℝ)) * ‖z‖ := by ring
            _ = _ := by rw [htail, mul_one]
    have hx : (z-hilbertOne)-x = (u-hilbertOne)-a • d := by dsimp [x]; abel
    rw [hx]
    calc
      _ ≤ ‖u-hilbertOne‖ + ‖a • d‖ := norm_sub_le _ _
      _ ≤ ‖u-hilbertOne‖ + ‖u-hilbertOne‖ * ‖z‖ := add_le_add le_rfl hcorr
      _ = _ := by ring

private abbrev mixedStage (M : ℕ) := mixedSpace (Finset.Icc 2 M)
private abbrev mixedUnion := ⨆ M : ℕ, mixedStage M

private theorem mixedStage_mono : Monotone mixedStage :=
  fun _ _ h => mixedSpace_mono (Finset.Icc_subset_Icc le_rfl h)

/-- A fixed physical head is preserved by finite mixed vectors approaching
any element of the mixed closure in the full norm. -/
theorem finite_mixed_approximate_fixed_head (N : ℕ) (x : ThresholdHilbert)
    (hx : x ∈ mixedClosure) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∃ v ∈ mixedSpace (Finset.Icc 2 M),
      (∀ k, 0 < k → k ≤ N → hilbertSequence v k = hilbertSequence x k) ∧ ‖v-x‖ < ε := by
  classical
  have hex (i : Fin N) : ∃ f ∈ mixedUnion, ∀ j : Fin N,
      headMap N f j = if j = i then 1 else 0 := by
    obtain ⟨M,f,hf,hh⟩ := exists_mixed_exact_head
      (fun k => if k = (i:ℕ)+1 then 1 else 0) N
    refine ⟨f, (le_iSup mixedStage M) hf, ?_⟩
    intro j
    rw [headMap_apply, hh _ (Nat.succ_pos _) (by omega)]
    by_cases he : j = i
    · subst j
      simp
    · have hv : (j : ℕ) ≠ (i : ℕ) := fun h => he (Fin.ext h)
      simp [he, hv]
  choose basis hmem hcoord using hex
  let R : (Fin N → ℝ) →L[ℝ] ThresholdHilbert :=
    (Fintype.linearCombination ℝ basis).toContinuousLinearMap
  have happ (b : Fin N → ℝ) : R b = ∑ i : Fin N, b i • basis i := by
    change Fintype.linearCombination ℝ basis b = _
    rw [Fintype.linearCombination_apply]
  have hr : Function.RightInverse R (headMap N) := by
    intro b
    ext j
    rw [happ, map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, hcoord]
    simp
  have hS (b : Fin N → ℝ) : R b ∈ mixedUnion := by
    rw [happ]
    exact mixedUnion.sum_mem fun i _ => mixedUnion.smul_mem _ (hmem i)
  obtain ⟨u, hu, ht⟩ := RiemannResearch.Analysis.FiniteConstraintClosure.exists_exact_approximants
    mixedUnion (headMap N) R hr hS (headMap N x) x hx rfl
  obtain ⟨i, hi⟩ := ((Metric.tendsto_nhds.mp ht) ε hε).exists
  obtain ⟨M, hM⟩ := (Submodule.mem_iSup_of_directed mixedStage
    mixedStage_mono.directed_le).mp (hu i).1
  refine ⟨M, u i, hM, ?_, by simpa [dist_eq_norm] using hi⟩
  intro k hk hkN
  have h := congrFun (hu i).2 (⟨k - 1, by omega⟩ : Fin N)
  simpa only [headMap_apply, Nat.sub_add_cancel hk] using h

/-- Finite mixed heads for a centered legal mean-one target. The choice of
finite mixed support can absorb any positive extra norm budget. -/
theorem finite_mixed_centered_head_transfer (N : ℕ) (z u : ThresholdHilbert)
    (hz : z ∈ closedSpace) (hu : u ∈ closedSpace) (hm : inner ℝ z hilbertOne = 1)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence u k = hilbertSequence hilbertOne k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∃ v ∈ mixedSpace (Finset.Icc 2 M),
      (∀ k, 0 < k → k ≤ N → hilbertSequence v k = hilbertSequence (z-hilbertOne) k) ∧
      ‖(z-hilbertOne)-v‖ < (1 + ‖z‖) * ‖u-hilbertOne‖ + ε := by
  obtain ⟨x,hx,hcoord,hcost⟩ := mixed_centered_head_transfer N z u hz hu hm hhead
  obtain ⟨M,v,hv,hmatch,hnear⟩ := finite_mixed_approximate_fixed_head N x hx ε hε
  refine ⟨M,v,hv,fun k hk hkN => (hmatch k hk hkN).trans (hcoord k hk hkN), ?_⟩
  have htri := dist_triangle (z-hilbertOne) x v
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev x v] at htri
  exact htri.trans_lt (add_lt_add_of_le_of_lt hcost hnear)

/-- The PDF target admits finite mixed fits on every head with sublinear
complete squared error. -/
theorem pdf_centered_parity_finite_mixed_sublinear :
    let z := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2
    ∃ M : ℕ → ℕ, ∃ v : ℕ → ThresholdHilbert,
      (∀ N, v N ∈ mixedSpace (Finset.Icc 2 (M N)) ∧
        ∀ k, 0 < k → k ≤ N → hilbertSequence (v N) k = hilbertSequence (z-hilbertOne) k) ∧
      Tendsto (fun N => ‖(z-hilbertOne)-v N‖^2 / (N:ℝ)) atTop (𝓝 0) := by
  let z := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2
  have hz : z ∈ closedSpace := closedSpace.smul_mem _ (packet_mem_closedSpace 2 (by decide))
  have hm : inner ℝ z hilbertOne = 1 := by
    dsimp only [z]
    rw [real_inner_smul_left, hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
      paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact inv_mul_cancel₀ (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
  have h (N : ℕ) := finite_mixed_centered_head_transfer N z (canonicalMobiusHilbert N) hz
    (canonicalMobiusHilbert_mem_closedSpace N) hm (by
      intro k hk hkN
      rw [canonicalMobiusHilbert_exact N k hk hkN, hilbertOne_sequence]
      simp [zeroAnchor, hk.ne']) 1 zero_lt_one
  choose M v hM hh hE using h
  refine ⟨M,v,fun N => ⟨hM N,hh N⟩,?_⟩
  let b := 1 + ‖z‖
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hs (N : ℕ) : ‖(z-hilbertOne)-v N‖^2 ≤
      2*b^2*‖hilbertOne-canonicalMobiusHilbert N‖^2+2 := by
    have he := (hE N).le
    rw [norm_sub_rev (canonicalMobiusHilbert N) hilbertOne] at he
    have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (mul_nonneg hb (norm_nonneg _)) zero_le_one)).mpr he
    nlinarith only [hsq,sq_nonneg (b*‖hilbertOne-canonicalMobiusHilbert N‖-1)]
  have hlim : Tendsto (fun N : ℕ => (2*b^2)*(‖hilbertOne-canonicalMobiusHilbert N‖^2/(N:ℝ))
      + 2*(1/(N:ℝ))) atTop (𝓝 0) := by
    simpa using (canonicalMobiusResidual_sublinear.const_mul (2*b^2)).add
      ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul 2)
  apply squeeze_zero (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg N)) _ hlim
  intro N
  calc
    _ ≤ (2*b^2*‖hilbertOne-canonicalMobiusHilbert N‖^2+2)/(N:ℝ) :=
      div_le_div_of_nonneg_right (hs N) (Nat.cast_nonneg N)
    _ = _ := by ring

end RiemannResearch.RH.Pareto.PrimePowerSchur
