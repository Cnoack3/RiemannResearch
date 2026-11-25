import RiemannResearch.RH.DyadicParityGramCapacity
import RiemannResearch.RH.ParetoConductor241Covariance
import RiemannResearch.RH.TailCapacityDilationCorrection

/-! # Constructive centered parity capacity at arbitrarily large cutoffs

Truncate the positive dilation series for centered parity and apply the
resulting finite operator to the actual conductor-241 fit of the unit.
The support, full Hilbert error, and uncaptured source norm are explicit.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization RiemannResearch.Analysis.ExhaustiveWalk

private def a (n : ℕ) : ℝ := (n:ℝ)/(2*(n:ℝ)+1)
private def jump (j : ℕ) : ℝ := a (j+3)-a (j+2)

private theorem jump_eq (j : ℕ) :
    jump j = 1/((2*(j:ℝ)+5)*(2*(j:ℝ)+7)) := by
  dsimp [jump,a]; push_cast
  field_simp <;> ring

private theorem jump_nonneg (j : ℕ) : 0 ≤ jump j := by rw [jump_eq]; positivity

private theorem a_le_half (n : ℕ) : a n ≤ 1/2 := by
  unfold a
  apply (div_le_iff₀ (by positivity)).mpr; linarith

private theorem a_mono : Monotone a := by
  intro m n h
  unfold a
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [show (m:ℝ) ≤ (n:ℝ) by exact_mod_cast h]

private theorem jump_block (q M : ℕ) :
    ∑ j ∈ Finset.range M, jump (q+j) = a (q+M+2)-a (q+2) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ,ih,jump]
    rw [show q+(M+1)+2 = q+M+3 by omega]
    ring

/-- Only conductors m ≥ 3 occur in the proper dilation part. -/
def centeredParityTransfer (M : ℕ) (u : ThresholdHilbert) : ThresholdHilbert :=
  (2/5:ℝ) • u +
    ∑ j ∈ Finset.range M, jump j • unscaledResidueDilation (j+3) (by omega) u

theorem centeredParityTransfer_mem (M k : ℕ) {u : ThresholdHilbert} (hu : u ∈ finiteSpace k) :
    centeredParityTransfer M u ∈ finiteSpace ((M+2)*(k+1)-1) := by
  unfold centeredParityTransfer
  apply Submodule.add_mem
  · apply Submodule.smul_mem
    apply walkSpan_mono residueAtom id _ hu
    have hh := Nat.mul_le_mul_right (k+1) (show 1 ≤ M+2 by omega)
    simp only [one_mul] at hh
    omega
  · apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    have h := Nat.mul_le_mul_right (k+1) (show j+3 ≤ M+2 by have := Finset.mem_range.mp hj; omega)
    exact walkSpan_mono residueAtom id (by omega : (j+3)*(k+1)-1 ≤ (M+2)*(k+1)-1)
      (unscaledResidueDilation_mem_finiteSpace k (j+3) (by omega) u hu)

private theorem transfer_sub (M : ℕ) (u v : ThresholdHilbert) :
    centeredParityTransfer M (u-v) = centeredParityTransfer M u-centeredParityTransfer M v := by
  simp only [centeredParityTransfer,map_sub,smul_sub,Finset.sum_sub_distrib]
  abel

private theorem transfer_succ (M : ℕ) (u : ThresholdHilbert) :
    centeredParityTransfer (M+1) u = centeredParityTransfer M u +
      jump M • unscaledResidueDilation (M+3) (by omega) u := by
  simp only [centeredParityTransfer,Finset.sum_range_succ,add_assoc]

private theorem transfer_one_coordinate (M k : ℕ) (hk : 0 < k) :
    hilbertSequence (centeredParityTransfer M hilbertOne) k = a (min (max k 2) (M+2)) := by
  induction M with
  | zero =>
    rw [centeredParityTransfer,Finset.range_zero,Finset.sum_empty,add_zero,hilbertSequence_smul,
      hilbertOne_sequence,min_eq_right (le_max_right k 2)]
    norm_num [a,zeroAnchor,hk.ne']
  | succ M ih =>
    rw [transfer_succ,hilbertSequence_add]
    change hilbertSequence (centeredParityTransfer M hilbertOne) k +
      hilbertSequence (jump M • unscaledResidueDilation (M+3) (by omega) hilbertOne) k = _
    rw [ih,hilbertSequence_smul]
    change a (min (max k 2) (M+2)) + jump M*hilbertSequence (unscaledResidueDilation (M+3) _ hilbertOne) k = _
    rw [unscaledResidueDilation_sequence,hilbertOne_sequence]
    by_cases h : M+3 ≤ k
    · have hpos := Nat.div_pos h (by omega : 0 < M+3)
      rw [max_eq_left (by omega),min_eq_right (by omega),min_eq_right (by omega)]
      simp only [zeroAnchor,if_neg hpos.ne',mul_one,jump]
      ring
    · have hmax : max k 2 ≤ M+2 := max_le (by omega) (by omega)
      rw [min_eq_left hmax,min_eq_left (by omega),Nat.div_eq_of_lt (by omega)]
      simp [zeroAnchor]

private theorem source_coordinate (k : ℕ) (hk : 0 < k) :
    hilbertSequence centeredParitySource k = a (max k 2) := by
  rw [centeredParitySource,hilbertSequence_add]
  change hilbertSequence parityAdjointPacket k +
    hilbertSequence ((1/15:ℝ) • paretoPointHilbert 0) k = _
  rw [parityAdjointPacket_coordinate,hilbertSequence_smul,hilbertSequence_paretoPoint]
  by_cases h : k = 1
  · subst k; norm_num [a,paretoPointSequence]
  · rw [max_eq_left (by omega : 2 ≤ k)]
    simp [a,paretoPointSequence,h]

/-- The clipped source agrees through M+2, then its error is dominated by
one explicit Pareto tail. -/
theorem centeredParityTransfer_truncation (M : ℕ) :
    ‖centeredParitySource-centeredParityTransfer M hilbertOne‖ ≤
      1/(2*(2*((M+2:ℕ):ℝ)+1)*Real.sqrt ((M+3:ℕ):ℝ)) := by
  let c : ℝ := 1/(2*(2*((M+2:ℕ):ℝ)+1))
  let x := centeredParitySource-centeredParityTransfer M hilbertOne
  let y := c • hilbertTail (M+3) (by omega)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcoord (k : ℕ) : (hilbertSequence x k)^2 ≤ (hilbertSequence y k)^2 := by
    rcases Nat.eq_zero_or_pos k with hk|hk
    · subst k; simp only [hilbertSequence_zero,le_refl]
    dsimp only [x,y]
    rw [hilbertSequence_sub,hilbertSequence_smul,hilbertTail_sequence]
    change (hilbertSequence centeredParitySource k-hilbertSequence (centeredParityTransfer M hilbertOne) k)^2 ≤
      (c*(if M+3 ≤ k then 1 else 0))^2
    rw [source_coordinate k hk,transfer_one_coordinate M k hk]
    by_cases h : M+3 ≤ k
    · rw [max_eq_left (by omega),min_eq_right (by omega),if_pos h,mul_one]
      apply (sq_le_sq₀ (sub_nonneg.mpr (a_mono (by omega))) hc).mpr
      have he : c = 1/2-a (M+2) := by
        dsimp only [c,a]
        field_simp [show 2*((M+2:ℕ):ℝ)+1 ≠ 0 by positivity] <;> ring
      rw [he]; exact sub_le_sub_right (a_le_half k) _
    · rw [min_eq_left (max_le (by omega) (by omega)),if_neg h,mul_zero,sub_self]
  have hsq : ‖x‖^2 ≤ ‖y‖^2 := by
    rw [hilbert_norm_weighted_sq,hilbert_norm_weighted_sq]
    exact Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hcoord k) (positiveWeight_nonneg k))
      (hilbertSequence_square_summable x) (hilbertSequence_square_summable y)
  have h := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hone : ‖hilbertOne‖ = 1 := by nlinarith [hilbertOne_norm_sq,norm_nonneg hilbertOne]
  change ‖x‖ ≤ ‖c • unscaledResidueDilation (M+3) (by omega) hilbertOne‖ at h
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,unscaledResidueDilation_norm,hone,mul_one] at h
  apply h.trans_eq
  dsimp only [c]; simp only [one_div,mul_inv_rev]; ring

private def gain (j : ℕ) : ℝ := jump j*(1/Real.sqrt ((j+3:ℕ):ℝ))

private theorem gain_nonneg (j : ℕ) : 0 ≤ gain j :=
  mul_nonneg (jump_nonneg j) (by positivity)

private theorem gain_le (j : ℕ) (c : ℝ) (h : 1 ≤ c*Real.sqrt ((j+3:ℕ):ℝ)) :
    gain j ≤ jump j*c := by
  apply mul_le_mul_of_nonneg_left _ (jump_nonneg j)
  exact (div_le_iff₀ (Real.sqrt_pos.mpr (by positivity))).mpr h

private theorem gain_sum_bound (M : ℕ) :
    2/5 + ∑ j ∈ Finset.range M, gain j ≤ (56/125:ℝ) := by
  have h3 : gain 0 ≤ jump 0*(7/12) := by
    apply gain_le
    have h : (12/7:ℝ) ≤ Real.sqrt 3 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    norm_num only [Nat.zero_add,Nat.cast_ofNat]
    linarith only [h]
  have h4 (j : ℕ) : gain (1+j) ≤ jump (1+j)*(1/2) := by
    apply gain_le
    have h := Real.sqrt_le_sqrt (show (4:ℝ) ≤ ((1+j+3:ℕ):ℝ) by exact_mod_cast (show 4 ≤ 1+j+3 by omega))
    rw [show Real.sqrt 4 = 2 by norm_num] at h
    linarith only [h]
  have h9 (j : ℕ) : gain (6+j) ≤ jump (6+j)*(1/3) := by
    apply gain_le
    have h := Real.sqrt_le_sqrt (show (9:ℝ) ≤ ((6+j+3:ℕ):ℝ) by exact_mod_cast (show 9 ≤ 6+j+3 by omega))
    rw [show Real.sqrt 9 = 3 by norm_num] at h
    linarith only [h]
  have hsmall : ∑ j ∈ Finset.range 5, gain (1+j) ≤ (a 8-a 3)*(1/2) := by
    apply (Finset.sum_le_sum (fun j _ => h4 j)).trans_eq
    rw [← Finset.sum_mul,jump_block]
  have hbig : ∑ j ∈ Finset.range M, gain (6+j) ≤ (1/2-a 8)*(1/3) := by
    apply (Finset.sum_le_sum (fun j _ => h9 j)).trans
    rw [← Finset.sum_mul,jump_block]
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right (a_le_half _) _) (by norm_num)
  have hsub : ∑ j ∈ Finset.range M, gain j ≤ ∑ j ∈ Finset.range (6+M), gain j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun j _ _ => gain_nonneg j)
  have hsplit : ∑ j ∈ Finset.range (6+M), gain j =
      (∑ j ∈ Finset.range 6, gain j) + ∑ j ∈ Finset.range M, gain (6+j) :=
    Finset.sum_range_add gain 6 M
  have hsix : ∑ j ∈ Finset.range 6, gain j = gain 0 + ∑ j ∈ Finset.range 5, gain (1+j) := by
    rw [show (6:ℕ) = 1+5 by decide, Finset.sum_range_add,Finset.sum_range_one]
  rw [hsplit,hsix] at hsub
  norm_num [a,jump] at h3 hsmall hbig
  linarith only [h3,hsmall,hbig,hsub]

theorem centeredParityTransfer_norm_bound (M : ℕ) (u : ThresholdHilbert) :
    ‖centeredParityTransfer M u‖ ≤ (56/125:ℝ)*‖u‖ := by
  let f (j : ℕ) := jump j • unscaledResidueDilation (j+3) (by omega) u
  have hf (j : ℕ) : ‖f j‖ = gain j*‖u‖ := by
    dsimp only [f]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (jump_nonneg j),unscaledResidueDilation_norm,gain]
    ring
  change ‖(2/5:ℝ) • u + ∑ j ∈ Finset.range M, f j‖ ≤ _
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2/5)]
  calc
    _ ≤ (2/5)*‖u‖ + ∑ j ∈ Finset.range M, ‖f j‖ := add_le_add le_rfl (norm_sum_le _ _)
    _ = (2/5 + ∑ j ∈ Finset.range M, gain j)*‖u‖ := by simp only [hf,add_mul,Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (gain_sum_bound M) (norm_nonneg u)

/-- Dilating any physical fit gives a legal trial with an explicit full
error. The estimate holds beyond its support cutoff. -/
theorem centeredParityGram_error_le_transfer (M k n : ℕ) (hn : (M+2)*(k+1)-1 ≤ n) :
    2*Real.log 2-Real.pi^2/8+11/450-centeredParityGramCapacity n ≤
      (1/(2*(2*((M+2:ℕ):ℝ)+1)*Real.sqrt ((M+3:ℕ):ℝ))+
        (56/125:ℝ)*Real.sqrt (energy k))^2 := by
  let x := centeredParityTransfer M (projection k)
  let w := centeredParityTransfer M hilbertOne
  have hx : x ∈ finiteSpace n := walkSpan_mono residueAtom id hn
    (centeredParityTransfer_mem M k ((finiteSpace k).starProjection_apply_mem hilbertOne))
  have he : ‖hilbertOne-projection k‖ = Real.sqrt (energy k) := by
    change ‖hilbertOne-projection k‖ = Real.sqrt (‖hilbertOne-projection k‖^2)
    rw [Real.sqrt_sq (norm_nonneg _)]
  have hnear := Metric.infDist_le_dist_of_mem (x := centeredParitySource) hx
  rw [(finiteSpace n).infDist_eq_norm_sub_starProjection,dist_eq_norm] at hnear
  have htriangle := dist_triangle centeredParitySource w x
  simp only [dist_eq_norm] at htriangle
  have hdiff : ‖w-x‖ ≤ (56/125:ℝ)*Real.sqrt (energy k) := by
    dsimp only [w,x]; rw [← transfer_sub,← he]
    exact centeredParityTransfer_norm_bound M _
  rw [← centeredParityGram_error]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
  exact hnear.trans (htriangle.trans (add_le_add (centeredParityTransfer_truncation M) hdiff))

open Filter
open scoped Topology

private theorem truncation_le_reciprocal (k : ℕ) : 1/(2*(2*((k+2:ℕ):ℝ)+1)*Real.sqrt ((k+3:ℕ):ℝ)) ≤ 1/((k:ℝ)+1) := by
  apply one_div_le_one_div_of_le (by positivity)
  have h₁ : (1:ℝ) ≤ Real.sqrt ((k+3:ℕ):ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    push_cast; linarith [Nat.cast_nonneg (α:=ℝ) k]
  calc
    _ ≤ 2*(2*((k+2:ℕ):ℝ)+1)*1 := by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) k]
    _ ≤ _ := mul_le_mul_of_nonneg_left h₁ (by positivity)

/-- The signed residual observation is centered at two fifths of the unit
energy with a uniform error of at most six one-hundred-twenty-fifths. -/
theorem centeredParity_residual_signed_bound :
    |inner ℝ limitResidual centeredParitySource-(2/5:ℝ)*limitEnergy| ≤
      (6/125:ℝ)*limitEnergy := by
  have ht : Tendsto (fun M => centeredParityTransfer M hilbertOne) atTop (𝓝 centeredParitySource) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun M => norm_nonneg _) ?_ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
    intro M
    rw [norm_sub_rev]
    exact (centeredParityTransfer_truncation M).trans (truncation_le_reciprocal M)
  have hz := (((innerSL ℝ limitResidual).continuous.tendsto _).comp ht).sub_const ((2/5:ℝ)*limitEnergy)
  refine le_of_tendsto hz.abs (Eventually.of_forall ?_)
  intro M
  change |inner ℝ limitResidual (centeredParityTransfer M hilbertOne) - (2/5:ℝ)*limitEnergy| ≤ _
  rw [centeredParityTransfer,inner_add_right,real_inner_smul_right,limitResidual_inner_one,inner_sum]
  simp only [real_inner_smul_right,add_sub_cancel_left]
  calc
    _ ≤ ∑ j ∈ Finset.range M, |jump j*inner ℝ limitResidual (unscaledResidueDilation (j+3) _ hilbertOne)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range M, gain j*limitEnergy := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_of_nonneg (jump_nonneg j),gain]
      calc
        _ ≤ jump j * (limitEnergy / Real.sqrt ((j+3:ℕ):ℝ)) :=
          mul_le_mul_of_nonneg_left (abs_residual_inner_tail_le_div_sqrt (j+3) (by omega)) (jump_nonneg j)
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (by linarith only [gain_sum_bound M]) (sq_nonneg _)

/-- Every finite capacity controls the unit defect with coefficient 44/125
in distance, obtained by retaining the scales three through eight. -/
theorem centeredParity_uniform_lower (n : ℕ) :
    (44/125:ℝ)^2*limitEnergy ≤ 2*Real.log 2-Real.pi^2/8+11/450-centeredParityGramCapacity n := by
  let r := limitResidual
  let y := centeredParitySource
  let v := (finiteSpace n).starProjection y
  let R := inner ℝ r (y-v)
  have hv := Submodule.inner_right_of_mem_orthogonal
    (RamanujanMultipleCapacityLimits.finiteSpace_le_closedSpace n ((finiteSpace n).starProjection_apply_mem y))
    limitResidual_mem_orthogonal
  have hp : inner ℝ r v = 0 := (real_inner_comm ..).trans hv
  have hR : R = inner ℝ limitResidual centeredParitySource := by
    dsimp only [R]; rw [inner_sub_right,hp,sub_zero]
  have he : 0 ≤ limitEnergy := sq_nonneg _
  have hl : (44/125:ℝ)*limitEnergy ≤ R := by
    rw [hR]; linarith only [(abs_le.mp centeredParity_residual_signed_bound).1]
  have hcs := RiemannResearch.Analysis.CorrelationCorrection.inner_sq_le r (y-v)
  change R^2 ≤ limitEnergy*‖y-v‖^2 at hcs
  have hs := ((sq_le_sq₀ (mul_nonneg (by norm_num) he) ((mul_nonneg (by norm_num) he).trans hl)).mpr hl).trans hcs
  rw [← centeredParityGram_error]
  change (44/125:ℝ)^2*limitEnergy ≤ ‖y-v‖^2
  by_cases h : limitEnergy = 0
  · rw [h,mul_zero]; exact sq_nonneg _
  apply le_of_mul_le_mul_left _ (lt_of_le_of_ne he (Ne.symm h))
  calc
    _ = ((44/125:ℝ)*limitEnergy)^2 := by ring
    _ ≤ _ := hs

/-- The centered parity distance and the unit distance control one another
uniformly. The upper estimate follows from actual finite dilation trials. -/
theorem centeredParity_limit_error_comparison :
    (44/125:ℝ)^2*limitEnergy ≤
        ‖centeredParitySource-closedSpace.starProjection centeredParitySource‖^2 ∧
      ‖centeredParitySource-closedSpace.starProjection centeredParitySource‖^2 ≤
        (56/125:ℝ)^2*limitEnergy := by
  let y := centeredParitySource
  have ht := walkProjection_tendsto residueAtom id Function.surjective_id y
  change Tendsto (fun n => (finiteSpace n).starProjection y) atTop
    (𝓝 (closedSpace.starProjection y)) at ht
  have hz := ((tendsto_const_nhds (x:=y)).sub ht).norm.pow 2
  constructor
  · refine le_of_tendsto_of_tendsto tendsto_const_nhds hz (Eventually.of_forall ?_)
    intro n
    exact (centeredParity_uniform_lower n).trans_eq (centeredParityGram_error n).symm
  · have hu := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).add
        (energy_tendsto.sqrt.const_mul (56/125:ℝ))).pow 2
    have hE : 0 ≤ limitEnergy := sq_nonneg _
    rw [zero_add,mul_pow,Real.sq_sqrt hE] at hu
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hu (Eventually.of_forall ?_)
    intro k
    let n := (k+2)*(k+1)-1
    have hx := RamanujanMultipleCapacityLimits.finiteSpace_le_closedSpace n
      ((finiteSpace n).starProjection_apply_mem y)
    have hd := Metric.infDist_le_dist_of_mem (x:=y) hx
    rw [closedSpace.infDist_eq_norm_sub_starProjection,dist_eq_norm] at hd
    exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hd).trans
      ((centeredParityGram_error n).le.trans ((centeredParityGram_error_le_transfer k k n le_rfl).trans
        ((sq_le_sq₀ (by positivity) (by positivity)).mpr (add_le_add (truncation_le_reciprocal k) le_rfl))))

/-- At every cutoff past 61694 this explicit finite trial captures at least
99 percent of the centered source squared norm. -/
theorem centeredParityGramCapacity_ninety_nine_percent (n : ℕ) (hn : 61695 ≤ n) :
    (99/100:ℝ)*‖centeredParitySource‖^2 ≤ centeredParityGramCapacity n := by
  have h0 := centeredParityGram_error_le_transfer 254 240 n (by simpa using hn)
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at h0
  have he : energy 240 ≤ (8776/1000000:ℝ) :=
    GroupedResidueMass.Conductor241.energy_le_conductor_241_covariance.trans (by norm_num)
  have hs : Real.sqrt (energy 240) ≤ (937/10000:ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,he.trans (by norm_num)⟩
  have ht : 1/(2*(2*(256:ℝ)+1)*Real.sqrt 257) ≤ (1/16000:ℝ) := by
    have hp : (16:ℝ) ≤ Real.sqrt 257 :=
      (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hp]
  have hb : 1/(2*(2*(256:ℝ)+1)*Real.sqrt 257)+(56/125:ℝ)*Real.sqrt (energy 240)
      ≤ (4205/100000:ℝ) := by linarith only [hs,ht]
  have hsq := (sq_le_sq₀ (by positivity) (by norm_num)).mpr hb
  have hpi : Real.pi ≤ (31416/10000:ℝ) := by linarith only [Real.pi_lt_d20]
  have hpi2 := (sq_le_sq₀ Real.pi_pos.le (by norm_num)).mpr hpi
  have hN : (177/1000:ℝ) ≤ 2*Real.log 2-Real.pi^2/8+11/450 := by
    linarith only [hpi2,Real.log_two_gt_d9]
  rw [centeredParitySource_norm_sq]
  linarith only [h0,hsq,hN]

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
