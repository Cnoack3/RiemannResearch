import RiemannResearch.RH.LegalTailMeanCapacityMellin
import RiemannResearch.RH.ThresholdHilbertProjection
import RiemannResearch.RH.CenteredMeanSquarefreeConverse
import RiemannResearch.RH.MixedConductorBilinear
import RiemannResearch.RH.MeanOneResidualFloor
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Dilation gains and limits of normalized legal tail capacity

Source: the user's divisor comparison. The scaled old projection represents
the mean on the entire dilated legal kernel. The orthogonal remainder gives
the gain and compares two predecessor stages at any common multiple.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization FiniteHeadRepair
open RiemannResearch.Analysis.SingleObservationProjection

def normalizedLegalTailMeanCapacity (K : ℕ) : ℝ :=
  ((K : ℝ) + 1) * legalTailMeanCapacity K

def legalTailMeanVector (K : ℕ) : ThresholdHilbert :=
  (legalHeadKernel K).starProjection (paretoTail K)

theorem legalTailMeanVector_mem (K : ℕ) : legalTailMeanVector K ∈ legalHeadKernel K :=
  (legalHeadKernel K).starProjection_apply_mem _

theorem legalTailMeanVector_pairing {K : ℕ} {x : ThresholdHilbert}
    (hx : x ∈ legalHeadKernel K) : inner ℝ (legalTailMeanVector K) x = inner ℝ hilbertOne x :=
  (projection_pairing _ _ _ hx).symm.trans (tail_eq_mean_of_head_zero hx.2)

theorem legalHeadKernel_dilation {K L m : ℕ} (hm : 0 < m) (hL : L + 1 = m * (K + 1))
    {x : ThresholdHilbert} (hx : x ∈ legalHeadKernel K) :
    hilbertDilation m hm x ∈ legalHeadKernel L := by
  refine ⟨closedSpace_dilation hx.1 m hm, ?_⟩
  change headMap L (hilbertDilation m hm x) = 0
  ext i
  rw [headMap_apply, hilbertDilation_sequence]
  change (m : ℝ) * hilbertSequence x ((i.val + 1) / m) = 0
  have hi : (i.val + 1) / m < K + 1 := (Nat.div_lt_iff_lt_mul hm).2 (by
    rw [Nat.mul_comm, ← hL]
    omega)
  cases hv : (i.val + 1) / m with
  | zero => simp [hilbertSequence_zero]
  | succ j =>
    have hj : j < K := by omega
    have hz := congrFun (show headMap K x = 0 from hx.2) (⟨j, hj⟩ : Fin K)
    have hz' : hilbertSequence x (j + 1) = 0 := by
      simpa only [headMap_apply, Pi.zero_apply] using hz
    rw [hz', mul_zero]

/-- Riesz representative of the tail mean on the transported legal subspace. -/
def dilatedLegalTailMeanVector (K m : ℕ) (hm : 0 < m) : ThresholdHilbert :=
  (m : ℝ)⁻¹ • hilbertDilation m hm (legalTailMeanVector K)

theorem legalTailMean_dilation_orthogonal {K L m : ℕ} (hm : 0 < m)
    (hL : L + 1 = m * (K + 1)) {x : ThresholdHilbert} (hx : x ∈ legalHeadKernel K) :
    inner ℝ (legalTailMeanVector L - dilatedLegalTailMeanVector K m hm)
      (hilbertDilation m hm x) = 0 := by
  have hmean : inner ℝ hilbertOne (hilbertDilation m hm x) = inner ℝ hilbertOne x := by
    conv_lhs => rw [real_inner_comm]
    conv_rhs => rw [real_inner_comm]
    simp only [hilbert_inner_one, hilbertDilation_mean]
  rw [inner_sub_left, legalTailMeanVector_pairing (legalHeadKernel_dilation hm hL hx),
    dilatedLegalTailMeanVector, real_inner_smul_left, hilbertDilation_inner,
    legalTailMeanVector_pairing hx, hmean]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Exact increment, including the case of a zero innovation. -/
theorem normalizedLegalTailMeanCapacity_gain {K L m : ℕ} (hm : 0 < m)
    (hL : L + 1 = m * (K + 1)) :
    normalizedLegalTailMeanCapacity L - normalizedLegalTailMeanCapacity K =
      ((L : ℝ) + 1) * ‖legalTailMeanVector L - dilatedLegalTailMeanVector K m hm‖ ^ 2 := by
  let a := legalTailMeanVector L
  let b := dilatedLegalTailMeanVector K m hm
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have ho : inner ℝ (a - b) b = 0 := by
    change inner ℝ (a - b) ((m : ℝ)⁻¹ • hilbertDilation m hm (legalTailMeanVector K)) = 0
    rw [real_inner_smul_right, legalTailMean_dilation_orthogonal hm hL (legalTailMeanVector_mem K),
      mul_zero]
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  have hb : ‖b‖ ^ 2 = legalTailMeanCapacity K / m := by
    dsimp only [b, dilatedLegalTailMeanVector]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hilbertDilation_norm_sq]
    change _ = ‖legalTailMeanVector K‖ ^ 2 / (m : ℝ)
    field_simp
  have hdiff : ‖a - b‖ ^ 2 = legalTailMeanCapacity L - legalTailMeanCapacity K / m := by
    rw [norm_sub_sq_real, sub_eq_zero.mp ho, hb]
    change _ = ‖a‖ ^ 2 - _
    ring
  have hcast : (L : ℝ) + 1 = (m : ℝ) * ((K : ℝ) + 1) := by exact_mod_cast hL
  change _ = ((L : ℝ) + 1) * ‖a - b‖ ^ 2
  rw [hdiff, normalizedLegalTailMeanCapacity, normalizedLegalTailMeanCapacity, hcast]
  field_simp

theorem normalizedLegalTailMeanCapacity_mono_of_dvd {K L : ℕ} (h : K + 1 ∣ L + 1) :
    normalizedLegalTailMeanCapacity K ≤ normalizedLegalTailMeanCapacity L := by
  obtain ⟨m, hm⟩ := h
  have hmpos : 0 < m := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hm
  have hL : L + 1 = m * (K + 1) := hm.trans (Nat.mul_comm _ _)
  exact sub_nonneg.mp ((normalizedLegalTailMeanCapacity_gain hmpos hL).symm ▸
    (mul_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) + 1) (sq_nonneg _)))

/-- A legal test vector detects gain by its mismatch with the transported mean. -/
theorem legalTailMean_gain_test {K L m : ℕ} (hm : 0 < m) (hL : L + 1 = m * (K + 1))
    {y : ThresholdHilbert} (hy : y ∈ legalHeadKernel L) :
    ((L : ℝ) + 1) * (inner ℝ hilbertOne y - inner ℝ (dilatedLegalTailMeanVector K m hm) y) ^ 2 ≤
      (normalizedLegalTailMeanCapacity L - normalizedLegalTailMeanCapacity K) * ‖y‖ ^ 2 := by
  let d := legalTailMeanVector L - dilatedLegalTailMeanVector K m hm
  have h := pow_le_pow_left₀ (abs_nonneg (inner ℝ d y)) (abs_real_inner_le_norm d y) 2
  rw [sq_abs, mul_pow] at h
  have hp : inner ℝ d y = _ := (inner_sub_left _ _ _).trans
    (congrArg (fun z => z - inner ℝ (dilatedLegalTailMeanVector K m hm) y)
      (legalTailMeanVector_pairing hy))
  rw [← hp, normalizedLegalTailMeanCapacity_gain hm hL, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- Two lifts into the same stage, for example from coprime denominators.
The second square detects a discrepancy even before solving the new projection. -/
theorem normalizedLegalTailMeanCapacity_two_lift_gain {K J L m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hK : L + 1 = m * (K + 1)) (hJ : L + 1 = n * (J + 1)) :
    let a := dilatedLegalTailMeanVector K m hm
    let b := dilatedLegalTailMeanVector J n hn
    let w := legalTailMeanVector L
    normalizedLegalTailMeanCapacity L -
        (normalizedLegalTailMeanCapacity K + normalizedLegalTailMeanCapacity J) / 2 =
      (((L : ℝ) + 1) / 4) * (‖(w - a) + (w - b)‖ ^ 2 + ‖a - b‖ ^ 2) := by
  dsimp only
  let w := legalTailMeanVector L
  let a := dilatedLegalTailMeanVector K m hm
  let b := dilatedLegalTailMeanVector J n hn
  have h1 := normalizedLegalTailMeanCapacity_gain hm hK
  have h2 := normalizedLegalTailMeanCapacity_gain hn hJ
  have hid : ‖(w - a) + (w - b)‖ ^ 2 + ‖a - b‖ ^ 2 = 2 * (‖w - a‖ ^ 2 + ‖w - b‖ ^ 2) := by
    rw [norm_sub_rev a b, show b - a = (w - a) - (w - b) by abel,
      norm_add_sq_real (w - a) (w - b), norm_sub_sq_real (w - a) (w - b)]
    ring
  change _ = _ * (‖(w - a) + (w - b)‖ ^ 2 + ‖a - b‖ ^ 2)
  rw [hid]
  change _ = ((L : ℝ) + 1) * ‖w - a‖ ^ 2 at h1
  change _ = ((L : ℝ) + 1) * ‖w - b‖ ^ 2 at h2
  linarith only [h1, h2]

private theorem factorial_cutoff_succ (n : ℕ) : n.factorial - 1 + 1 = n.factorial :=
  Nat.sub_add_cancel (Nat.factorial_pos n)

theorem normalizedLegalTailMeanCapacity_factorial_mono :
    Monotone (fun n : ℕ => normalizedLegalTailMeanCapacity (n.factorial - 1)) := by
  intro a b hab
  apply normalizedLegalTailMeanCapacity_mono_of_dvd
  simpa only [factorial_cutoff_succ] using Nat.factorial_dvd_factorial hab

theorem normalizedLegalTailMeanCapacity_le_factorial (K : ℕ) :
    normalizedLegalTailMeanCapacity K ≤
      normalizedLegalTailMeanCapacity ((K + 1).factorial - 1) := by
  apply normalizedLegalTailMeanCapacity_mono_of_dvd
  simpa only [factorial_cutoff_succ] using Nat.dvd_factorial (Nat.succ_pos K) (le_refl (K + 1))

private theorem normalizedCapacity_bdd : BddAbove (Set.range normalizedLegalTailMeanCapacity) :=
  ⟨1, by rintro _ ⟨k, rfl⟩; exact (legalTailMeanCapacity_normalized_bounds k).2⟩

theorem normalizedLegalTailMeanCapacity_factorial_tendsto :
    Tendsto (fun n : ℕ => normalizedLegalTailMeanCapacity (n.factorial - 1)) atTop
      (𝓝 (⨆ k, normalizedLegalTailMeanCapacity k)) := by
  let F := fun n : ℕ => normalizedLegalTailMeanCapacity (n.factorial - 1)
  have hb : BddAbove (Set.range F) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (legalTailMeanCapacity_normalized_bounds _).2⟩
  have he : (⨆ n, F n) = ⨆ k, normalizedLegalTailMeanCapacity k :=
    le_antisymm (ciSup_le fun n => le_ciSup normalizedCapacity_bdd (n.factorial - 1))
      (ciSup_le fun k => (normalizedLegalTailMeanCapacity_le_factorial k).trans
        (le_ciSup hb (k + 1)))
  rw [← he]
  exact tendsto_atTop_ciSup normalizedLegalTailMeanCapacity_factorial_mono hb

theorem legalHeadKernel_antitone : Antitone legalHeadKernel := by
  intro K L hKL z hz
  refine ⟨hz.1, ?_⟩
  change headMap K z = 0
  funext i
  have hi := congrFun (show headMap L z = 0 from hz.2) (⟨i.val, i.isLt.trans_le hKL⟩ : Fin L)
  simpa only [headMap_apply, Pi.zero_apply] using hi

theorem legalTailMeanCapacity_antitone : Antitone legalTailMeanCapacity := by
  intro K L hKL
  have hL := legalTailMeanVector_mem L
  have hK := legalHeadKernel_antitone hKL hL
  have he : inner ℝ (legalTailMeanVector K) (legalTailMeanVector L) =
      ‖legalTailMeanVector L‖ ^ 2 := by
    rw [legalTailMeanVector_pairing hK, ← legalTailMeanVector_pairing hL,
      real_inner_self_eq_norm_sq]
  have hd := sq_nonneg ‖legalTailMeanVector K - legalTailMeanVector L‖
  rw [norm_sub_sq_real, he] at hd
  change ‖legalTailMeanVector L‖ ^ 2 ≤ ‖legalTailMeanVector K‖ ^ 2
  linarith only [hd]

/-- Round N+1 up to the next multiple of K+1. -/
theorem normalizedLegalTailMeanCapacity_rounding (K N : ℕ) :
    normalizedLegalTailMeanCapacity K ≤
      normalizedLegalTailMeanCapacity N + (K : ℝ) / ((N : ℝ) + 1) := by
  let b := (K + 1) * (N / (K + 1) + 1)
  have hdiv := Nat.mod_add_div N (K + 1)
  have hmod : N % (K + 1) < K + 1 := Nat.mod_lt N (Nat.succ_pos K)
  have blo : N < b := by dsimp [b]; rw [Nat.mul_add, Nat.mul_one]; omega
  have bhi : b ≤ N + K + 1 := by dsimp [b]; rw [Nat.mul_add, Nat.mul_one]; omega
  have hc : b - 1 + 1 = b := Nat.sub_add_cancel (by omega)
  have hcr : ((b - 1 : ℕ) : ℝ) + 1 = (b : ℝ) := by exact_mod_cast hc
  have hbK : K + 1 ∣ b - 1 + 1 := by rw [hc]; exact ⟨N / (K + 1) + 1, rfl⟩
  have hbr : (b : ℝ) ≤ (N : ℝ) + (K : ℝ) + 1 := by exact_mod_cast bhi
  calc
    _ ≤ normalizedLegalTailMeanCapacity (b - 1) := normalizedLegalTailMeanCapacity_mono_of_dvd hbK
    _ = (b : ℝ) * legalTailMeanCapacity (b - 1) := by
      unfold normalizedLegalTailMeanCapacity
      rw [hcr]
    _ ≤ (b : ℝ) * legalTailMeanCapacity N := mul_le_mul_of_nonneg_left
      (legalTailMeanCapacity_antitone (by omega : N ≤ b - 1)) (Nat.cast_nonneg b)
    _ ≤ ((N : ℝ) + (K : ℝ) + 1) * legalTailMeanCapacity N :=
      mul_le_mul_of_nonneg_right hbr (legalTailMeanCapacity_pos N).le
    _ = normalizedLegalTailMeanCapacity N + (K : ℝ) * legalTailMeanCapacity N := by
      unfold normalizedLegalTailMeanCapacity; ring
    _ ≤ _ := by
      apply add_le_add_right
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left (legalTailMeanCapacity_bounds N).2 (Nat.cast_nonneg K)

/-- Ordinary cutoffs converge to the same supremum as factorial cutoffs. -/
theorem normalizedLegalTailMeanCapacity_tendsto :
    Tendsto normalizedLegalTailMeanCapacity atTop
      (𝓝 (⨆ K, normalizedLegalTailMeanCapacity K)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨K, hK⟩ : ∃ K : ℕ, a < normalizedLegalTailMeanCapacity K := by
      by_contra! h
      exact (not_le_of_gt ha) (ciSup_le h)
    obtain ⟨M, hM⟩ := exists_nat_gt ((K : ℝ) / (normalizedLegalTailMeanCapacity K - a))
    filter_upwards [Filter.eventually_ge_atTop M] with n hn
    have hn' : (K : ℝ) / (normalizedLegalTailMeanCapacity K - a) < (n : ℝ) + 1 :=
      hM.trans_le (by exact_mod_cast (by omega : M ≤ n + 1))
    have he : (K : ℝ) / ((n : ℝ) + 1) < normalizedLegalTailMeanCapacity K - a :=
      (div_lt_iff₀ (by positivity)).mpr (by
        simpa only [mul_comm] using (div_lt_iff₀ (sub_pos.mpr hK)).mp hn')
    linarith only [normalizedLegalTailMeanCapacity_rounding K n, he]
  · intro a ha
    exact Filter.Eventually.of_forall fun n => (le_ciSup normalizedCapacity_bdd n).trans_lt ha

/-- At the initial scale the mean projection is the original legal projection of one. -/
theorem normalizedLegalTailMeanCapacity_zero :
    normalizedLegalTailMeanCapacity 0 = 1 - limitEnergy := by
  have hs : legalHeadKernel 0 = closedSpace := by
    apply le_antisymm inf_le_left
    intro f hf
    refine ⟨hf, ?_⟩
    change headMap 0 f = 0
    funext i
    exact Fin.elim0 i
  let v := legalTailMeanVector 0
  have hv : v ∈ closedSpace := (legalTailMeanVector_mem 0).1
  have hu : limitProjection ∈ closedSpace := closedSpace.starProjection_apply_mem _
  have hd := closedSpace.sub_mem hv hu
  have h0 : v - limitProjection ∈ legalHeadKernel 0 := hs.symm ▸ hd
  have h1 : inner ℝ v (v - limitProjection) = inner ℝ hilbertOne (v - limitProjection) :=
    legalTailMeanVector_pairing h0
  have h2 : inner ℝ hilbertOne (v - limitProjection) =
      inner ℝ limitProjection (v - limitProjection) :=
    projection_pairing closedSpace hilbertOne _ hd
  have hz : inner ℝ (v - limitProjection) (v - limitProjection) = 0 := by
    rw [inner_sub_left, h1, h2, sub_self]
  have he : v = limitProjection := sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  simp only [normalizedLegalTailMeanCapacity, Nat.cast_zero, zero_add, one_mul]
  change ‖v‖ ^ 2 = 1 - limitEnergy
  rw [he, limitProjection_norm_sq]

/-- The rank-one defect coefficient gives the reciprocal of the base capacity. -/
theorem normalizedLegalTailMeanCapacity_zero_mul_defect :
    normalizedLegalTailMeanCapacity 0 *
        (1 + Bilinear.defectForm normalizedScreenedTwo normalizedScreenedTwo) = 1 := by
  rw [normalizedLegalTailMeanCapacity_zero, Bilinear.defectForm_normalizedScreenedTwo,
    norm_sub_sq_real, normalizedScreenedTwo_mean, hilbertOne_norm_sq, normalizedScreenedTwo_norm_sq]
  field_simp [one_sub_limitEnergy_pos.ne']
  ring

theorem normalizedLegalTailMeanCapacity_eq_one_iff_RH (K : ℕ) :
    normalizedLegalTailMeanCapacity K = 1 ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_legalTailMeanCapacity_saturation
    intro ε hε
    refine ⟨K, ?_⟩
    change 1 - ε < normalizedLegalTailMeanCapacity K
    rw [h]
    linarith
  · intro hRH
    have hOne := CenteredMeanSnake.boundary_eq_zero_iff_one_mem.mp
      ((CenteredMeanSnake.stageUnit_zero_iff_boundary 0).mp
        ((CenteredMeanSnake.stageUnit_zero_iff_RH 0).mpr hRH))
    have he := limitEnergy_zero_iff_mem.mpr hOne
    obtain ⟨hlo, hhi⟩ := legalTailMeanCapacity_normalized_bounds K
    rw [he, sub_zero] at hlo
    exact le_antisymm hhi hlo

theorem normalizedLegalTailMeanCapacity_iSup_eq_one_iff_RH :
    (⨆ K, normalizedLegalTailMeanCapacity K) = 1 ↔ RiemannHypothesis := by
  constructor
  · intro he
    apply riemannHypothesis_of_legalTailMeanCapacity_saturation
    intro ε hε
    change ∃ K, 1 - ε < normalizedLegalTailMeanCapacity K
    by_contra! h
    have hi := ciSup_le h
    rw [he] at hi
    linarith
  · intro h
    simp only [fun K => (normalizedLegalTailMeanCapacity_eq_one_iff_RH K).mpr h, ciSup_const]

/-- A uniform fraction of the remaining deficit suffices. The hypotheses can be
tested on explicit legal directions using `legalTailMean_gain_test`. -/
theorem riemannHypothesis_of_tailCapacity_relative_gain {δ : ℝ} (hδ : 0 < δ)
    (gain : ∀ K : ℕ, ∃ L : ℕ, δ * (1 - normalizedLegalTailMeanCapacity K) ≤
      normalizedLegalTailMeanCapacity L - normalizedLegalTailMeanCapacity K) :
    RiemannHypothesis := by
  let S := ⨆ K, normalizedLegalTailMeanCapacity K
  have hupper : S ≤ 1 := ciSup_le fun K => (legalTailMeanCapacity_normalized_bounds K).2
  have hineq (K : ℕ) : δ + (1 - δ) * normalizedLegalTailMeanCapacity K ≤ S := by
    obtain ⟨L, hL⟩ := gain K
    have h := le_ciSup normalizedCapacity_bdd L
    change normalizedLegalTailMeanCapacity L ≤ S at h
    linarith only [hL, h]
  have hfin : δ + (1 - δ) * S ≤ S := by
    apply le_of_tendsto_of_tendsto' (Filter.Tendsto.const_add δ
      (Filter.Tendsto.const_mul (1 - δ) normalizedLegalTailMeanCapacity_tendsto))
      tendsto_const_nhds hineq
  apply normalizedLegalTailMeanCapacity_iSup_eq_one_iff_RH.mp
  change S = 1
  apply le_antisymm hupper
  by_contra! h
  nlinarith only [hfin, mul_pos hδ (sub_pos.mpr h)]

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.legalTailMean_dilation_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms legalTailMean_dilation_orthogonal

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.normalizedLegalTailMeanCapacity_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalizedLegalTailMeanCapacity_gain

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.legalTailMean_gain_test' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms legalTailMean_gain_test

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.normalizedLegalTailMeanCapacity_two_lift_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalizedLegalTailMeanCapacity_two_lift_gain

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.normalizedLegalTailMeanCapacity_mono_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalizedLegalTailMeanCapacity_mono_of_dvd

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.normalizedLegalTailMeanCapacity_factorial_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalizedLegalTailMeanCapacity_factorial_tendsto

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.normalizedLegalTailMeanCapacity_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalizedLegalTailMeanCapacity_tendsto

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.normalizedLegalTailMeanCapacity_zero_mul_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalizedLegalTailMeanCapacity_zero_mul_defect

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.normalizedLegalTailMeanCapacity_eq_one_iff_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalizedLegalTailMeanCapacity_eq_one_iff_RH

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.normalizedLegalTailMeanCapacity_iSup_eq_one_iff_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalizedLegalTailMeanCapacity_iSup_eq_one_iff_RH

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.riemannHypothesis_of_tailCapacity_relative_gain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_of_tailCapacity_relative_gain

end RiemannResearch.RH.Pareto.PrimePowerSchur
