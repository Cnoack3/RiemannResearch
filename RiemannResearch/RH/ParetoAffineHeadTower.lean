import RiemannResearch.RH.MixedConductorHead
import RiemannResearch.RH.ParetoCoordinateEvaluation
import RiemannResearch.RH.ParetoMixedCenteredParityHeads
import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Orthogonal tower for the Pareto mean-one fiber

At stage n the first n positive physical coordinates are fixed to one. The
directions available for further corrections form the mixed space with those
coordinates zero. Projecting the next coordinate representer onto this kernel
gives a nonzero row by finite mixed interpolation. Normalizing to unit response
gives the one-dimensional orthogonal increment.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.AffineHeadTower

open CoefficientStabilization

/-- Tangent space after imposing the first n positive physical coordinates. -/
def kernel : ℕ → Submodule ℝ ThresholdHilbert
  | 0 => mixedClosure
  | n + 1 => kernel n ⊓ (physicalEvaluationCLM n).ker

theorem mem_kernel {x : ThresholdHilbert} (n : ℕ) :
    x ∈ kernel n ↔ x ∈ mixedClosure ∧ ∀ i < n, physicalEvaluationCLM i x = 0 := by
  induction n with
  | zero => simp [kernel]
  | succ n ih =>
    change (x ∈ kernel n ∧ physicalEvaluationCLM n x = 0) ↔ _
    rw [ih]
    constructor
    · rintro ⟨⟨hm, hh⟩, hn⟩
      refine ⟨hm, fun i hi => ?_⟩
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
      · exact hh i h
      · exact hn
    · rintro ⟨hm, hh⟩
      exact ⟨⟨hm, fun i hi => hh i (Nat.lt_succ_of_lt hi)⟩, hh n (Nat.lt_succ_self n)⟩

theorem kernel_antitone : Antitone kernel := by
  intro n m h x hx
  obtain ⟨hm, hh⟩ := (mem_kernel m).mp hx
  exact (mem_kernel n).mpr ⟨hm, fun i hi => hh i (lt_of_lt_of_le hi h)⟩

theorem kernel_closed (n : ℕ) : IsClosed (kernel n : Set ThresholdHilbert) := by
  induction n with
  | zero => exact isClosed_closure
  | succ n ih => exact ih.inter (physicalEvaluationCLM n).isClosed_ker

instance (n : ℕ) : (kernel n).HasOrthogonalProjection := by
  let _ : CompleteSpace (kernel n) := (kernel_closed n).completeSpace_coe
  infer_instance

/-- The Riesz representer of physical site n+1 after the previous constraints. -/
def row (n : ℕ) : ThresholdHilbert :=
  (kernel n).starProjection ((paretoWeight n)⁻¹ • paretoPointHilbert n)

theorem row_mem (n : ℕ) : row n ∈ kernel n := (kernel n).starProjection_apply_mem _

theorem row_inner (n : ℕ) {x : ThresholdHilbert} (hx : x ∈ kernel n) :
    inner ℝ x (row n) = physicalEvaluationCLM n x := by
  let p := (paretoWeight n)⁻¹ • paretoPointHilbert n
  have h := (kernel n).sub_starProjection_mem_orthogonal p x hx
  rw [inner_sub_right, sub_eq_zero] at h
  calc
    inner ℝ x (row n) = inner ℝ x p := h.symm
    _ = inner ℝ p x := real_inner_comm _ _
    _ = _ := by rw [show p = _ from rfl, real_inner_smul_left]; rfl

theorem row_ne_zero (n : ℕ) : row n ≠ 0 := by
  obtain ⟨B, x, hx, hh⟩ := exists_mixed_exact_head (fun k => if k = n+1 then 1 else 0) (n+1)
  have he (i : ℕ) (hi : i ≤ n) :
      physicalEvaluationCLM i x = if i = n then 1 else 0 := by
    rw [physicalEvaluationCLM_apply, hh _ (Nat.succ_pos _) (by omega)]
    simp
  have hk : x ∈ kernel n := (mem_kernel n).mpr
    ⟨mixedSpace_window_le_closure B hx, fun i hi => by rw [he i hi.le, if_neg hi.ne]⟩
  intro hzero
  have h := row_inner n hk
  simp [hzero, he n le_rfl] at h

/-- The shortest mixed correction vanishing at sites 1,...,n with value one at n+1. -/
def direction (n : ℕ) : ThresholdHilbert := (‖row n‖ ^ 2)⁻¹ • row n

theorem direction_mem (n : ℕ) : direction n ∈ kernel n := (kernel n).smul_mem _ (row_mem n)

theorem direction_eval (n : ℕ) : physicalEvaluationCLM n (direction n) = 1 := by
  have h := (row_inner n (row_mem n)).symm
  rw [real_inner_self_eq_norm_sq] at h
  simp [direction, h, row_ne_zero n]

theorem direction_orthogonal (n : ℕ) : direction n ∈ (kernel (n+1))ᗮ := by
  intro x hx
  change x ∈ kernel n ∧ physicalEvaluationCLM n x = 0 at hx
  rw [direction, real_inner_smul_right, row_inner n hx.1, hx.2, mul_zero]

theorem directions_inner {i j : ℕ} (h : i < j) : inner ℝ (direction j) (direction i) = 0 :=
  direction_orthogonal i _ (kernel_antitone (Nat.succ_le_of_lt h) (direction_mem j))

/-- The exact orthogonal splitting of a tangent vector at one further coordinate. -/
theorem subtract_next_mem (n : ℕ) {x : ThresholdHilbert} (hx : x ∈ kernel n) :
    x - physicalEvaluationCLM n x • direction n ∈ kernel (n+1) := by
  refine ⟨(kernel n).sub_mem hx ((kernel n).smul_mem _ (direction_mem n)), ?_⟩
  change physicalEvaluationCLM n (x - _ • _) = 0
  rw [map_sub, map_smul, direction_eval, smul_eq_mul, mul_one, sub_self]

theorem layer_eq_span (n : ℕ) :
    kernel n ⊓ (kernel (n+1))ᗮ = Submodule.span ℝ {direction n} := by
  apply le_antisymm
  · intro x hx
    let c := physicalEvaluationCLM n x
    have hm := subtract_next_mem n hx.1
    have ho := (kernel (n+1)).orthogonal.sub_mem hx.2
      ((kernel (n+1)).orthogonal.smul_mem c (direction_orthogonal n))
    have hz : x - c • direction n = 0 := inner_self_eq_zero.mp (ho _ hm)
    exact Submodule.mem_span_singleton.mpr ⟨c, (sub_eq_zero.mp hz).symm⟩
  · exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      ⟨direction_mem n, direction_orthogonal n⟩))

/-- The affine fiber at depth n fixes the mean and the first n physical values. -/
def fiber (n : ℕ) : Set ThresholdHilbert :=
  {v | v ∈ closedSpace ∧ inner ℝ v hilbertOne = 1 ∧ ∀ i < n, physicalEvaluationCLM i v = 1}

/-- The successive canonical affine lifts, starting at the screened mean section. -/
def patch : ℕ → ThresholdHilbert
  | 0 => normalizedScreenedTwo
  | n+1 => patch n + (1 - physicalEvaluationCLM n (patch n)) • direction n

theorem patch_spec (n : ℕ) : patch n ∈ fiber n ∧ patch n ∈ (kernel n)ᗮ := by
  induction n with
  | zero =>
    have hu := normalizedScreenedTwo_mem_screenedPrimeClosure
    rw [screenedPrimeClosure_eq_inf_orthogonal] at hu
    exact ⟨⟨hu.1, normalizedScreenedTwo_mean, fun i hi => by omega⟩, hu.2⟩
  | succ n ih =>
    obtain ⟨⟨hv, hmean, hhead⟩, hort⟩ := ih
    let a := 1 - physicalEvaluationCLM n (patch n)
    have hm := ((mem_kernel n).mp (direction_mem n)).1
    obtain ⟨hV, hzero⟩ := (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp hm
    change (patch n + a • direction n ∈ fiber (n+1)) ∧
      patch n + a • direction n ∈ (kernel (n+1))ᗮ
    refine ⟨⟨closedSpace.add_mem hv (closedSpace.smul_mem _ hV), ?_, ?_⟩, ?_⟩
    · rw [inner_add_left, real_inner_smul_left, hzero, hmean, mul_zero, add_zero]
    · intro i hi
      rw [map_add, map_smul, smul_eq_mul]
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
      · rw [((mem_kernel n).mp (direction_mem n)).2 i h, mul_zero, add_zero, hhead i h]
      · rw [direction_eval, mul_one]; dsimp [a]; ring
    · exact (kernel (n+1)).orthogonal.add_mem
        (fun y hy => hort y (kernel_antitone (Nat.le_succ n) hy))
        ((kernel (n+1)).orthogonal.smul_mem a (direction_orthogonal n))

theorem mem_fiber_iff (n : ℕ) (v : ThresholdHilbert) :
    v ∈ fiber n ↔ v - patch n ∈ kernel n := by
  obtain ⟨⟨hp, hm, he⟩, _⟩ := patch_spec n
  rw [mem_kernel, mem_mixedClosure_iff_mem_closedSpace_and_mean_zero]
  constructor
  · rintro ⟨hv, hmean, hhead⟩
    exact ⟨⟨closedSpace.sub_mem hv hp, by rw [inner_sub_left, hmean, hm, sub_self]⟩,
      fun i hi => by rw [map_sub, hhead i hi, he i hi, sub_self]⟩
  · rintro ⟨⟨hv, hmean⟩, hhead⟩
    have hV := closedSpace.add_mem hv hp
    rw [sub_add_cancel] at hV
    rw [inner_sub_left, hm, sub_eq_zero] at hmean
    refine ⟨hV, hmean, fun i hi => ?_⟩
    have hi' := hhead i hi
    rwa [map_sub, he i hi, sub_eq_zero] at hi'

/-- Exact cost above the unique least-norm patch. -/
theorem feasible_norm_sq (n : ℕ) {v : ThresholdHilbert} (hv : v ∈ fiber n) :
    ‖v‖^2 = ‖patch n‖^2 + ‖v - patch n‖^2 := by
  have h := (patch_spec n).2 _ ((mem_fiber_iff n v).mp hv)
  calc
    ‖v‖^2 = ‖(v - patch n) + patch n‖^2 := by rw [sub_add_cancel]
    _ = _ := by rw [norm_add_sq_real, h]; ring

/-- Scalar correction cost at the next physical site. -/
def stepEnergy (n : ℕ) : ℝ :=
  (1 - physicalEvaluationCLM n (patch n))^2 / ‖row n‖^2

theorem patch_norm_sq_step (n : ℕ) :
    ‖patch (n+1)‖^2 = ‖patch n‖^2 + stepEnergy n := by
  have ho := (real_inner_comm _ _).trans ((patch_spec n).2 _ (direction_mem n))
  rw [patch, norm_add_sq_real, real_inner_smul_right, ho, mul_zero, mul_zero, add_zero,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, direction, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  unfold stepEnergy
  field_simp [(norm_ne_zero_iff.mpr (row_ne_zero n))]

theorem patch_norm_sq (n : ℕ) :
    ‖patch n‖^2 = ‖normalizedScreenedTwo‖^2 + ∑ i ∈ Finset.range n, stepEnergy i := by
  induction n with
  | zero => simp [patch]
  | succ n ih => rw [patch_norm_sq_step, ih, Finset.sum_range_succ]; ring

theorem patch_error_sq (n : ℕ) :
    ‖patch n - hilbertOne‖^2 = ‖normalizedScreenedTwo - hilbertOne‖^2 +
      ∑ i ∈ Finset.range n, stepEnergy i := by
  rw [norm_sub_sq_real, norm_sub_sq_real, (patch_spec n).1.2.1, normalizedScreenedTwo_mean,
    patch_norm_sq]
  ring

/-- Each new observation splits off one orthogonal line. -/
theorem kernel_split (n : ℕ) :
    kernel (n+1) ⊔ Submodule.span ℝ {direction n} = kernel n := by
  rw [← layer_eq_span]
  exact RiemannResearch.Analysis.NestedOrthogonalDecomposition.prime_sup_carry
    (kernel_antitone (Nat.le_succ n))

/-- Orthogonal synthesis of the minimum-norm affine patch. -/
theorem patch_eq_sum (n : ℕ) :
    patch n = normalizedScreenedTwo + ∑ i ∈ Finset.range n,
      (1 - physicalEvaluationCLM i (patch i)) • direction i := by
  induction n with
  | zero => simp [patch]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    rfl

theorem patch_norm_sq_between {n m : ℕ} (hnm : n ≤ m) :
    ‖patch m‖^2 = ‖patch n‖^2 + ‖patch m - patch n‖^2 := by
  obtain ⟨hv, hm, hh⟩ := (patch_spec m).1
  exact feasible_norm_sq n ⟨hv, hm, fun i hi => hh i (lt_of_lt_of_le hi hnm)⟩

private theorem eq_zero_of_all_kernels {x : ThresholdHilbert} (hk : ∀ n, x ∈ kernel n) :
    x = 0 := by
  apply hilbertSequence_injective
  funext k
  cases k with
  | zero => simp
  | succ i =>
    have h := ((mem_kernel (i+1)).mp (hk (i+1))).2 i (Nat.lt_succ_self _)
    rw [← physicalEvaluationCLM_apply, ← physicalEvaluationCLM_apply, map_zero]
    exact h

theorem kernel_intersection : (⨅ n, kernel n) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  exact eq_zero_of_all_kernels (fun n => (iInf_le kernel n) hx)

/-- The orthogonal lines exhaust the entire mixed closure in the Hilbert norm. -/
theorem directions_dense :
    (Submodule.span ℝ (Set.range direction)).topologicalClosure = mixedClosure := by
  let S := (Submodule.span ℝ (Set.range direction)).topologicalClosure
  have hSM : S ≤ mixedClosure := Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr (by
      rintro _ ⟨n, rfl⟩
      exact ((mem_kernel n).mp (direction_mem n)).1))
    (show IsClosed (mixedClosure : Set ThresholdHilbert) from isClosed_closure)
  apply le_antisymm hSM
  intro x hx
  let e := x - S.starProjection x
  have he : e ∈ Sᗮ := S.sub_starProjection_mem_orthogonal x
  have hk (n : ℕ) : e ∈ kernel n := by
    induction n with
    | zero => exact mixedClosure.sub_mem hx (hSM (S.starProjection_apply_mem x))
    | succ n ih =>
      refine ⟨ih, ?_⟩
      have hd : direction n ∈ S := Submodule.le_topologicalClosure _
        (Submodule.subset_span (Set.mem_range_self n))
      have h := (real_inner_comm _ _).trans (he _ hd)
      rw [direction, real_inner_smul_right, row_inner n ih, mul_eq_zero] at h
      exact h.resolve_left (inv_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr (row_ne_zero n))))
  have hfix : x = S.starProjection x := sub_eq_zero.mp (eq_zero_of_all_kernels hk)
  exact S.starProjection_eq_self_iff.mp hfix.symm

/-- On the mean-one fiber, the same Pythagorean remainder measures the physical error. -/
theorem feasible_error_sq (n : ℕ) {v : ThresholdHilbert} (hv : v ∈ fiber n) :
    ‖v - hilbertOne‖^2 = ‖patch n - hilbertOne‖^2 + ‖v - patch n‖^2 := by
  rw [norm_sub_sq_real v hilbertOne, norm_sub_sq_real (patch n) hilbertOne,
    hv.2.1, (patch_spec n).1.2.1, feasible_norm_sq n hv]
  ring

private theorem eval_one (n : ℕ) : physicalEvaluationCLM n hilbertOne = 1 := by
  rw [physicalEvaluationCLM_apply, hilbertOne_sequence]
  simp [zeroAnchor]

private theorem patch_eq_one_of_seed (hu : normalizedScreenedTwo = hilbertOne) (n : ℕ) :
    patch n = hilbertOne := by
  induction n with
  | zero => exact hu
  | succ n ih => simp only [patch, ih, eval_one, sub_self, zero_smul, add_zero]

private theorem stepEnergy_zero_of_seed (hu : normalizedScreenedTwo = hilbertOne) (n : ℕ) :
    stepEnergy n = 0 := by
  rw [stepEnergy, patch_eq_one_of_seed hu, eval_one, sub_self, zero_pow (by decide : 2 ≠ 0), zero_div]

/-- Bounded total correction cost is equivalent to the screened seed being one. -/
theorem bounded_energy_iff :
    (∃ C : ℝ, ∀ n : ℕ, ∑ i ∈ Finset.range n, stepEnergy i ≤ C) ↔
      normalizedScreenedTwo = hilbertOne := by
  constructor
  · rintro ⟨C, hC⟩
    have hu : normalizedScreenedTwo ∈ closedSpace := (patch_spec 0).1.1
    have hm (n : ℕ) : patch n - normalizedScreenedTwo ∈ mixedClosure := by
      apply (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mpr
      exact ⟨closedSpace.sub_mem (patch_spec n).1.1 hu, by
        rw [inner_sub_left, (patch_spec n).1.2.1, normalizedScreenedTwo_mean, sub_self]⟩
    have he (n i : ℕ) (hi : i < n) : patch n i = hilbertOne i := by
      have h := ((patch_spec n).1.2.2 i hi).trans (eval_one i).symm
      simpa only [physicalEvaluationCLM_apply, hilbertSequence_succ,
        div_left_inj' (Real.sqrt_pos.2 (paretoWeight_pos i)).ne'] using h
    have hd := mem_mixedClosure_of_bounded_exact_heads
      (hilbertOne - normalizedScreenedTwo) id (fun n => patch n - normalizedScreenedTwo)
      tendsto_id hm (fun n i hi => by
        change patch n i - normalizedScreenedTwo i = hilbertOne i - normalizedScreenedTwo i
        rw [he n i hi])
      (‖normalizedScreenedTwo - hilbertOne‖^2 + C) (fun n => by
        rw [sub_sub_sub_cancel_right, norm_sub_rev, patch_error_sq]
        linarith only [hC n])
    apply one_mem_closedSpace_iff_normalizedScreenedTwo.mp
    simpa only [sub_add_cancel] using closedSpace.add_mem (mixedClosure_le_closedSpace hd) hu
  · intro hu
    refine ⟨0, fun n => ?_⟩
    simp [stepEnergy_zero_of_seed hu]

/-- The infinite energy test specializes the tower to the RH implication. -/
theorem summable_stepEnergy_iff : Summable stepEnergy ↔ normalizedScreenedTwo = hilbertOne := by
  constructor
  · intro h
    exact bounded_energy_iff.mp ⟨∑' i, stepEnergy i, fun n =>
      h.sum_le_tsum _ (fun i _ => by unfold stepEnergy; positivity)⟩
  · intro hu
    have hfun : stepEnergy = fun _ => 0 := funext (stepEnergy_zero_of_seed hu)
    rw [hfun]
    exact summable_zero

theorem riemannHypothesis_of_summable_steps (h : Summable stepEnergy) : RiemannHypothesis :=
  riemannHypothesis_of_normalizedScreenedTwo (summable_stepEnergy_iff.mp h)

/-- Cofinal boundedness is enough because the scalar energies are nonnegative. -/
theorem cofinal_energy_iff :
    (∃ C : ℝ, ∀ n : ℕ, ∃ m ≥ n, ∑ i ∈ Finset.range m, stepEnergy i ≤ C) ↔
      normalizedScreenedTwo = hilbertOne := by
  rw [← bounded_energy_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n => ?_⟩
    obtain ⟨m, hm, hE⟩ := hC n
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
      (fun i _ _ => by unfold stepEnergy; positivity)).trans hE
  · rintro ⟨C, hC⟩
    exact ⟨C, fun n => ⟨n, le_rfl, hC n⟩⟩

/-- If the seed differs from the physical constant, the minimum correction
cost grows beyond every finite bound. -/
theorem energy_tendsto_atTop_of_seed_ne (hu : normalizedScreenedTwo ≠ hilbertOne) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, stepEnergy i) atTop atTop := by
  have h := mt cofinal_energy_iff.mp hu
  push_neg at h
  apply tendsto_atTop.2
  intro b
  obtain ⟨n, hn⟩ := h b
  exact eventually_atTop.2 ⟨n, fun m hm => (hn m hm).le⟩

/-- Existing finite centered-parity trials give unconditional sublinear growth of
the minimum physical squared error in this tower. -/
theorem patch_error_sublinear :
    Tendsto (fun n : ℕ => ‖patch n - hilbertOne‖^2 / (n : ℝ)) atTop (𝓝 0) := by
  let z := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2
  obtain ⟨B, m, hhead, hlim⟩ := pdf_centered_parity_finite_mixed_sublinear
  have hz : z ∈ closedSpace := closedSpace.smul_mem _ (packet_mem_closedSpace 2 (by decide))
  have hzmean : inner ℝ z hilbertOne = 1 := by
    dsimp only [z]
    rw [real_inner_smul_left, hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
      paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
      Nat.cast_ofNat, inv_mul_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  have hf (n : ℕ) : z - m n ∈ fiber n := by
    obtain ⟨hm, hh⟩ := hhead n
    obtain ⟨hV, hzero⟩ := (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp
      (mixedSpace_window_le_closure (B n) hm)
    refine ⟨closedSpace.sub_mem hz hV, by rw [inner_sub_left, hzmean, hzero, sub_zero],
      fun i hi => ?_⟩
    have he := hh (i+1) (Nat.succ_pos _) (by omega)
    have he' : physicalEvaluationCLM i (m n) = physicalEvaluationCLM i (z - hilbertOne) := by
      simpa only [physicalEvaluationCLM_apply] using he
    rw [map_sub, he', map_sub, eval_one]
    ring
  apply squeeze_zero (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) _ hlim
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have he := feasible_error_sq n (hf n)
  have hr : (z - m n) - hilbertOne = (z - hilbertOne) - m n := by abel
  rw [hr] at he
  rw [he]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.RH.Pareto.PrimePowerSchur.AffineHeadTower
