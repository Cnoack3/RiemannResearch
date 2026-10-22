import RiemannResearch.RH.ParetoPhysicalDualTransfer
import RiemannResearch.RH.ParetoDualSupportError

/-!
# The actual physical-dual finite-support projection

Source: user-provided `Prime_Phases_Agenda_Proof_Attempts.tex`,
Proposition "Explicit dual approximation and its coefficient vector".
At stage `n`, the head length is `K=n+1` and the duals are `u_2,...,u_K`.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.RH.Pareto.DualSupportError
open RiemannResearch.RH.ArithmeticCumulative

def physicalDualSpace (n : ℕ) : Submodule ℝ ThresholdHilbert :=
  synthesisSpan (fun i : Fin n => coefficientDual i.val)

instance physicalDualSpace_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (physicalDualSpace n) :=
  synthesisSpan_finiteDimensional _

def physicalDualProjection (n : ℕ) : ThresholdHilbert :=
  (physicalDualSpace n).starProjection hilbertOne

def physicalDualProjectionResidual (n : ℕ) : ThresholdHilbert :=
  hilbertOne - physicalDualProjection n

theorem physicalDualProjection_expansion (n : ℕ) :
    ∃ a : Fin n → ℝ, physicalDualProjection n = physicalDualCombination n a := by
  have hm := (physicalDualSpace n).starProjection_apply_mem hilbertOne
  change physicalDualProjection n ∈ synthesisSpan (fun i : Fin n => coefficientDual i.val) at hm
  unfold synthesisSpan at hm
  rw [← Fintype.range_linearCombination] at hm
  obtain ⟨a, ha⟩ := hm
  exact ⟨a, ha.symm⟩

theorem physicalDualSpace_support (n j : ℕ) (hj : n + 1 < j)
    (x : ThresholdHilbert) (hx : x ∈ physicalDualSpace n) :
    hilbertSequence x j = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    change hilbertSequenceLinear (-mobiusRieszHilbert (i.val + 2)) j = 0
    rw [map_neg]
    change -hilbertSequence (mobiusRieszHilbert (i.val + 2)) j = 0
    rw [mobiusRieszHilbert_sequence (i.val + 2) j (by omega),
      dualCoeff_eq_zero_of_lt (by omega) (by omega)]
    norm_num
  | zero =>
    change hilbertSequenceLinear 0 j = 0
    rw [map_zero]
    rfl
  | add x y hx hy ihx ihy =>
    change hilbertSequenceLinear x j = 0 at ihx
    change hilbertSequenceLinear y j = 0 at ihy
    change hilbertSequenceLinear (x + y) j = 0
    rw [map_add]
    simpa only [Pi.add_apply, ihx, ihy] using (add_zero (0 : ℝ))
  | smul c x hx ih =>
    change hilbertSequenceLinear x j = 0 at ih
    change hilbertSequenceLinear (c • x) j = 0
    rw [map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, ih, mul_zero]

theorem physicalDualProjection_support (n j : ℕ) (hj : n + 1 < j) :
    hilbertSequence (physicalDualProjection n) j = 0 :=
  physicalDualSpace_support n j hj _
    ((physicalDualSpace n).starProjection_apply_mem hilbertOne)

theorem physicalDualProjectionResidual_mobius_zero (n m : ℕ)
    (hm : 1 < m) (hmn : m ≤ n + 1) :
    mobiusDifferenceCLM m (physicalDualProjectionResidual n) = 0 := by
  let i : Fin n := ⟨m - 2, by omega⟩
  have hi : coefficientDual i.val ∈ physicalDualSpace n :=
    Submodule.subset_span ⟨i, rfl⟩
  have ho := ((physicalDualSpace n).mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal hilbertOne)
    (coefficientDual i.val) hi
  have hmidx : i.val + 2 = m := by dsimp [i]; omega
  rw [real_inner_comm, inner_coefficientDual_eq_coefficientCLM, hmidx] at ho
  change -(mobiusDifferenceCLM m (physicalDualProjectionResidual n)) = 0 at ho
  linarith

/-- Finite Möbius inversion determines every head coordinate of the residual. -/
theorem physicalDualProjectionResidual_head (n k : ℕ) (hk : k ≤ n + 1) :
    hilbertSequence (physicalDualProjectionResidual n) k =
      (k : ℝ) * hilbertSequence (physicalDualProjectionResidual n) 1 := by
  let f := physicalDualProjectionResidual n
  have hstep (j : ℕ) (hj : j + 1 ≤ n + 1) :
      hilbertSequence f (j + 1) - hilbertSequence f j = hilbertSequence f 1 := by
    have hi := sum_mobiusDifference (hilbertSequence f) (j + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hi
    rw [← hi]
    calc
      (∑ d ∈ (j + 1).divisors, mobiusDifference d (hilbertSequence f)) =
          ∑ d ∈ (j + 1).divisors,
            if d = 1 then hilbertSequence f 1 else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hd1 : d = 1
        · subst d
          simp [mobiusDifference]
        · have hdp := Nat.pos_of_mem_divisors hd
          have hdl := Nat.le_of_dvd (by omega : 0 < j + 1)
            (Nat.mem_divisors.mp hd).1
          rw [if_neg hd1]
          simpa only [mobiusDifferenceCLM_apply, f] using
            physicalDualProjectionResidual_mobius_zero n d (by omega) (by omega)
      _ = _ := by simp [Nat.mem_divisors]
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := hstep k hk
    rw [ih (by omega)] at hs
    push_cast
    nlinarith

def finiteLinearSequence (K j : ℕ) : ℝ := if j ≤ K then (j : ℝ) else 0

theorem finiteLinearSequence_summable (K : ℕ) :
    Summable (fun j => positiveWeight j * finiteLinearSequence K j ^ 2) := by
  apply weighted_summable_of_bounded (C := (K : ℝ) ^ 2)
  intro j
  unfold finiteLinearSequence
  split_ifs with hj
  · rw [abs_of_nonneg (sq_nonneg _)]
    have hle : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hj
    nlinarith [Nat.cast_nonneg (α := ℝ) j]
  · simp

def finiteLinearHilbert (K : ℕ) : ThresholdHilbert :=
  sequenceHilbert (finiteLinearSequence K) (finiteLinearSequence_summable K)

theorem finiteLinearHilbert_sequence (K : ℕ) :
    hilbertSequence (finiteLinearHilbert K) = finiteLinearSequence K := by
  apply hilbertSequence_sequenceHilbert
  simp [finiteLinearSequence]

theorem physicalDual_inner_finiteLinear (n : ℕ) (i : Fin n) :
    inner ℝ (coefficientDual i.val) (finiteLinearHilbert (n + 1)) = 0 := by
  rw [coefficientDual, inner_neg_left, mobiusRieszHilbert_inner,
    mobiusDifferenceCLM_apply, finiteLinearHilbert_sequence]
  have hdiff : mobiusDifference (i.val + 2) (finiteLinearSequence (n + 1)) =
      mobiusDifference (i.val + 2) (residue 0) := by
    unfold mobiusDifference
    apply Finset.sum_congr rfl
    intro d hd
    have hdl := Nat.le_of_dvd (by omega : 0 < i.val + 2) (Nat.mem_divisors.mp hd).1
    have h1 : d ≤ n + 1 := by omega
    have h2 : d - 1 ≤ n + 1 := by omega
    simp [finiteLinearSequence, h1, h2, residue]
  rw [hdiff, mobiusDifference_residue (i.val + 2) 0 (by omega)]
  simp

theorem physicalDualSpace_inner_finiteLinear (n : ℕ) (x : ThresholdHilbert)
    (hx : x ∈ physicalDualSpace n) :
    inner ℝ x (finiteLinearHilbert (n + 1)) = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact physicalDual_inner_finiteLinear n i
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_left, ihx, ihy]
  | smul c x hx ih => simp [real_inner_smul_left, ih]

theorem inner_finiteLinear_eq_sum (K : ℕ) (x : ThresholdHilbert) :
    inner ℝ x (finiteLinearHilbert K) =
      ∑ k ∈ Finset.range K, hilbertSequence x (k + 1) / ((k : ℝ) + 2) := by
  rw [hilbertGibbs_inner_physical]
  have hp (k : ℕ) : hilbertGibbsPhysical (finiteLinearHilbert K) k =
      if k < K then (k : ℝ) + 1 else 0 := by
    rw [hilbertGibbsPhysical_eq, finiteLinearHilbert_sequence]
    have he : k + 1 ≤ K ↔ k < K := by omega
    simp [finiteLinearSequence, he]
  rw [tsum_eq_sum (s := Finset.range K) (by
    intro k hk
    rw [hp, if_neg (by simpa only [Finset.mem_range] using hk)]
    simp)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hp, if_pos (Finset.mem_range.mp hk), hilbertGibbsPhysical_eq]
  unfold paretoWeight
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]

theorem finite_linear_sum (K : ℕ) :
    (∑ k ∈ Finset.range K, ((k : ℝ) + 1) / ((k : ℝ) + 2)) =
      (K : ℝ) - supportA K := by
  have hterm (k : ℕ) : ((k : ℝ) + 1) / ((k : ℝ) + 2) =
      1 - 1 / ((k : ℝ) + 2) := by
    have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
    field_simp [h2]
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← supportA_eq_sum]
  simp

theorem physicalDualProjectionResidual_first (n : ℕ) :
    hilbertSequence (physicalDualProjectionResidual n) 1 =
      supportA (n + 1) / (((n + 1 : ℕ) : ℝ) - supportA (n + 1)) := by
  have hq : inner ℝ (physicalDualProjection n) (finiteLinearHilbert (n + 1)) = 0 :=
    physicalDualSpace_inner_finiteLinear n _
      ((physicalDualSpace n).starProjection_apply_mem hilbertOne)
  have hone : inner ℝ hilbertOne (finiteLinearHilbert (n + 1)) = supportA (n + 1) := by
    rw [inner_finiteLinear_eq_sum, supportA_eq_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hh : hilbertSequence hilbertOne (k + 1) = 1 := by
      rw [hilbertOne_sequence]
      simp [zeroAnchor]
    change hilbertSequence hilbertOne (k + 1) / ((k : ℝ) + 2) = _
    rw [hh]
  have hres : inner ℝ (physicalDualProjectionResidual n) (finiteLinearHilbert (n + 1)) =
      hilbertSequence (physicalDualProjectionResidual n) 1 *
        (((n + 1 : ℕ) : ℝ) - supportA (n + 1)) := by
    rw [inner_finiteLinear_eq_sum, ← finite_linear_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [physicalDualProjectionResidual_head n (k + 1) (by
      have h := Finset.mem_range.mp hk
      omega)]
    push_cast
    ring
  have he : supportA (n + 1) =
      hilbertSequence (physicalDualProjectionResidual n) 1 *
        (((n + 1 : ℕ) : ℝ) - supportA (n + 1)) := by
    rw [physicalDualProjectionResidual, inner_sub_left, hone, hq, sub_zero] at hres
    exact hres
  have hhalf := supportA_le_half (n + 1)
  have hd : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) - supportA (n + 1) := by
    have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    linarith
  apply (eq_div_iff (ne_of_gt hd)).mpr
  exact he.symm

/-- The manuscript's explicit `q_K` is the actual physical-dual projection. -/
theorem physicalDualProjection_explicit (n j : ℕ) :
    hilbertSequence (physicalDualProjection n) j =
      if j ≤ n + 1 then
        (if j = 0 then 0 else 1) -
          (supportA (n + 1) / (((n + 1 : ℕ) : ℝ) - supportA (n + 1))) * j
      else 0 := by
  by_cases hj : j ≤ n + 1
  · rw [if_pos hj]
    have h := physicalDualProjectionResidual_head n j hj
    rw [physicalDualProjectionResidual_first] at h
    have hsub := congrFun
      (hilbertSequenceLinear.map_sub hilbertOne (physicalDualProjection n)) j
    change hilbertSequence (physicalDualProjectionResidual n) j =
      hilbertSequence hilbertOne j - hilbertSequence (physicalDualProjection n) j at hsub
    rw [hsub] at h
    have hh := congrFun (hilbertOne_sequence) j
    rw [hh] at h
    change (if j = 0 then 0 else 1) -
      hilbertSequence (physicalDualProjection n) j = _ at h
    linarith
  · rw [if_neg hj]
    exact physicalDualProjection_support n j (by omega)

theorem inner_one_of_head_support (K : ℕ) (x : ThresholdHilbert)
    (hx : ∀ j, K < j → hilbertSequence x j = 0) :
    inner ℝ x hilbertOne =
      ∑ k ∈ Finset.range K, paretoWeight k * hilbertSequence x (k + 1) := by
  rw [hilbertGibbs_inner_physical]
  simp only [hilbertGibbs_one_physical, mul_one]
  rw [tsum_eq_sum (s := Finset.range K) (by
    intro k hk
    rw [hilbertGibbsPhysical_eq, hx (k + 1) (by
      have h := (Finset.mem_range.not.mp hk)
      omega)]
    simp)]
  simp_rw [hilbertGibbsPhysical_eq]

theorem weighted_linear_head_sum (K : ℕ) :
    (∑ k ∈ Finset.range K, paretoWeight k * ((k : ℝ) + 1)) = supportA K := by
  rw [supportA_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  unfold paretoWeight
  have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (k : ℝ) + 2 ≠ 0 := by positivity
  field_simp [h1, h2]

theorem physicalDualProjection_inner_one (n : ℕ) :
    inner ℝ (physicalDualProjection n) hilbertOne =
      1 - 1 / (((n + 1 : ℕ) : ℝ) + 1) -
        (supportA (n + 1) / (((n + 1 : ℕ) : ℝ) - supportA (n + 1))) *
          supportA (n + 1) := by
  rw [inner_one_of_head_support (n + 1) _ (physicalDualProjection_support n)]
  have hs :
      (∑ k ∈ Finset.range (n + 1),
        paretoWeight k * hilbertSequence (physicalDualProjection n) (k + 1)) =
      (∑ k ∈ Finset.range (n + 1), paretoWeight k) -
        (supportA (n + 1) / (((n + 1 : ℕ) : ℝ) - supportA (n + 1))) *
          ∑ k ∈ Finset.range (n + 1), paretoWeight k * ((k : ℝ) + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [physicalDualProjection_explicit, if_pos (by
      have h := Finset.mem_range.mp hk
      omega), if_neg (by omega : k + 1 ≠ 0)]
    push_cast
    ring
  rw [hs, paretoWeight_partial_sum, weighted_linear_head_sum]

theorem physicalDualProjectionResidual_norm_sq (n : ℕ) :
    ‖physicalDualProjectionResidual n‖ ^ 2 = supportErrorSq (n + 1) := by
  have ho : inner ℝ (hilbertOne - physicalDualProjection n)
      (physicalDualProjection n) = 0 := by
    rw [real_inner_comm]
    exact ((physicalDualSpace n).mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal hilbertOne) _
      ((physicalDualSpace n).starProjection_apply_mem _)
  rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm] at ho
  have hq := physicalDualProjection_inner_one n
  rw [physicalDualProjectionResidual, norm_sub_sq_real, hilbertOne_norm_sq,
    real_inner_comm, hq]
  unfold supportErrorSq
  have hd : (((n + 1 : ℕ) : ℝ) - supportA (n + 1)) ≠ 0 := by
    have hhalf := supportA_le_half (n + 1)
    have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hs :
      (supportA (n + 1) / (((n + 1 : ℕ) : ℝ) - supportA (n + 1))) *
          supportA (n + 1) =
        supportA (n + 1) ^ 2 / (((n + 1 : ℕ) : ℝ) - supportA (n + 1)) := by ring
  rw [hq] at ho
  rw [hs] at ho
  rw [hs]
  ring_nf at ho ⊢
  linarith

/-- The proven logarithmic support budget now applies to the actual Hilbert vector. -/
theorem physicalDualProjectionResidual_log_bound (n : ℕ) :
    ‖physicalDualProjectionResidual n‖ ^ 2 ≤
      (2 * Real.log (((n + 1 : ℕ) : ℝ) + 1) ^ 2 + 1) / ((n + 1 : ℕ) : ℝ) := by
  rw [physicalDualProjectionResidual_norm_sq]
  exact supportErrorSq_log_bound (n + 1) (by omega)

end RiemannResearch.RH.Pareto.CoefficientStabilization
