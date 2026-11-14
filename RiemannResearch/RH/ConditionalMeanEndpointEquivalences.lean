import RiemannResearch.RH.ConditionalMeanExactEndpoint
import RiemannResearch.RH.ParetoFiniteHeadRepair
import RiemannResearch.RH.ResidueClosureDensity
import RiemannResearch.Analysis.CesaroDenseRange
import Mathlib.Tactic.Linarith

/-!
# Theorem 12.2 with its classical input exposed

Source: user-provided `RH_Random_Prime_Powers_CRT_Multi_Range_2026-09-19.tex`,
Theorem 12.2. The RH-to-density input is the discrete consequence of
L. Baez-Duarte, "A strengthening of the Nyman-Beurling criterion for the
Riemann hypothesis", https://arxiv.org/abs/math/0202141.

The published theorem supports the explicitly named
`StrongNymanBeurlingForward` proposition. No provider for that proposition
is supplied here. The final equivalence is therefore a conditional
formalization, not an unconditional kernel proof of all of Theorem 12.2.
All finite-head repair, density-to-infimum, mean-neutralization and
logarithmic-limit steps are proved; the reverse implication uses the
actual zeta zero obstruction.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.Cesaro
open RiemannResearch.Probability.ConditionalIID

/-- Dilation invariance upgrades constant-target membership to full density. -/
theorem hilbertLegalClosure_eq_top_of_one_mem (A : Set ℕ)
    (h : hilbertOne ∈ hilbertLegalClosure A) : hilbertLegalClosure A = ⊤ := by
  have hp (n : ℕ) : paretoPointHilbert n ∈ hilbertLegalClosure A := by
    rw [CoefficientStabilization.paretoPoint_eq_scaled_dilation_difference]
    exact (hilbertLegalClosure A).sub_mem
      ((hilbertLegalClosure A).smul_mem _
        (hilbertLegalClosure_dilation A h (n + 1) (by omega)))
      ((hilbertLegalClosure A).smul_mem _
        (hilbertLegalClosure_dilation A h (n + 2) (by omega)))
  have hspan : Submodule.span ℝ (Set.range paretoPointHilbert) ≤
      hilbertLegalClosure A := by
    apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    exact hp n
  have ht := (Submodule.span ℝ (Set.range paretoPointHilbert)).topologicalClosure_minimal
    hspan (Submodule.isClosed_topologicalClosure (hilbertLegalSubspace A))
  rw [paretoPoint_span_dense] at ht
  exact top_unique ht

/-- The mean-space vector with physical values one through Y and zero afterwards. -/
def conditionalHeadTarget (Y : ℕ) : ThresholdHilbert :=
  ∑ k ∈ Finset.range Y, lp.single 2 k (Real.sqrt (conditionalWeight k))

theorem conditionalHeadTarget_apply (Y k : ℕ) :
    conditionalHeadTarget Y k =
      if k < Y then Real.sqrt (conditionalWeight k) else 0 := by
  classical
  simp only [conditionalHeadTarget, lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  simp

theorem conditionalHeadTarget_norm_sq (Y : ℕ) :
    ‖conditionalHeadTarget Y‖ ^ 2 = (Y : ℝ) / ((Y : ℝ) + 2) := by
  rw [hilbert_norm_sq]
  have he (k : ℕ) : (conditionalHeadTarget Y k) ^ 2 =
      if k < Y then conditionalWeight k else 0 := by
    rw [conditionalHeadTarget_apply]
    split_ifs <;> simp [Real.sq_sqrt (conditionalWeight_pos k).le]
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range Y) (by
    intro k hk
    simp only [Finset.mem_range] at hk
    simp [hk])]
  calc
    (∑ k ∈ Finset.range Y, if k < Y then conditionalWeight k else 0) =
        ∑ k ∈ Finset.range Y, conditionalWeight k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [if_pos (Finset.mem_range.mp hk)]
    _ = _ := conditionalWeight_sum_range Y

theorem cesaroOperator_norm_sq_eq_conditionalMeanSquare (f : ThresholdHilbert) :
    ‖cesaroOperator f‖ ^ 2 = conditionalMeanSquare (hilbertSequence f) :=
  hilbertCesaro_norm_sq f

/-- The finite mean-space target has a genuine Pareto preimage with the exact head. -/
theorem exists_conditionalHeadTarget_preimage (Y : ℕ) :
    ∃ f : ThresholdHilbert, cesaroOperator f = conditionalHeadTarget Y ∧
      ∀ n, 0 < n → n ≤ Y → hilbertSequence f n = 1 := by
  obtain ⟨f, hf⟩ := cesaroOperator_finite_support_range (conditionalHeadTarget Y) Y
    (fun k hk => by rw [conditionalHeadTarget_apply, if_neg (by omega)])
  have hm (n : ℕ) (hn : 0 < n) (hnY : n ≤ Y) :
      cesaro (hilbertSequence f) n = 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have h := congrArg (fun u : ThresholdHilbert => u k) hf
    rw [cesaroOperator_apply, conditionalHeadTarget_apply, if_pos (by omega)] at h
    change Real.sqrt (conditionalWeight k) * cesaro (hilbertSequence f) (k + 1) =
      Real.sqrt (conditionalWeight k) at h
    apply mul_left_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (conditionalWeight_pos k)))
    simpa only [mul_one] using h
  refine ⟨f, hf, ?_⟩
  intro n hn hnY
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [cesaro_recover (hilbertSequence f) k, hm (k + 1) (by omega) hnY]
  cases k with
  | zero => simp
  | succ k =>
    rw [hm (k + 1) (by omega) (by omega)]
    push_cast
    ring

/-- The exact infimum follows from density by fixed-head repair and continuity. -/
theorem conditionalHeadMinimum_eq_head_mass_of_dense
    (hdense : hilbertLegalClosure (Set.Ici 1) = ⊤) (Y : ℕ) :
    conditionalHeadMinimum Y = (Y : ℝ) / ((Y : ℝ) + 2) := by
  apply le_antisymm _ (conditionalHeadMinimum_ge_head_mass Y)
  obtain ⟨f, hf, hhead⟩ := exists_conditionalHeadTarget_preimage Y
  obtain ⟨u, hu, ht⟩ := FiniteHeadRepair.exists_exact_head_approximants Y f
    (by rw [hdense]; trivial)
  have hE : Tendsto (fun j => conditionalMeanSquare (hilbertSequence (u j)))
      atTop (𝓝 ((Y : ℝ) / ((Y : ℝ) + 2))) := by
    have h := (((cesaroOperator.continuous.tendsto f).comp ht).norm).pow 2
    simpa only [Function.comp_def, cesaroOperator_norm_sq_eq_conditionalMeanSquare,
      hf, conditionalHeadTarget_norm_sq] using h
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨j, hj⟩ := (hE.eventually (gt_mem_nhds
    (lt_add_of_pos_right ((Y : ℝ) / ((Y : ℝ) + 2)) hε))).exists
  have hmem : hilbertSequence (u j) ∈ conditionalHeadClass Y := by
    refine ⟨(hu j).1, ?_⟩
    intro n hn hnY
    rw [(hu j).2 n hn hnY, hhead n hn hnY]
  exact (conditionalHeadMinimum_le Y hmem).trans hj.le

theorem exactConditionalEndpoint_of_one_mem
    (h : hilbertOne ∈ hilbertLegalClosure (Set.Ici 1)) : ExactConditionalEndpoint := by
  intro Y _
  exact conditionalHeadMinimum_eq_head_mass_of_dense
    (hilbertLegalClosure_eq_top_of_one_mem (Set.Ici 1) h) Y

/-- The sole unprovided classical input for the full endpoint equivalences.
This is a proposition, not an axiom or a proof of it. -/
def StrongNymanBeurlingForward : Prop :=
  RiemannHypothesis → hilbertOne ∈ hilbertLegalClosure (Set.Ici 1)

/-- Theorem 12.2: all four equivalences, including the zero-mean version of (iv),
conditional only on the explicitly exposed classical forward input. -/
theorem exact_endpoint_equivalences (hNB : StrongNymanBeurlingForward) :
    (RiemannHypothesis ↔ ExactConditionalEndpoint) ∧
    (RiemannHypothesis ↔ ZeroMeanExactConditionalEndpoint) ∧
    (RiemannHypothesis ↔ LogarithmicConditionalHeads) ∧
    (RiemannHypothesis ↔ ZeroMeanLogarithmicConditionalHeads) := by
  have hi : RiemannHypothesis ↔ ExactConditionalEndpoint :=
    ⟨fun h => exactConditionalEndpoint_of_one_mem (hNB h),
      riemannHypothesis_of_exactConditionalEndpoint⟩
  have hz : RiemannHypothesis ↔ ZeroMeanLogarithmicConditionalHeads :=
    ⟨fun h => zeroMeanLogarithmicConditionalHeads_of_exactEndpoint (hi.mp h),
      fun h => riemannHypothesis_of_logarithmicConditionalHeads
        (logarithmicConditionalHeads_iff_zeroMean.mpr h)⟩
  exact ⟨hi, hi.trans exactConditionalEndpoint_iff_zeroMean,
    hz.trans logarithmicConditionalHeads_iff_zeroMean.symm, hz⟩

/-- info: 'RiemannResearch.RH.Pareto.zeroMeanConditionalHeadMinimum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.zeroMeanConditionalHeadMinimum_eq
/-- info: 'RiemannResearch.RH.Pareto.logarithmicConditionalHeads_iff_zeroMean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.logarithmicConditionalHeads_iff_zeroMean
/-- info: 'RiemannResearch.RH.Pareto.riemannHypothesis_of_logarithmicConditionalHeads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.riemannHypothesis_of_logarithmicConditionalHeads
/-- info: 'RiemannResearch.RH.Pareto.conditionalHeadMinimum_eq_head_mass_of_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.conditionalHeadMinimum_eq_head_mass_of_dense
/-- info: 'RiemannResearch.RH.Pareto.exact_endpoint_equivalences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.exact_endpoint_equivalences
end RiemannResearch.RH.Pareto
