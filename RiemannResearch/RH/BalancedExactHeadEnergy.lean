import RiemannResearch.RH.BalancedHeadInterpolation
import RiemannResearch.RH.ParetoExactHeadClosure

/-!
# The unrestricted exact-head optimum for the proposed minimal support

Source: user-provided argument, RH_Minimal_Seeds_Continuation_20260916.md,
Section 13. The optimization is over actual finite combinations from the
existing nonzero Möbius-target support, with no dilation-budget restriction.
The full Hilbert norm retains every signed mixed term. Uniform boundedness
is characterized, not asserted. In particular support thinning remains open.
-/

open Filter
namespace RiemannResearch.RH.Pareto.BalancedExactHeadEnergy
open RiemannResearch.Analysis
noncomputable section

/-- The precise candidate minimal finite span from the source. -/
def targetSpan : Submodule ℝ ThresholdHilbert :=
  dictionarySpan balancedIndexHilbert balancedNonzeroTargetSupport

/-- Feasibility has both literal finite support and exact physical head constraints. -/
def Feasible (N : ℕ) (f : ThresholdHilbert) : Prop :=
  f ∈ targetSpan ∧ ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1

def energyValues (N : ℕ) : Set ℝ :=
  {e | ∃ f : ThresholdHilbert, Feasible N f ∧ ‖f‖ ^ 2 = e}

/-- No minimizer or externally chosen finite budget is built into the infimum. -/
def energy (N : ℕ) : ℝ := sInf (energyValues N)

theorem feasible_nonempty (N : ℕ) : ∃ f, Feasible N f :=
  ⟨balancedTargetHead N, balancedTargetHead_mem_nonzeroTargetSpan N,
    balancedTargetHead_exact N⟩

theorem energyValues_nonempty (N : ℕ) : (energyValues N).Nonempty := by
  obtain ⟨f, hf⟩ := feasible_nonempty N
  exact ⟨‖f‖ ^ 2, f, hf, rfl⟩

theorem energyValues_bddBelow (N : ℕ) : BddBelow (energyValues N) := by
  refine ⟨0, ?_⟩
  rintro e ⟨f, hf, rfl⟩
  exact sq_nonneg ‖f‖

theorem energy_le {N : ℕ} {f : ThresholdHilbert} (hf : Feasible N f) :
    energy N ≤ ‖f‖ ^ 2 :=
  csInf_le (energyValues_bddBelow N) ⟨f, hf, rfl⟩

theorem le_energy {N : ℕ} {B : ℝ}
    (hB : ∀ f, Feasible N f → B ≤ ‖f‖ ^ 2) : B ≤ energy N := by
  apply le_csInf (energyValues_nonempty N)
  rintro e ⟨f, hf, rfl⟩
  exact hB f hf

theorem energy_nonneg (N : ℕ) : 0 ≤ energy N :=
  le_energy fun f _ => sq_nonneg ‖f‖

theorem feasible_of_le {M N : ℕ} (hMN : M ≤ N)
    {f : ThresholdHilbert} (hf : Feasible N f) : Feasible M f :=
  ⟨hf.1, fun k hk hkM => hf.2 k hk (hkM.trans hMN)⟩

theorem energy_monotone : Monotone energy := by
  intro M N hMN
  exact le_energy fun f hf => energy_le (feasible_of_le hMN hf)

/-- The head contribution is compulsory in the same full Pareto norm. -/
theorem head_floor_le_energy (N : ℕ) :
    (N : ℝ) / ((N : ℝ) + 1) ≤ energy N := by
  apply le_energy
  intro f hf
  rw [paretoMellin_head_tail_energy hf.2]
  exact le_add_of_nonneg_right (MeasureTheory.integral_nonneg fun _ => sq_nonneg _)

/-- Arbitrarily close feasible finite witnesses exist even if the infimum is not attained. -/
theorem exists_near_minimizer (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f, Feasible N f ∧ ‖f‖ ^ 2 < energy N + ε := by
  by_contra! h
  have hh : energy N + ε ≤ energy N := le_energy h
  linarith

/-- The proposed minimal span is an actual subspace of the original legal span. -/
theorem targetSpan_le_legal : targetSpan ≤ hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  rw [← balanced_dictionarySpan_univ]
  exact Submodule.span_mono (Set.image_mono (Set.subset_univ _))

/-- Supported closure vectors can be approximated while preserving any fixed head.
The projection norm may depend arbitrarily on N. -/
theorem exists_target_near_with_same_head {f : ThresholdHilbert}
    (hf : f ∈ targetSpan.topologicalClosure) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ThresholdHilbert, g ∈ targetSpan ∧
      (∀ k, 0 < k → k ≤ N → hilbertSequence g k = hilbertSequence f k) ∧
      ‖f - g‖ < ε := by
  let L := balancedHeadProjection N
  have hL : 0 < 1 + ‖L‖ := by positivity
  have hδ : 0 < ε / (1 + ‖L‖) := div_pos hε hL
  have hf' : f ∈ closure (targetSpan : Set ThresholdHilbert) := hf
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hf' _ hδ
  let q := g + L (f - g)
  have hq : q ∈ targetSpan := by
    apply targetSpan.add_mem hg
    apply balancedHeadProjection_mem_nonzeroTargetSpan
    exact targetSpan.topologicalClosure.sub_mem hf (targetSpan.le_topologicalClosure hg)
  refine ⟨q, hq, ?_, ?_⟩
  · intro k hk hkN
    change hilbertSequenceLinear (g + balancedHeadProjection N (f - g)) k = _
    rw [map_add]
    change hilbertSequence g k + hilbertSequence (balancedHeadProjection N (f - g)) k = _
    rw [balancedHeadProjection_exact_head N (f - g) k hk hkN]
    change hilbertSequenceLinear g k + hilbertSequenceLinear (f - g) k = _
    rw [map_sub]
    change hilbertSequence g k + (hilbertSequence f k - hilbertSequence g k) = _
    ring
  · have he : f - q = (f - g) - L (f - g) := by dsimp [q]; abel
    rw [he]
    have hb := L.le_opNorm (f - g)
    have hd : ‖f - g‖ < ε / (1 + ‖L‖) := by
      simpa only [dist_eq_norm] using hdist
    have hsmall : (1 + ‖L‖) * ‖f - g‖ < ε := by
      have := (lt_div_iff₀ hL).mp hd
      nlinarith
    calc
      _ ≤ ‖f - g‖ + ‖L (f - g)‖ := norm_sub_le _ _
      _ ≤ ‖f - g‖ + ‖L‖ * ‖f - g‖ := add_le_add le_rfl hb
      _ < ε := by nlinarith

/-- Passing to the supported closure does not change any exact-head infimum. -/
theorem energy_le_closed {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ targetSpan.topologicalClosure)
    (hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) :
    energy N ≤ ‖f‖ ^ 2 := by
  by_contra h
  have hlt : ‖f‖ ^ 2 < energy N := lt_of_not_ge h
  have ho : IsOpen {g : ThresholdHilbert | ‖g‖ ^ 2 < energy N} :=
    isOpen_lt (continuous_norm.pow 2) continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho f hlt
  obtain ⟨g, hg, hsame, hnear⟩ := exists_target_near_with_same_head hf N hδ
  have hgf : Feasible N g :=
    ⟨hg, fun k hk hkN => (hsame k hk hkN).trans (hhead k hk hkN)⟩
  have hgn : ‖g‖ ^ 2 < energy N := hball
    (by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hnear)
  exact (not_lt_of_ge (energy_le hgf)) hgn

/-- Bounded unrestricted optimal energy supplies actual bounded exact-head witnesses. -/
theorem hilbertOne_mem_closure_of_energy_bddAbove
    (hb : BddAbove (Set.range energy)) : hilbertOne ∈ targetSpan.topologicalClosure := by
  obtain ⟨C, hC⟩ := hb
  choose f hf he using fun N => exists_near_minimizer N (by norm_num : (0 : ℝ) < 1)
  apply hilbertOne_mem_closure_of_bounded_exact_head_energy targetSpan f
    (fun N => (hf N).1) (fun N => (hf N).2) (C := C + 1)
  intro N
  exact (he N).le.trans (add_le_add (hC ⟨N, rfl⟩) le_rfl)

/-- If the supported closure contains one, each fixed-head optimum is at most one. -/
theorem energy_le_one_of_closure
    (h1 : hilbertOne ∈ targetSpan.topologicalClosure) (N : ℕ) : energy N ≤ 1 := by
  have hhead : ∀ k, 0 < k → k ≤ N → hilbertSequence hilbertOne k = 1 := by
    intro k hk hkN
    simp [hilbertOne_sequence, zeroAnchor, Nat.ne_of_gt hk]
  simpa only [hilbertOne_norm_sq] using energy_le_closed h1 hhead

/-- Uniform boundedness of the actual unrestricted infimum is exactly the
remaining minimal-support closure condition, not an extra established estimate. -/
theorem energy_bddAbove_iff_closure :
    BddAbove (Set.range energy) ↔ hilbertOne ∈ targetSpan.topologicalClosure := by
  constructor
  · exact hilbertOne_mem_closure_of_energy_bddAbove
  · intro h1
    refine ⟨1, ?_⟩
    rintro e ⟨N, rfl⟩
    exact energy_le_one_of_closure h1 N

/-- The finite limit in the bounded case is forced to be exactly one. -/
theorem energy_tendsto_one_of_bddAbove (hb : BddAbove (Set.range energy)) :
    Tendsto energy atTop (nhds 1) := by
  have h1 := hilbertOne_mem_closure_of_energy_bddAbove hb
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp ht
  have hl : Tendsto (fun N : ℕ => 1 - ((N : ℝ) + 1)⁻¹) atTop (nhds (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hi
  have hlow (N : ℕ) : 1 - ((N : ℝ) + 1)⁻¹ ≤ energy N := by
    have he : 1 - ((N : ℝ) + 1)⁻¹ = (N : ℝ) / ((N : ℝ) + 1) := by
      have hn : (N : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [he]
    exact head_floor_le_energy N
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow
    (energy_le_one_of_closure h1)

/-- Failure of supported approximation forces the actual unrestricted optimum
to diverge, not merely the norms of one proposed construction. -/
theorem energy_tendsto_atTop_of_not_closure
    (h1 : hilbertOne ∉ targetSpan.topologicalClosure) :
    Tendsto energy atTop atTop := by
  have hb : ¬ BddAbove (Set.range energy) := by
    intro hb
    exact h1 (hilbertOne_mem_closure_of_energy_bddAbove hb)
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨e, he, hB⟩ := not_bddAbove_iff.mp hb B
  obtain ⟨N, rfl⟩ := he
  filter_upwards [eventually_ge_atTop N] with M hM
  exact hB.le.trans (energy_monotone hM)

/-- There is no finite limiting plateau above one. -/
theorem energy_limit_dichotomy :
    Tendsto energy atTop (nhds 1) ∨ Tendsto energy atTop atTop := by
  by_cases hb : BddAbove (Set.range energy)
  · exact Or.inl (energy_tendsto_one_of_bddAbove hb)
  · exact Or.inr (energy_tendsto_atTop_of_not_closure fun h1 =>
      hb (energy_bddAbove_iff_closure.mpr h1))

/-- CONDITIONAL RESEARCH REDUCTION: the uniform energy bound is unresolved.
Once supplied, the conclusion is Lean's actual Riemann Hypothesis proposition. -/
theorem riemannHypothesis_of_energy_bddAbove (hb : BddAbove (Set.range energy)) :
    RiemannHypothesis := by
  obtain ⟨C, hC⟩ := hb
  choose f hf he using fun N => exists_near_minimizer N (by norm_num : (0 : ℝ) < 1)
  apply riemannHypothesis_of_bounded_exact_subspace_heads targetSpan targetSpan_le_legal f
    (fun N => (hf N).1) (fun N => (hf N).2) (C := C + 1)
  intro N
  exact (he N).le.trans (add_le_add (hC ⟨N, rfl⟩) le_rfl)

end
end RiemannResearch.RH.Pareto.BalancedExactHeadEnergy
