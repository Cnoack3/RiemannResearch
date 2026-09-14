import RiemannResearch.RH.FiniteTwoSeedHeadMean
import RiemannResearch.RH.ParetoLegalApproximationClosure
import RiemannResearch.RH.ParetoLegalHeadGrowth

/-!
# The actual finite two-seed exact-head energy

Source: user-provided research direction, 14 September 2026. Work in the full
Pareto Hilbert norm, retaining all signed mixed terms and allowing every
positive integer dilation of seeds 2 and 3. No squarefree or conductor-growth
restriction is imposed.

The optimization set consists of actual finite legal Hilbert vectors. Its
nonemptiness follows from the previously proved triangular head construction.
The infimum need not be attained; arbitrary near-minimizers have a finite
dilation budget. The last theorem is a conditional research reduction: a
cofinal subpolynomial upper bound for this explicit infimum remains unproved.
-/

open Filter

namespace RiemannResearch.RH.Pareto.TwoSeedExactHeadEnergy

noncomputable section

private theorem seeds_pos : ∀ a ∈ ({2, 3} : Set ℕ), 0 < a := by
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> omega

/-- Actual finite legal vectors whose physical sequence is one through `N`. -/
def Feasible (N : ℕ) (f : ThresholdHilbert) : Prop :=
  f ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) ∧
    ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1

/-- Full squared norms, without separating seed or frequency channels. -/
def energyValues (N : ℕ) : Set ℝ :=
  {e | ∃ f : ThresholdHilbert, Feasible N f ∧ ‖f‖ ^ 2 = e}

/-- Infimum over every finite legal dilation budget. -/
def energy (N : ℕ) : ℝ := sInf (energyValues N)

theorem feasible_nonempty (N : ℕ) : ∃ f, Feasible N f := by
  obtain ⟨g, hg, hhead⟩ :=
    FiniteTwoSeedCompletion.exists_head (fun _ => (1 : ℝ)) N
  obtain ⟨f, hf, hseq⟩ := legalSeedSpan_exists_hilbert
    ({2, 3} : Set ℕ) seeds_pos (FiniteTwoSeedCompletion.budgetSpan_le_legal N hg)
  refine ⟨f, hf, ?_⟩
  simpa only [hseq] using hhead

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

/-- The compulsory head is charged in the same full Hilbert norm. -/
theorem head_floor_le_energy (N : ℕ) :
    (N : ℝ) / ((N : ℝ) + 1) ≤ energy N := by
  apply le_energy
  intro f hf
  rw [paretoMellin_head_tail_energy hf.2]
  exact le_add_of_nonneg_right (MeasureTheory.integral_nonneg fun _ => sq_nonneg _)

/-- No minimizer-existence assumption is needed. -/
theorem exists_near_minimizer (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ f, Feasible N f ∧ ‖f‖ ^ 2 < energy N + ε := by
  by_contra! h
  have hh : energy N + ε ≤ energy N := le_energy h
  linarith

/-- Every near-minimizer is realized at a finite, freely chosen budget. -/
theorem exists_finite_budget_near_minimizer (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∃ f : ThresholdHilbert,
      hilbertSequence f ∈ FiniteTwoSeedCompletion.budgetSpan M ∧
      (∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) ∧
      ‖f‖ ^ 2 < energy N + ε := by
  obtain ⟨f, hf, he⟩ := exists_near_minimizer N hε
  have hlegal : hilbertSequence f ∈ legalSeedSpan ({2, 3} : Set ℕ) := hf.1
  obtain ⟨M, hM⟩ :=
    (FiniteTwoSeedCompletion.mem_legal_iff_exists_budget (hilbertSequence f)).mp hlegal
  exact ⟨M, f, hM, hf.2, he⟩

/-- A finite budget at least as large as the head, so feasibility is automatic. -/
def BudgetFeasible (N K : ℕ) (f : ThresholdHilbert) : Prop :=
  hilbertSequence f ∈ FiniteTwoSeedCompletion.budgetSpan (N + K) ∧
    ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1

def budgetEnergyValues (N K : ℕ) : Set ℝ :=
  {e | ∃ f : ThresholdHilbert, BudgetFeasible N K f ∧ ‖f‖ ^ 2 = e}

/-- Infimum at the finite dilation budget `N + K`. -/
def budgetEnergy (N K : ℕ) : ℝ := sInf (budgetEnergyValues N K)

theorem budgetFeasible_nonempty (N K : ℕ) : ∃ f, BudgetFeasible N K f := by
  obtain ⟨g, hg, hhead⟩ :=
    FiniteTwoSeedCompletion.exists_head (fun _ => (1 : ℝ)) N
  obtain ⟨f, hf, hseq⟩ := legalSeedSpan_exists_hilbert
    ({2, 3} : Set ℕ) seeds_pos (FiniteTwoSeedCompletion.budgetSpan_le_legal N hg)
  refine ⟨f, ?_, ?_⟩
  · rw [hseq]
    exact FiniteTwoSeedCompletion.budgetSpan_mono (Nat.le_add_right N K) hg
  · simpa only [hseq] using hhead

theorem budgetEnergyValues_nonempty (N K : ℕ) :
    (budgetEnergyValues N K).Nonempty := by
  obtain ⟨f, hf⟩ := budgetFeasible_nonempty N K
  exact ⟨‖f‖ ^ 2, f, hf, rfl⟩

theorem budgetEnergyValues_bddBelow (N K : ℕ) :
    BddBelow (budgetEnergyValues N K) := by
  refine ⟨0, ?_⟩
  rintro e ⟨f, hf, rfl⟩
  exact sq_nonneg ‖f‖

theorem budgetEnergy_le {N K : ℕ} {f : ThresholdHilbert}
    (hf : BudgetFeasible N K f) : budgetEnergy N K ≤ ‖f‖ ^ 2 :=
  csInf_le (budgetEnergyValues_bddBelow N K) ⟨f, hf, rfl⟩

theorem energy_le_budgetEnergy (N K : ℕ) : energy N ≤ budgetEnergy N K := by
  apply le_csInf (budgetEnergyValues_nonempty N K)
  rintro e ⟨f, hf, rfl⟩
  apply energy_le
  exact ⟨FiniteTwoSeedCompletion.budgetSpan_le_legal (N + K) hf.1, hf.2⟩

theorem budgetEnergy_antitone (N : ℕ) : Antitone (budgetEnergy N) := by
  intro K L hKL
  apply le_csInf (budgetEnergyValues_nonempty N K)
  rintro e ⟨f, hf, rfl⟩
  exact budgetEnergy_le
    ⟨FiniteTwoSeedCompletion.budgetSpan_mono (Nat.add_le_add_left hKL N) hf.1, hf.2⟩

/-- Exhausting the finite dilation budgets recovers the unrestricted finite
legal infimum. This is a limit for each fixed head; no interchange of limits
or uniform budget-growth estimate is asserted. -/
theorem budgetEnergy_tendsto (N : ℕ) :
    Tendsto (budgetEnergy N) atTop (nhds (energy N)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun K => ha.trans_le (energy_le_budgetEnergy N K)
  · intro b hb
    obtain ⟨M, f, hf, hhead, he⟩ :=
      exists_finite_budget_near_minimizer N (sub_pos.mpr hb)
    have he' : ‖f‖ ^ 2 < b := by linarith
    filter_upwards [eventually_ge_atTop M] with K hK
    apply lt_of_le_of_lt _ he'
    apply budgetEnergy_le
    refine ⟨FiniteTwoSeedCompletion.budgetSpan_mono ?_ hf, hhead⟩
    omega

/-- A right-half-plane zero constrains the actual infimum, uniformly over all budgets. -/
theorem energy_power_lower_of_zeta
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) {N : ℕ} (hN : 3 ≤ N) :
    ((2 * s.re - 1) / (4 * ‖s‖ ^ 2)) *
      ((N : ℝ) + 1) ^ (2 * s.re - 1) ≤ energy N := by
  apply le_energy
  intro f hf
  exact legal_exactHead_power_lower_of_zeta ({2, 3} : Set ℕ) seeds_pos s hs hs1 hz
    (Submodule.le_topologicalClosure _ hf.1) hN hf.2

/-- Conditional research reduction. Each exponent may use its own cofinal
sequence of head lengths, and every witness may use a different finite budget.
The cofinal subpolynomial estimate itself is not established here. -/
theorem riemannHypothesis_of_cofinal_subpower
    (hsub : ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧ energy N ≤ C * ((N : ℝ) + 1) ^ p) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨s, hz, hs, hslt⟩ := RiemannResearch.RH.exists_right_zero_of_not_RH hRH
  have hs1 : s ≠ 1 := by intro he; simp [he] at hslt
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  let δ : ℝ := 2 * s.re - 1
  let p : ℝ := δ / 2
  let c : ℝ := δ / (4 * ‖s‖ ^ 2)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hp : 0 < p := by dsimp [p]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨C, hC⟩ := hsub p hp
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp ht
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hpow.eventually (eventually_gt_atTop (C / c)))
  obtain ⟨N, hN, hupper⟩ := hC (max 3 N₀)
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hlarge := hN₀ N ((le_max_right _ _).trans hN)
  have hlarge' : C < c * ((N : ℝ) + 1) ^ p := by
    have hh := (div_lt_iff₀ hc).mp hlarge
    nlinarith
  have hbase : 0 < (N : ℝ) + 1 := by positivity
  have hpos : 0 < ((N : ℝ) + 1) ^ p := Real.rpow_pos_of_pos hbase _
  have hδp : δ = p + p := by dsimp [p]; ring
  have hsplit : ((N : ℝ) + 1) ^ δ =
      ((N : ℝ) + 1) ^ p * ((N : ℝ) + 1) ^ p := by
    rw [hδp, Real.rpow_add hbase]
  have hlower : c * ((N : ℝ) + 1) ^ δ ≤ energy N :=
    energy_power_lower_of_zeta s hs hs1 hz hN3
  rw [hsplit] at hlower
  nlinarith [mul_pos (sub_pos.mpr hlarge') hpos]

end

end RiemannResearch.RH.Pareto.TwoSeedExactHeadEnergy
