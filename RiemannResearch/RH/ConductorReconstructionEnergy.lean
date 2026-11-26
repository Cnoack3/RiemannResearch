import RiemannResearch.Analysis.HilbertConstraintEnergy
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.QConductorEscape
import RiemannResearch.RH.QConductorLimits
import RiemannResearch.RH.QCovarianceInvertibility
import RiemannResearch.RH.QFullDivisorProjection
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Reconstruction from all physical conductor observations

Source: user-provided Atom/Carry CRT Stage 3 handoff, §14.7.3. Index `i`
denotes conductor `i + 2`. The Pareto and Q test vectors are the actual
normalized residues in their own inner products. Data are prescribed
independently and may be any real sequence. Distinct conductors ensure
finite feasibility. The remaining condition is boundedness of the exact
energies on the running LCM tower. An explicit obstruction persists for the
decaying target b(d) = 1/√d, even though every finite system is solvable.
-/

noncomputable section
open Filter
open scoped Topology BigOperators ENNReal

namespace RiemannResearch.RH.ConductorReconstructionEnergy

open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.HilbertConstraintReconstruction
open Pareto.CoefficientStabilization ZetaTwoHilbert ZetaTwoParetoTransfer
open QFullDivisorProjection
open QParetoEquivalence ZetaTwoProbability

/-- Atom indices for the nontrivial divisors of the running LCM. -/
def stage (N : ℕ) : Finset ℕ :=
  (((lcmPeriod N : ℕ).divisors).filter (fun d => 1 < d)).image (fun d => d - 2)

theorem mem_stage (i N : ℕ) : i ∈ stage N ↔ i + 2 ∣ (lcmPeriod N : ℕ) := by
  constructor
  · intro h
    obtain ⟨d, hd, he⟩ := Finset.mem_image.mp h
    obtain ⟨hd, hlarge⟩ := Finset.mem_filter.mp hd
    have heq : i + 2 = d := by omega
    rw [heq]
    exact Nat.dvd_of_mem_divisors hd
  · intro h
    exact Finset.mem_image.mpr ⟨i + 2, Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨h, (lcmPeriod N).ne_zero⟩, by omega⟩, by omega⟩

theorem stage_tendsto : Tendsto stage atTop atTop := by
  apply tendsto_atTop.mpr
  intro F
  filter_upwards [eventually_ge_atTop (F.sup id + 2)] with N hN
  intro i hi
  apply (mem_stage i N).mpr
  have hi' : i ≤ F.sup id := Finset.le_sup (f := id) hi
  change i + 2 ∣ (Finset.Icc 1 N).lcm id
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Quadratic form of the Moore–Penrose inverse on a finite restriction. -/
def gramCost (u : ℕ → H) (b : ℕ → ℝ) (F : Finset ℕ) : ℝ :=
  ∑ i : F, b i * gramPseudoinverse (fun j : F => u j) (fun j : F => b j) i

/-- Every assignment on finitely many distinct physical atoms is feasible. -/
theorem finite_gram_range (u : ℕ → H) (b : ℕ → ℝ) (F : Finset ℕ)
    (hu : LinearIndependent ℝ (fun i : F => u i)) :
    ∃ c : F → ℝ, gram (fun i : F => u i) c = (fun i : F => b i) :=
  (gramEquiv hu).surjective _

/-- Exact cost; the finite range condition follows from atom independence. -/
theorem finiteOptimum_eq_gramCost (u : ℕ → H) (b : ℕ → ℝ) (F : Finset ℕ)
    (hu : LinearIndependent ℝ (fun i : F => u i)) :
    finiteOptimum u b F = ENNReal.ofReal (gramCost u b F) :=
  finiteConstraintEnergy_feasible _ _ (finite_gram_range u b F hu)

variable [CompleteSpace H]

theorem globalOptimum_eq_stage_cost (u : ℕ → H) (b : ℕ → ℝ)
    (hu : ∀ F : Finset ℕ, LinearIndependent ℝ (fun i : F => u i)) :
    globalOptimum u b = ⨆ N, ENNReal.ofReal (gramCost u b (stage N)) := by
  rw [globalOptimum_eq_iSup_finiteOptimum]
  simp_rw [← finiteOptimum_eq_gramCost u b _ (hu _)]
  apply le_antisymm
  · apply iSup_le
    intro F
    obtain ⟨N, hN⟩ := (stage_tendsto.eventually (eventually_ge_atTop F)).exists
    exact (finiteOptimum_mono u b hN).trans (le_iSup (fun n => finiteOptimum u b (stage n)) N)
  · exact iSup_le fun N => le_iSup _ (stage N)

/-- Once the cofinal pseudoinverse costs are uniformly finite, the stage
minimizers converge strongly to the unique representer in the closed atom span. -/
theorem reconstruction_iff_stage_cost (u : ℕ → H) (b : ℕ → ℝ)
    (hu : ∀ F : Finset ℕ, LinearIndependent ℝ (fun i : F => u i)) :
    (⨆ N, ENNReal.ofReal (gramCost u b (stage N))) < ⊤ ↔
      ∃ x : H, IsSolution u b x ∧ x ∈ closedSpan u ∧
        Tendsto (fun N => finiteMinimum u b (stage N)) atTop (𝓝 x) := by
  rw [← globalOptimum_eq_stage_cost u b hu, globalOptimum_eq_iSup_finiteOptimum,
    ← exists_solution_iff_iSup_finiteOptimum_lt_top]
  constructor
  · intro h
    obtain ⟨x, ⟨hx, hmem⟩, _⟩ := existsUnique_solution_in_closedSpan u b h
    refine ⟨x, hx, hmem, ?_⟩
    simpa only [Submodule.starProjection_eq_self_iff.mpr hmem] using
      finiteMinimum_tendsto_of_cofinal u b hx stage stage_tendsto
  · rintro ⟨x, hx, _, _⟩
    exact ⟨x, hx⟩

/-- A fixed squared-norm budget needs to hold at only cofinally many
running LCM stages. The same budget is attained by a global representer. -/
theorem bounded_solution_iff_frequently_stageCost (u : ℕ → H) (b : ℕ → ℝ)
    (hu : ∀ F : Finset ℕ, LinearIndependent ℝ (fun i : F => u i))
    {C : ℝ} (hC : 0 ≤ C) :
    (∃ x : H, ‖x‖ ^ 2 ≤ C ∧ IsSolution u b x) ↔
      ∃ᶠ N : ℕ in atTop, ENNReal.ofReal (gramCost u b (stage N)) ≤ ENNReal.ofReal C := by
  rw [bounded_solution_sq_iff_finite u b hC]
  constructor
  · intro h
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro N
    rw [← finiteOptimum_eq_gramCost u b _ (hu _)]
    exact (finiteOptimum_le_ofReal_iff u b (stage N) hC).mpr (h (stage N))
  · intro h F
    obtain ⟨N, hcost, hsub⟩ := (h.and_eventually (stage_tendsto.eventually
      (eventually_ge_atTop F))).exists
    rw [← finiteOptimum_eq_gramCost u b _ (hu _)] at hcost
    exact (finiteOptimum_le_ofReal_iff u b F hC).mp ((finiteOptimum_mono u b hsub).trans hcost)

def qAtom (i : ℕ) : QHilbert := qResidue (i + 2)

theorem p_finite_independent (F : Finset ℕ) :
    LinearIndependent ℝ (fun i : F => residueAtom i) :=
  residueAtom_linearIndependent.comp (fun i : F => (i : ℕ)) Subtype.val_injective

theorem q_finite_independent (F : Finset ℕ) :
    LinearIndependent ℝ (fun i : F => qAtom i) := by
  apply QCovarianceInvertibility.qResidue_linearIndependent
    (fun i : F => (i : ℕ) + 2) (fun i => by omega)
  intro i j h
  exact Subtype.ext (Nat.add_right_cancel h)

theorem physical_reconstruction_criteria (b : ℕ → ℝ) :
    ((⨆ N, ENNReal.ofReal (gramCost residueAtom b (stage N))) < ⊤ ↔
      ∃ x, IsSolution residueAtom b x ∧ x ∈ closedSpan residueAtom ∧
        Tendsto (fun N => finiteMinimum residueAtom b (stage N)) atTop (𝓝 x)) ∧
    ((⨆ N, ENNReal.ofReal (gramCost qAtom b (stage N))) < ⊤ ↔
      ∃ x, IsSolution qAtom b x ∧ x ∈ closedSpan qAtom ∧
        Tendsto (fun N => finiteMinimum qAtom b (stage N)) atTop (𝓝 x)) :=
  ⟨reconstruction_iff_stage_cost _ b p_finite_independent,
   reconstruction_iff_stage_cost _ b q_finite_independent⟩

private theorem compare_synthesis (F : Finset ℕ) (c : F → ℝ) :
    toPareto (Fintype.linearCombination ℝ (fun i : F => qAtom i) c) =
      Fintype.linearCombination ℝ (fun i : F => residueAtom i) c := by
  change toParetoLinear _ = _
  simp only [Fintype.linearCombination_apply, map_sum, map_smul]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg (fun z : Pareto.ThresholdHilbert => c i • z) (toPareto_residueAtom i)

/-- A bound for the same signed target transfers between the physical Gram
forms with the two probability-weight comparison constants. -/
theorem physical_dual_bound_transfer (b : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    (DualBound residueAtom b C → DualBound qAtom b (C * zetaTwo)) ∧
    (DualBound qAtom b C → DualBound residueAtom b (C * (2 / zetaTwo))) := by
  constructor
  · intro h F c
    have hnorm := toPareto_norm_sq_le (Fintype.linearCombination ℝ (fun i : F => qAtom i) c)
    rw [compare_synthesis] at hnorm
    simpa only [mul_assoc] using (h F c).trans (mul_le_mul_of_nonneg_left hnorm hC)
  · intro h F c
    have hnorm := toQ_norm_sq_le (Fintype.linearCombination ℝ (fun i : F => residueAtom i) c)
    rw [← compare_synthesis F c, toQ_toPareto, compare_synthesis F c] at hnorm
    simpa only [mul_assoc] using (h F c).trans (mul_le_mul_of_nonneg_left hnorm hC)

theorem physical_solvability_iff (b : ℕ → ℝ) :
    (∃ x, IsSolution residueAtom b x) ↔ ∃ y, IsSolution qAtom b y := by
  rw [exists_solution_iff_dualBound, exists_solution_iff_dualBound]
  constructor
  · rintro ⟨C, hC, hb⟩
    exact ⟨_, mul_nonneg hC zetaTwo_pos.le, (physical_dual_bound_transfer b hC).1 hb⟩
  · rintro ⟨C, hC, hb⟩
    exact ⟨_, mul_nonneg hC (div_nonneg (by norm_num) zetaTwo_pos.le),
      (physical_dual_bound_transfer b hC).2 hb⟩

private theorem qAtom_tendsto : Tendsto qAtom atTop (𝓝 0) := by
  apply qResidue_tendsto_zero (fun i => i + 2)
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop n] with i hi
  omega

private theorem pAtom_tendsto : Tendsto residueAtom atTop (𝓝 0) := by
  have h := toParetoCLM.continuous.continuousAt.tendsto.comp qAtom_tendsto
  simpa only [Function.comp_def, map_zero, toParetoCLM_apply, qAtom, toPareto_residueAtom]
    using h

omit [CompleteSpace H] in
/-- Every represented target decays as the conductor escapes. -/
private theorem target_tendsto {u : ℕ → H} {b : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0)) {x : H} (hx : IsSolution u b x) :
    Tendsto b atTop (𝓝 0) := by
  have hh : Tendsto (fun i => inner ℝ (u i) x) atTop (𝓝 (inner ℝ (0 : H) x)) :=
    hu.inner tendsto_const_nhds
  simpa only [inner_zero_left, show ∀ i, inner ℝ (u i) x = b i from hx] using hh

/-- A single nondecay obstruction forces the exact LCM-stage costs to have
infinite supremum under both measures, despite finite feasibility everywhere. -/
theorem nondecay_unbounded_costs (b : ℕ → ℝ) (hb : ¬ Tendsto b atTop (𝓝 0)) :
    (⨆ N, ENNReal.ofReal (gramCost residueAtom b (stage N))) = ⊤ ∧
    (⨆ N, ENNReal.ofReal (gramCost qAtom b (stage N))) = ⊤ := by
  constructor
  · by_contra h
    obtain ⟨x, hx, _, _⟩ := (physical_reconstruction_criteria b).1.mp (lt_top_iff_ne_top.mpr h)
    exact hb (target_tendsto pAtom_tendsto hx)
  · by_contra h
    obtain ⟨x, hx, _, _⟩ := (physical_reconstruction_criteria b).2.mp (lt_top_iff_ne_top.mpr h)
    exact hb (target_tendsto qAtom_tendsto hx)

/-- Normalized large-conductor atoms remain bounded in Q and escape every
fixed conductor head. Hence any represented signed target is o(d^(-1/2)). -/
theorem scaled_target_tendsto (b : ℕ → ℝ) (h : ∃ x, IsSolution qAtom b x) :
    Tendsto (fun i : ℕ => Real.sqrt ((i + 2 : ℕ) : ℝ) * b i) atTop (𝓝 0) := by
  obtain ⟨x, hx⟩ := h
  let v (i : ℕ) := Real.sqrt ((i + 2 : ℕ) : ℝ) • qAtom i
  have hh : Tendsto (fun i : ℕ => i + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro n
    filter_upwards [eventually_ge_atTop n] with i hi
    omega
  have hm (i : ℕ) : v i ∈ qConductorTailSpan (i + 1) :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i + 2, by omega, rfl⟩)
  have hbound (i : ℕ) : ‖v i‖ ≤ Real.sqrt (2 / zetaTwo) := by
    let d : ℕ := i + 2
    have hd : 0 < (d : ℝ) := by exact_mod_cast (by dsimp [d]; omega : 0 < d)
    have ht := mul_le_mul_of_nonneg_left (qResidue_norm_sq_le_two_div d (by dsimp [d]; omega)) hd.le
    have hc : (d : ℝ) * (2 / (zetaTwo * d)) = 2 / zetaTwo := by
      field_simp [hd.ne', zetaTwo_pos.ne']
    rw [hc] at ht
    apply Real.le_sqrt_of_sq_le
    change ‖Real.sqrt (d : ℝ) • qResidue d‖ ^ 2 ≤ 2 / zetaTwo
    rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt hd.le]
  have hw := qConductorTailSpan_weak_tendsto_zero v _ hh (fun i => by omega) hm
    _ (Real.sqrt_nonneg _) hbound x
  have he (i : ℕ) : inner ℝ x (v i) = Real.sqrt ((i + 2 : ℕ) : ℝ) * b i := by
    rw [real_inner_comm]
    change inner ℝ (Real.sqrt _ • qAtom i) x = _
    rw [real_inner_smul_left, hx i]
  simpa only [he] using hw

/-- The critical decay rate itself gives an explicit sequence of independently
prescribed observations with finite solutions and unbounded minimum energies. -/
theorem reciprocal_sqrt_costs_unbounded :
    let b := fun i : ℕ => (Real.sqrt ((i + 2 : ℕ) : ℝ))⁻¹
    (⨆ N, ENNReal.ofReal (gramCost residueAtom b (stage N))) = ⊤ ∧
    (⨆ N, ENNReal.ofReal (gramCost qAtom b (stage N))) = ⊤ := by
  let b := fun i : ℕ => (Real.sqrt ((i + 2 : ℕ) : ℝ))⁻¹
  have hnone : ¬ ∃ y, IsSolution qAtom b y := by
    intro hy
    have hs := scaled_target_tendsto b hy
    have he (i : ℕ) : Real.sqrt ((i + 2 : ℕ) : ℝ) * b i = 1 := by
      exact mul_inv_cancel₀ (by positivity)
    simp only [he] at hs
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hs)
  constructor
  · by_contra h
    obtain ⟨x, hx, _, _⟩ := (physical_reconstruction_criteria b).1.mp (lt_top_iff_ne_top.mpr h)
    exact hnone ((physical_solvability_iff b).mp ⟨x, hx⟩)
  · by_contra h
    obtain ⟨x, hx, _, _⟩ := (physical_reconstruction_criteria b).2.mp (lt_top_iff_ne_top.mpr h)
    exact hnone ⟨x, hx⟩

end RiemannResearch.RH.ConductorReconstructionEnergy
