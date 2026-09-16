import RiemannResearch.Analysis.FiniteResidueConductorSupport
import RiemannResearch.RH.CoupledResidualCorrections

/-!
# Actual finite Pareto fits have zero-total residue charges

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 9, for the residue expansion. The coefficients below are constructed
by span induction from the genuine binary and ternary Hilbert generators.
The formal conductor `1` is retained, even though its residue function is zero.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoupledResidual
open FiniteTwoSeedCompletion RamanujanLaguerre AdjacentPacket
open RiemannResearch.Analysis.FiniteResidueCharge

private theorem generator_conductor_mem (M p m : ℕ)
    (hm : 0 < m) (hmM : m ≤ M) (hseed : p = 2 ∨ p = 3) :
    m ∈ conductorSet M ∧ p * m ∈ conductorSet M := by
  have hbase : m ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨hm, hmM⟩
  constructor
  · simp only [conductorSet, Finset.mem_union]
    exact Or.inl (Or.inl hbase)
  · rcases hseed with rfl | rfl
    · simp only [conductorSet, Finset.mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨m, hbase, rfl⟩))
    · simp only [conductorSet, Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨m, hbase, rfl⟩)

private theorem generator_charge_representation (M p m : ℕ)
    (hp : 0 < p) (hm : 0 < m) (hmM : m ≤ M) (hseed : p = 2 ∨ p = 3) :
    ∃ b : conductorSet M → ℝ, (∑ i, b i = 0) ∧
      ∀ n, hilbertSequence (generator p m hp hm) n =
        ∑ i, b i * residue (i : ℕ) n := by
  classical
  obtain ⟨hmS, hpmS⟩ := generator_conductor_mem M p m hm hmM hseed
  let src : conductorSet M := ⟨m, hmS⟩
  let tgt : conductorSet M := ⟨p * m, hpmS⟩
  refine ⟨fun i => (if i = tgt then 1 else 0) - (if i = src then 1 else 0), ?_, ?_⟩
  · simp [Finset.sum_sub_distrib]
  · intro n
    rw [generator_sequence_apply]
    simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
    simp [src, tgt]

/-- Every vector in the actual budget has a residue expansion on the genuine
conductor set with total coefficient zero. No independence or interpolation
hypothesis is needed for this construction. -/
theorem budget_charge_representation (M : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ budgetHilbert M) :
    ∃ b : conductorSet M → ℝ, (∑ i, b i = 0) ∧
      ∀ n, hilbertSequence f n = ∑ i, b i * residue (i : ℕ) n := by
  classical
  rw [← canonicalHilbertFamily_span] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨hm, hmM, hs⟩ := (mem_canonicalIndices M i.val).mp i.property
    have hp : 0 < i.val.1 := by
      rcases hs with h | ⟨h, _⟩ <;> omega
    have hseed : i.val.1 = 2 ∨ i.val.1 = 3 := by
      rcases hs with h | ⟨h, _⟩
      · exact Or.inr h
      · exact Or.inl h
    exact generator_charge_representation M i.val.1 i.val.2 hp hm hmM hseed
  | zero =>
    refine ⟨fun _ => 0, by simp, ?_⟩
    intro n
    simp only [zero_mul, Finset.sum_const_zero]
    change hilbertSequenceLinear 0 n = 0
    exact congrFun hilbertSequenceLinear.map_zero n
  | add x y hx hy ihx ihy =>
    obtain ⟨bx, hbx, hex⟩ := ihx
    obtain ⟨dy, hby, hey⟩ := ihy
    refine ⟨fun i => bx i + dy i, ?_, ?_⟩
    · rw [Finset.sum_add_distrib, hbx, hby, add_zero]
    · intro n
      simp only [hilbertSequence_add, Pi.add_apply, hex n, hey n, add_mul,
        Finset.sum_add_distrib]
  | smul c x hx ih =>
    obtain ⟨b, hb, he⟩ := ih
    refine ⟨fun i => c * b i, ?_, ?_⟩
    · rw [← Finset.mul_sum, hb, mul_zero]
    · intro n
      simp only [hilbertSequence_smul, Pi.smul_apply, smul_eq_mul, he n]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The actual optimum inherits the constructed zero-total residue charge. -/
theorem fit_charge_representation (M : ℕ) :
    ∃ b : conductorSet M → ℝ, (∑ i, b i = 0) ∧
      ∀ n, hilbertSequence (fit M) n = ∑ i, b i * residue (i : ℕ) n :=
  budget_charge_representation M (fit M)
    ((budgetHilbert M).starProjection_apply_mem hilbertOne)

/-- In particular the actual fit has either a nonzero constant charge or a
nonzero even moment whose corresponding odd index is at most `4*M-1`. -/
theorem fit_finite_charge_forcing (M : ℕ) :
    ∃ b : conductorSet M → ℝ, (∑ i, b i = 0) ∧
      (∀ n, hilbertSequence (fit M) n = ∑ i, b i * residue (i : ℕ) n) ∧
      (constantTerm b (fun i : conductorSet M => ((i : ℕ) : ℝ)) ≠ 0 ∨
        ∃ j, moment b (fun i : conductorSet M => ((i : ℕ) : ℝ)) (j + 1) ≠ 0 ∧
          2 * j + 1 ≤ 4 * M - 1) := by
  obtain ⟨b, hb, he⟩ := fit_charge_representation M
  refine ⟨b, hb, he, ?_⟩
  by_cases ha : constantTerm b (fun i : conductorSet M => ((i : ℕ) : ℝ)) = 0
  · exact Or.inr (actual_support_moment_index_bound M (conductorSet M)
      (fun _ h => h) b hb ha)
  · exact Or.inl ha

end RiemannResearch.RH.Pareto.CoupledResidual
