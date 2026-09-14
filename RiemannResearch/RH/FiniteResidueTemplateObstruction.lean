import RiemannResearch.RH.FiniteSeedMellinObstruction
import RiemannResearch.RH.ThresholdHilbertCocycle
import RiemannResearch.RH.ThresholdJointAdjointRigidity
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# No fixed finite full-remainder template approximates the constant

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 6. This extends the existing two-seed coefficient theorem to the
entire finite positive remainder span. Analytic zero persistence, finite
phase recurrence, the actual Mellin identity and continuity are imported
proved theorems; no RH or unproved provider is assumed.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- The actual finite remainder packet with a finite index set. -/
def finiteResidueTemplate {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (u : ι → ℝ) : ThresholdHilbert :=
  ∑ i, u i • digitHilbert (d i) 1 (hd i) (by omega)

theorem finiteResidueTemplate_mellin {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (u : ι → ℝ)
    (s : ℂ) (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    paretoMellin (finiteResidueTemplate d hd u) s =
      riemannZeta s / s * ∑ i, (u i : ℂ) * (1 - (d i : ℂ) ^ (1-s)) := by
  change paretoMellinContinuous s hs (∑ i, u i • digitHilbert (d i) 1 (hd i) _) = _
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change (u i : ℂ) * paretoMellin (digitHilbert (d i) 1 (hd i) _) s = _
  rw [paretoMellin_residue_zeta (d i) (hd i) s (by linarith) hs1]
  ring

theorem finiteResidueTemplate_has_mellin_zero {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (u : ι → ℝ) :
    ∃ s : ℂ, (1/2 : ℝ) < s.re ∧ s.im ≠ 0 ∧
      paretoMellin (finiteResidueTemplate d hd u) s = 0 := by
  classical
  let a : ι ⊕ ι → ℂ := Sum.elim (fun i => (u i : ℂ)) (fun i => -(u i : ℂ))
  let freq : ι ⊕ ι → ℝ := Sum.elim (fun _ => 0) (fun i => -Real.log (d i))
  have hrepr (s : ℂ) : Analysis.finiteExponentialPolynomial a freq s =
      ∑ i, (u i : ℂ) * (1 - (d i : ℂ) ^ (1-s)) := by
    unfold Analysis.finiteExponentialPolynomial
    rw [Fintype.sum_sum_type]
    simp only [a, freq, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, mul_one]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hdi : (d i : ℂ) ≠ 0 := by exact_mod_cast (hd i).ne'
    have he : Complex.exp (((-Real.log (d i) : ℝ) : ℂ) * (s-1)) =
        (d i : ℂ) ^ (1-s) := by
      rw [Complex.cpow_def_of_ne_zero hdi, ← Complex.natCast_log]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  have hone : Analysis.finiteExponentialPolynomial a freq 1 = 0 := by
    rw [hrepr]
    simp
  obtain ⟨s, hs, him, hz⟩ := Analysis.finiteExponentialPolynomial_nonreal_zero a freq hone
  refine ⟨s, hs, him, ?_⟩
  have hs1 : s ≠ 1 := by intro he; apply him; simp [he]
  rw [finiteResidueTemplate_mellin d hd u s hs hs1, ← hrepr, hz, mul_zero]

theorem finiteResidueTemplate_not_cyclic {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i) (u : ι → ℝ) :
    hilbertOne ∉ singleSeedDilationClosure (finiteResidueTemplate d hd u) := by
  obtain ⟨s, hs, _, hz⟩ := finiteResidueTemplate_has_mellin_zero d hd u
  exact hilbertOne_not_mem_singleSeedClosure_of_mellin _ s hs hz

/-- All full-remainder finite templates have an actual Mellin annihilator. -/
theorem fullResidueSpan_has_mellin_zero (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace {n : ℕ | 0 < n}) :
    ∃ s : ℂ, (1/2 : ℝ) < s.re ∧ s.im ≠ 0 ∧ paretoMellin f s = 0 := by
  classical
  let v : {n : ℕ // 0 < n} → ThresholdHilbert :=
    fun n => digitHilbert n.1 1 n.2 (by omega)
  let S : Submodule ℝ ThresholdHilbert := Submodule.span ℝ (Set.range v)
  have hspan : legalSeedSpan {n : ℕ | 0 < n} ≤ S.map hilbertSequenceLinear := by
    rw [legalSeedSpan_positive_eq_residue_span]
    apply Submodule.span_le.mpr
    rintro g ⟨m, hm, rfl⟩
    refine ⟨v ⟨m, hm⟩, Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩, ?_⟩
    change hilbertSequence (digitHilbert m 1 hm _) = residue m
    rw [hilbertSequence_digitHilbert]
    funext k
    simp [digitSequence, residue]
  obtain ⟨w, hw, hwf⟩ := hspan hf
  have he : w = f := hilbertSequence_injective hwf
  subst w
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hw
  let d : c.support → ℕ := fun i => i.1.1
  let hd : ∀ i : c.support, 0 < d i := fun i => i.1.2
  let u : c.support → ℝ := fun i => c i.1
  have heq : c.sum (fun i a => a • v i) = finiteResidueTemplate d hd u := by
    change (∑ n ∈ c.support, c n • v n) = ∑ i : c.support, c i.1 • v i.1
    exact (Finset.sum_coe_sort c.support (fun n => c n • v n)).symm
  rw [heq]
  exact finiteResidueTemplate_has_mellin_zero d hd u

/-- Even the full finite remainder space contains no single cyclic template. -/
theorem fullResidueSpan_not_cyclic (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace {n : ℕ | 0 < n}) :
    hilbertOne ∉ singleSeedDilationClosure f := by
  obtain ⟨s, hs, _, hz⟩ := fullResidueSpan_has_mellin_zero f hf
  exact hilbertOne_not_mem_singleSeedClosure_of_mellin f s hs hz

theorem fullResidueSpan_positive_distance_gap (f : ThresholdHilbert)
    (hf : f ∈ hilbertLegalSubspace {n : ℕ | 0 < n}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ singleSeedDilationClosure f,
      δ ≤ ‖hilbertOne - g‖ ^ 2 := by
  obtain ⟨s, hs, _, hz⟩ := fullResidueSpan_has_mellin_zero f hf
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  refine ⟨(2 * s.re - 1) / ‖s‖ ^ 2, ?_, ?_⟩
  · exact div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hs0))
  · intro g hg
    exact singleSeedClosure_distance_sq_lower_bound f s hs hz hg

/-- A fixed ratio between the two seeds cannot be retained across all dilations. -/
theorem fixed_two_seed_mixture_not_cyclic (α β : ℝ) :
    hilbertOne ∉ singleSeedDilationClosure
      (α • digitHilbert 2 1 (by norm_num) (by norm_num) +
        β • digitHilbert 3 1 (by norm_num) (by norm_num)) := by
  let d : Fin 2 → ℕ := fun i => if i = 0 then 2 else 3
  let hd : ∀ i, 0 < d i := by intro i; dsimp [d]; split <;> omega
  let u : Fin 2 → ℝ := fun i => if i = 0 then α else β
  simpa [finiteResidueTemplate, Fin.sum_univ_two, d, hd, u] using
    finiteResidueTemplate_not_cyclic d hd u

/-- Exactly two fixed finite templates are optimal, conditional only on full
remainder density: the explicit templates R₂,R₃ suffice, while every single
fixed finite template from the larger full remainder span fails. This does
not assume or assert the unformalized RH-to-full-density provider. -/
theorem two_finite_templates_optimal_of_full_density
    (hfull : hilbertLegalClosure {n : ℕ | 0 < n} = ⊤) :
    hilbertOne ∈ hilbertLegalClosure {2, 3} ∧
      ∀ f ∈ hilbertLegalSubspace {n : ℕ | 0 < n},
        hilbertOne ∉ singleSeedDilationClosure f := by
  constructor
  · rw [twoSeed_legalClosure_eq_top_of_full_density hfull]
    trivial
  · exact fullResidueSpan_not_cyclic

end
end RiemannResearch.RH.Pareto
