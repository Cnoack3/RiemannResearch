import RiemannResearch.RH.CanonicalMobiusTailNondegeneracy
import RiemannResearch.Analysis.FiniteGramAffineMinimum
import RiemannResearch.Analysis.FiniteGramRange

/-!
# Attained signed-covariance minimum for canonical Möbius families

Source: user-provided Pareto direct-attempt handoff, Sections 7 and 9.
The complete infinite tail Gram form is used. Finite periodicity supplies
normal-equation solvability even when its coefficient matrix is singular.
The asymptotic capacity lower bound remains an explicit research hypothesis.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
open RiemannResearch.Analysis.FiniteHilbertGram

variable {ι : Type*} [Fintype ι]

def combination (k : ι → ℕ) (c : ι → ℝ) : ThresholdHilbert :=
  Fintype.linearCombination ℝ (fun i => canonicalMobiusHilbert (k i)) c

def tailFamily (N : ℕ) (k : ι → ℕ) (i : ι) : ThresholdHilbert :=
  hilbertTailShift (canonicalMobiusHilbert (k i)) N

theorem combination_sequence (k : ι → ℕ) (c : ι → ℝ) (j : ℕ) :
    hilbertSequence (combination k c) j = ∑ i, c i * canonicalMobiusHead (k i) j := by
  change hilbertSequenceLinear (combination k c) j = _
  simp only [combination, Fintype.linearCombination_apply, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, c i * hilbertSequence (canonicalMobiusHilbert (k i)) j) = _
  simp_rw [canonicalMobiusHilbert_sequence]

theorem combination_mem_finiteSpace (k : ι → ℕ) (c : ι → ℝ) :
    combination k c ∈ finiteSpace (Finset.univ.sup k) := by
  classical
  unfold combination
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id
    (Finset.le_sup (f := k) hi) (canonicalMobiusHilbert_mem_finiteSpace (k i))

theorem combination_mem_closedSpace (k : ι → ℕ) (c : ι → ℝ) :
    combination k c ∈ closedSpace := by
  unfold combination
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro i hi
  exact closedSpace.smul_mem (c i) (canonicalMobiusHilbert_mem_closedSpace (k i))

theorem combination_exact (N : ℕ) (k : ι → ℕ) (c : ι → ℝ)
    (hk : ∀ i, N ≤ k i) (hc : ∑ i, c i = 1)
    (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) :
    hilbertSequence (combination k c) j = 1 := by
  rw [combination_sequence]
  simpa only [canonicalMobiusHead_exact (k _) j hj (hjN.trans (hk _)), mul_one] using hc

theorem combination_tail (N : ℕ) (k : ι → ℕ) (c : ι → ℝ) :
    hilbertTailShift (combination k c) N =
      Fintype.linearCombination ℝ (tailFamily N k) c := by
  change hilbertTailShiftLinear N (combination k c) = _
  simp only [combination, Fintype.linearCombination_apply, map_sum, map_smul]
  rfl

theorem tail_synthesis_kernel_sum (N : ℕ) (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) (c : ι → ℝ)
    (hc : Fintype.linearCombination ℝ (tailFamily N k) c = 0) :
    ∑ i, c i = 0 := by
  have ht : hilbertTailShift (combination k c) N = 0 := by
    rw [combination_tail, hc]
  have hz := finiteSpace_first_eq_zero_of_tailShift_eq_zero
    (Finset.univ.sup k) N _ (combination_mem_finiteSpace k c) ht
  rw [combination_sequence] at hz
  have he : (∑ i, c i * canonicalMobiusHead (k i) 1) = ∑ i, c i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [canonicalMobiusHead_exact (k i) 1 (by omega) (hk i), mul_one]
  rwa [he] at hz

theorem tail_energy_expansion (N : ℕ) (k : ι → ℕ) (c : ι → ℝ) :
    ‖Fintype.linearCombination ℝ (tailFamily N k) c‖ ^ 2 =
      ∑ i, ∑ j, c i * c j * canonicalMobiusTailCovariance N (k i) (k j) := by
  rw [gram_quadratic]
  simp_rw [gram_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change c i * (canonicalMobiusTailCovariance N (k i) (k j) * c j) = _
  ring

/-- The actual full-tail normal equations are solvable without an inverse premise. -/
theorem normal_exists (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i) :
    ∃ z, gram (tailFamily N k) z = fun _ => 1 :=
  exists_gram_eq_one_of_synthesis_null_sum_zero (tailFamily N k)
    (tail_synthesis_kernel_sum N k hk)

def normal (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i) : ι → ℝ :=
  Classical.choose (normal_exists N k hk)

theorem normal_equations (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i) :
    gram (tailFamily N k) (normal N k hk) = fun _ => 1 :=
  Classical.choose_spec (normal_exists N k hk)

/-- The scalar `1ᵀ C† 1`, defined through an actual solution `C z = 1`.
No choice of generalized-inverse convention is required. -/
def capacity (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i) : ℝ :=
  ∑ i, normal N k hk i

theorem capacity_eq_sum_of_normal (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (z : ι → ℝ) (hz : gram (tailFamily N k) z = fun _ => 1) :
    capacity N k hk = ∑ i, z i :=
  normal_mass_unique _ _ _ (normal_equations N k hk) hz

variable [Nonempty ι]

theorem capacity_pos (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i) :
    0 < capacity N k hk :=
  normal_mass_pos _ _ (normal_equations N k hk)

def optimizedAverage (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i) : ThresholdHilbert :=
  combination k (affineCoefficients (normal N k hk))

omit [Nonempty ι] in
theorem optimizedAverage_mem_closedSpace (N : ℕ) (k : ι → ℕ)
    (hk : ∀ i, 0 < k i) : optimizedAverage N k hk ∈ closedSpace :=
  combination_mem_closedSpace _ _

theorem optimizedAverage_exact (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (hindex : ∀ i, N ≤ k i) (j : ℕ) (hj : 0 < j) (hjN : j ≤ N) :
    hilbertSequence (optimizedAverage N k hk) j = 1 :=
  combination_exact N k _ hindex
    (affineCoefficients_sum _ _ (normal_equations N k hk)) j hj hjN

theorem optimizedAverage_tail_energy (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i) :
    ‖hilbertTailShift (optimizedAverage N k hk) N‖ ^ 2 = (capacity N k hk)⁻¹ := by
  unfold optimizedAverage
  rw [combination_tail, affineCoefficients_energy _ _ (normal_equations N k hk)]
  rfl

/-- Exact full norm of the attained signed-average optimizer. -/
theorem optimizedAverage_norm_sq (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (hindex : ∀ i, N ≤ k i) :
    ‖optimizedAverage N k hk‖ ^ 2 = (N : ℝ) / ((N : ℝ) + 1) +
      (capacity N k hk)⁻¹ := by
  rw [exact_head_norm_sq_split _ N (optimizedAverage_exact N k hk hindex),
    optimizedAverage_tail_energy]

/-- The actual finite covariance minimum is attained, including the singular case. -/
theorem covariance_isLeast (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i) :
    IsLeast {E : ℝ | ∃ c : ι → ℝ, (∑ i, c i) = 1 ∧
      (∑ i, ∑ j, c i * c j * canonicalMobiusTailCovariance N (k i) (k j)) = E}
      (capacity N k hk)⁻¹ := by
  have h := affineCoefficients_isLeast (tailFamily N k) (normal N k hk)
    (normal_equations N k hk)
  simpa only [tail_energy_expansion, capacity] using h

/-- Conditional research reduction: a cofinal positive lower bound on the
actual normal capacity gives RH. The capacity bound is the open provider. -/
theorem riemannHypothesis_of_capacity_frequently_ge
    {I : ℕ → Type*} [∀ N, Fintype (I N)] [∀ N, Nonempty (I N)]
    (k : ∀ N, I N → ℕ) (hk : ∀ N i, 0 < k N i)
    (hindex : ∀ N i, N ≤ k N i)
    (ε : ℝ) (hε : 0 < ε)
    (hbound : ∃ᶠ N in atTop, ε ≤ capacity N (k N) (hk N)) : RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_bounded_exact_head_energy
    (fun N => optimizedAverage N (k N) (hk N))
    (fun N => optimizedAverage_mem_closedSpace N (k N) (hk N))
    (fun N => optimizedAverage_exact N (k N) (hk N) (hindex N)) (1 + ε⁻¹)
  apply hbound.mono
  intro N hN
  rw [optimizedAverage_norm_sq N (k N) (hk N) (hindex N)]
  have hhead : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).2
    linarith
  have hinv : (capacity N (k N) (hk N))⁻¹ ≤ ε⁻¹ :=
    (inv_le_inv₀ (capacity_pos N (k N) (hk N)) hε).2 hN
  linarith

/-- Failure of RH forces every such growing finite-family capacity to vanish.
Finite-stage strict positivity supplies no uniform lower bound. -/
theorem capacity_tendsto_zero_of_not_RH
    {I : ℕ → Type*} [∀ N, Fintype (I N)] [∀ N, Nonempty (I N)]
    (k : ∀ N, I N → ℕ) (hk : ∀ N i, 0 < k N i)
    (hindex : ∀ N i, N ≤ k N i) (hRH : ¬ RiemannHypothesis) :
    Tendsto (fun N => capacity N (k N) (hk N)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hn : ¬ (∃ᶠ N in atTop, ε ≤ capacity N (k N) (hk N)) := by
    intro hb
    exact hRH (riemannHypothesis_of_capacity_frequently_ge k hk hindex ε hε hb)
  have he : ∀ᶠ N in atTop, capacity N (k N) (hk N) < ε := by
    simpa only [not_frequently, not_le] using hn
  filter_upwards [he] with N hN
  simpa only [Real.dist_eq, sub_zero, abs_of_pos (capacity_pos N (k N) (hk N))] using hN


section FamilyMonotonicity
variable {κ : Type*} [Fintype κ] [Nonempty κ]

/-- Adding indices to an actual finite signed-covariance family cannot decrease
its capacity. Neither family is required to have an invertible Gram matrix. -/
theorem capacity_mono_of_family_map
    (N : ℕ) (k : ι → ℕ) (l : κ → ℕ)
    (hk : ∀ i, 0 < k i) (hl : ∀ j, 0 < l j)
    (e : ι → κ) (he : ∀ i, k i = l (e i)) :
    capacity N k hk ≤ capacity N l hl := by
  unfold capacity
  apply normal_mass_mono_of_family_map
    (tailFamily N k) (tailFamily N l) (normal N k hk) (normal N l hl)
    (normal_equations N k hk) (normal_equations N l hl) e
  intro i
  simp only [tailFamily, he i]

end FamilyMonotonicity

/-- Every affine coefficient choice bounds the inverse actual capacity. -/
theorem capacity_inv_le_tail_energy
    (N : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (c : ι → ℝ) (hc : ∑ i, c i = 1) :
    (capacity N k hk)⁻¹ ≤ ‖hilbertTailShift (combination k c) N‖ ^ 2 := by
  rw [combination_tail]
  exact (affineCoefficients_isLeast (tailFamily N k) (normal N k hk)
    (normal_equations N k hk)).2 ⟨c, hc, rfl⟩

/-- For a fixed family exact through K, changing the tail cutoff from N to K
subtracts only the common deterministic head energy from the affine minimum.
No invertibility or linear independence premise is used. -/
theorem capacity_inv_cutoff_identity
    (N K : ℕ) (hNK : N ≤ K) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (hindex : ∀ i, K ≤ k i) :
    (capacity N k hk)⁻¹ = (capacity K k hk)⁻¹ +
      (K : ℝ) / ((K : ℝ) + 1) - (N : ℝ) / ((N : ℝ) + 1) := by
  have hindexN : ∀ i, N ≤ k i := fun i => hNK.trans (hindex i)
  have hNmin := capacity_inv_le_tail_energy N k hk
    (affineCoefficients (normal K k hk))
    (affineCoefficients_sum (tailFamily K k) (normal K k hk)
      (normal_equations K k hk))
  change (capacity N k hk)⁻¹ ≤
    ‖hilbertTailShift (optimizedAverage K k hk) N‖ ^ 2 at hNmin
  have hKmin := capacity_inv_le_tail_energy K k hk
    (affineCoefficients (normal N k hk))
    (affineCoefficients_sum (tailFamily N k) (normal N k hk)
      (normal_equations N k hk))
  change (capacity K k hk)⁻¹ ≤
    ‖hilbertTailShift (optimizedAverage N k hk) K‖ ^ 2 at hKmin
  have hheadNK : ∀ j, 0 < j → j ≤ K →
      hilbertSequence (optimizedAverage N k hk) j = 1 := by
    intro j hj hjK
    exact combination_exact K k (affineCoefficients (normal N k hk)) hindex
      (affineCoefficients_sum (tailFamily N k) (normal N k hk)
        (normal_equations N k hk)) j hj hjK
  have hheadKN : ∀ j, 0 < j → j ≤ N →
      hilbertSequence (optimizedAverage K k hk) j = 1 := by
    intro j hj hjN
    exact optimizedAverage_exact K k hk hindex j hj (hjN.trans hNK)
  have hnormN := optimizedAverage_norm_sq N k hk hindexN
  have hnormK := optimizedAverage_norm_sq K k hk hindex
  have hsplitN := exact_head_norm_sq_split (optimizedAverage N k hk) K hheadNK
  have hsplitK := exact_head_norm_sq_split (optimizedAverage K k hk) N hheadKN
  linarith
end RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
