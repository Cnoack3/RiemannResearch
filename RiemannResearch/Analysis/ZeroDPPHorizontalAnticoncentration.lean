import RiemannResearch.Analysis.ZeroDPPHorizontalVariance
import RiemannResearch.Analysis.MontgomeryFejerCertificate
import RiemannResearch.Probability.ZeroOrdinateDPPVisibility
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Linarith

/-!
# A persistent small-interval obstruction from one off-line zero

Any permutation of multiplicity labels preserving ordinates preserves the DPP
law. Swapping two such labels changes a linear statistic by the difference of
their coefficients whenever exactly one is selected. Two coefficients separated
by twice a radius force a fixed amount of probability outside every open
interval of that radius. Horizontal reflection and the unit-shell inclusion
bound make this obstruction uniform in the height and in the frequency list.
-/

noncomputable section
open MeasureTheory Filter Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
open RiemannResearch.Analysis ActualZeroOrdinate

/-- Relabel the Boolean configuration by an ordinate-preserving permutation. -/
theorem measurePreserving_relabel (q : ℕ → ℝ) (σ : Site ≃ Site)
    (hσ : ∀ i, ordinate (σ i) = ordinate i) :
    MeasurePreserving (fun (x : Site → Bool) i => x (σ i)) (limitingLaw q) (limitingLaw q) := by
  classical
  let μ := limitingLaw q
  let F := fun (x : Site → Bool) i => x (σ i)
  have hm : Measurable F := measurable_pi_lambda _ fun i => measurable_pi_apply (σ i)
  refine ⟨hm, ?_⟩
  let : IsProbabilityMeasure (μ.map F) := Measure.isProbabilityMeasure_map hm.aemeasurable
  change μ.map F = μ
  apply boolLaw_unique _ (limitingLaw_isDPP q)
  constructor
  · intro i
    exact (measurableSet_singleton true).preimage (measurable_pi_apply i)
  · intro m e
    let A := {x : Site → Bool | ∀ k, x (e k) = true}
    have hA : MeasurableSet A := by
      simp only [A, Set.ofPred_forall]
      exact MeasurableSet.iInter fun k => (limitingLaw_isDPP q).measurable_occupancy (e k)
    change ((μ.map F) A).toReal = _
    rw [Measure.map_apply hm hA]
    let e' := e.trans σ.toEmbedding
    have h := (limitingLaw_isDPP q).correlation m e'
    change μ.real (F ⁻¹' A) = Matrix.det (Matrix.of
      (fun k l => limitingKernel q (σ (e k)) (σ (e l)))) at h
    have hk (i j : Site) : limitingKernel q (σ i) (σ j) = limitingKernel q i j := by
      simp only [limitingKernel, kernelOfSpace, ProjectionDPP.kernel,
        collision_projection_eq q (hσ i), collision_projection_eq q (hσ j)]
    simpa only [Measure.real, hk] using h

private theorem measurable_sampleLinear (q : ℕ → ℝ) (T : ℝ) (w : Copies T → ℝ) :
    Measurable (linearStatistic (fun x : Site → Bool => {j | x j = true}) (liftCopy T) w) := by
  apply Finset.measurable_fun_sum
  intro c _
  exact measurable_const.mul (measurable_const.indicator ((limitingLaw_isDPP q).measurable_occupancy _))

private theorem linear_difference_swap (T : ℝ) (c d : Copies T) (hcd : c ≠ d)
    (w : Copies T → ℝ) (x : Site → Bool) :
    let σ := Equiv.swap (liftCopy T c) (liftCopy T d)
    let S := linearStatistic (fun x : Site → Bool => {j | x j = true}) (liftCopy T) w
    S x - S (fun i => x (σ i)) = (w c - w d) *
      ((if x (liftCopy T c) = true then (1 : ℝ) else 0) -
        (if x (liftCopy T d) = true then (1 : ℝ) else 0)) := by
  classical
  let e := liftCopy T
  let σ := Equiv.swap (e c) (e d)
  let o := fun i : Site => if x i = true then (1 : ℝ) else 0
  change (∑ k, w k * occupancyIndicator _ (e k) x) -
    (∑ k, w k * occupancyIndicator _ (e k) (fun i => x (σ i))) = (w c - w d) * (o (e c) - o (e d))
  have ho (k : Copies T) : occupancyIndicator (fun z : Site → Bool => {j | z j = true}) (e k) x =
      o (e k) := by by_cases h : x (e k) = true <;> simp [occupancyIndicator, o, h]
  have hs (k : Copies T) : occupancyIndicator (fun z : Site → Bool => {j | z j = true}) (e k)
      (fun i => x (σ i)) = o (σ (e k)) := by
    by_cases h : x (σ (e k)) = true <;> simp [occupancyIndicator, o, h]
  simp only [ho, hs, ← Finset.sum_sub_distrib]
  have hterm (k : Copies T) : w k * o (e k) - w k * o (σ (e k)) =
      (if k = c then w c * (o (e c) - o (e d)) else 0) +
      (if k = d then w d * (o (e d) - o (e c)) else 0) := by
    by_cases hc : k = c
    · subst k
      simp [σ, hcd, mul_sub]
    · by_cases hd : k = d
      · subst k
        simp [σ, hcd.symm, mul_sub]
      · simp [σ, hc, hd, Equiv.swap_apply_of_ne_of_ne (e.injective.ne hc) (e.injective.ne hd)]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- Any same-ordinate pair with separated coefficients places at least one
label-inclusion probability outside every open interval of the given radius. -/
theorem linear_tail_lower_of_collision (q : ℕ → ℝ) (T : ℝ) (c d : Copies T) (hcd : c ≠ d)
    (hord : copyOrdinate T c = copyOrdinate T d) (w : Copies T → ℝ) (r a : ℝ)
    (hsep : 2 * r ≤ |w c - w d|) :
    limitingKernel q (liftCopy T c) (liftCopy T c) ≤
      (limitingLaw q).real {x | r ≤
        |linearStatistic (fun x : Site → Bool => {j | x j = true}) (liftCopy T) w x - a|} := by
  classical
  let i := liftCopy T c
  let j := liftCopy T d
  have hij : i ≠ j := (liftCopy T).injective.ne hcd
  have ho : ordinate i = ordinate j := hord
  let σ := Equiv.swap i j
  let F := fun (x : Site → Bool) k => x (σ k)
  have hp : MeasurePreserving F (limitingLaw q) (limitingLaw q) := by
    apply measurePreserving_relabel
    intro k
    by_cases hi : k = i
    · subst k
      simpa [σ] using ho.symm
    · by_cases hj : k = j
      · subst k
        simpa [σ] using ho
      · simp [σ, Equiv.swap_apply_of_ne_of_ne hi hj]
  let μ := limitingLaw q
  let S := linearStatistic (fun x : Site → Bool => {k | x k = true}) (liftCopy T) w
  let U := {x | r ≤ |S x - a|}
  let A := {x : Site → Bool | x i = true}
  let B := {x : Site → Bool | x j = true}
  have hU : MeasurableSet U := measurableSet_le measurable_const
    (((measurable_sampleLinear q T w).sub measurable_const).abs)
  have hpre : μ.real (F ⁻¹' U) = μ.real U := by
    unfold Measure.real
    rw [← Measure.map_apply hp.measurable hU, hp.map_eq]
  have hsub : A ∪ B ⊆ (U ∪ F ⁻¹' U) ∪ (A ∩ B) := by
    intro x hx
    by_cases hboth : x ∈ A ∩ B
    · exact Or.inr hboth
    · apply Or.inl
      by_contra hn
      have h₁ : |S x - a| < r := lt_of_not_ge (fun h => hn (Or.inl h))
      have h₂ : |S (F x) - a| < r := lt_of_not_ge (fun h => hn (Or.inr h))
      have hsmall : |S x - S (F x)| < 2 * r := abs_lt.mpr
        ⟨by linarith [(abs_lt.mp h₁).1, (abs_lt.mp h₂).2],
         by linarith [(abs_lt.mp h₁).2, (abs_lt.mp h₂).1]⟩
      have hdiff := linear_difference_swap T c d hcd w x
      change S x - S (F x) = (w c - w d) *
        ((if x i = true then (1 : ℝ) else 0) - (if x j = true then (1 : ℝ) else 0)) at hdiff
      change x i = true ∨ x j = true at hx
      change ¬(x i = true ∧ x j = true) at hboth
      rcases hx with hi | hj
      · have hj : x j ≠ true := fun h => hboth ⟨hi, h⟩
        simp [hdiff, hi, hj] at hsmall
        exact (not_lt_of_ge hsep) hsmall
      · have hi : x i ≠ true := fun h => hboth ⟨h, hj⟩
        simp [hdiff, hi, hj] at hsmall
        exact (not_lt_of_ge hsep) ((abs_sub_comm (w d) (w c)) ▸ hsmall)
  have hI : μ.real (A ∩ B) = 0 := collision_pair_probability_zero q hij ho
  have hAB := measureReal_union_add_inter (μ := μ) (s := A)
    (show MeasurableSet B from (limitingLaw_isDPP q).measurable_occupancy j)
  have hA : μ.real A = limitingKernel q i i := (limitingLaw_isDPP q).occupation i
  have hB : μ.real B = limitingKernel q i i := by
    rw [(show μ.real B = limitingKernel q j j from (limitingLaw_isDPP q).occupation j)]
    simp only [limitingKernel, kernelOfSpace, ProjectionDPP.kernel, collision_projection_eq q ho]
  have hub := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  have hu := measureReal_union_le (μ := μ) U (F ⁻¹' U)
  change limitingKernel q i i ≤ μ.real U
  linarith only [hub, hu, hAB, hA, hB, hpre, hI]

end RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

namespace RiemannResearch.Analysis.ZeroDPPHorizontal
open ActualZeroOrdinate ActualZeroCollisionCertificate MontgomeryFormFactor
open RiemannResearch.Probability.DPP RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

/-- A single off-line zero and its reflection force a persistent probability
outside every open interval of radius |Re ρ - 1/2|. The same positive mass
works for all higher cutoffs, all dictionaries, and all centres. -/
theorem persistent_tail_of_offline {H : ℝ} {ρ : ℂ} (hρ : ρ ∈ cutoff H) (hoff : ρ.re ≠ 1 / 2) :
    ∃ p : ℝ, 0 < p ∧ ∀ (T : ℝ), ρ.im ≤ T → ∀ (q : ℕ → ℝ) (a : ℝ),
      p ≤ (limitingLaw q).real {x | |ρ.re - 1 / 2| ≤
        |horizontalStatistic q T (fun _ => 1) x - a|} := by
  classical
  let base : Copies H := ⟨⟨ρ, hρ⟩, ⟨0, multiplicity_pos hρ⟩⟩
  let i := liftCopy H base
  have hi : 0 < ordinate i := (mem_cutoff.mp hρ).2.1
  let n := ⌈ordinate i⌉₊ - 1
  have hceil : 0 < ⌈ordinate i⌉₊ := Nat.ceil_pos.mpr hi
  have hn : n + 1 = ⌈ordinate i⌉₊ := by dsimp [n]; omega
  have hlow : (n : ℝ) < ordinate i := Nat.lt_ceil.mp (by omega : n < ⌈ordinate i⌉₊)
  have hhigh : ordinate i ≤ (n : ℝ) + 1 := by
    have he : (n : ℝ) + 1 = (⌈ordinate i⌉₊ : ℝ) := by exact_mod_cast hn
    rw [he]
    exact Nat.le_ceil _
  let N : ℝ := Ncount n ((n : ℝ) + 1)
  have hunit (q : ℕ → ℝ) : 1 ≤ limitingKernel q i i * N :=
    one_le_kernel_mul_unit_count q n i hlow hhigh
  have hN : 0 < N := by
    by_contra! hn'
    have hzero : N = 0 := le_antisymm hn' (Nat.cast_nonneg _)
    have hu := hunit (fun _ => 0)
    simp only [hzero, mul_zero] at hu
    norm_num at hu
  refine ⟨1 / N, one_div_pos.mpr hN, ?_⟩
  intro T hT q a
  have hρT : ρ ∈ cutoff T := mem_cutoff.mpr ⟨(mem_cutoff.mp hρ).1, (mem_cutoff.mp hρ).2.1, hT⟩
  let c : Copies T := ⟨⟨ρ, hρT⟩, ⟨0, multiplicity_pos hρT⟩⟩
  let d : Copies T := ⟨⟨reflect ρ, reflect_mem hρT⟩, ⟨0, multiplicity_pos (reflect_mem hρT)⟩⟩
  have hcd : c ≠ d := by
    intro h
    have h' := congrArg (fun k : Copies T => k.1.1.re) h
    change ρ.re = (reflect ρ).re at h'
    rw [reflect_re] at h'
    exact hoff (by linarith)
  have ho : copyOrdinate T c = copyOrdinate T d := (reflect_im ρ).symm
  let K := limitingKernel q i i
  have hK : 0 < K := limitingKernel_diagonal_pos q i
  have hle : K ≤ 1 := ((limitingLaw_isDPP q).diagonal_bounds i).2
  have hdK : limitingKernel q (liftCopy T d) (liftCopy T d) = K := by
    have hg : ordinate (liftCopy T d) = ordinate i := ho.symm
    dsimp only [K, limitingKernel, kernelOfSpace, ProjectionDPP.kernel]
    rw [collision_projection_eq q hg]
  let w := fun k : Copies T => (1 * (k.1.1.re - 1 / 2)) /
    Real.sqrt (limitingKernel q (liftCopy T k) (liftCopy T k))
  have hwc : w c = (ρ.re - 1 / 2) / Real.sqrt K := by simp only [w, one_mul]; rfl
  have hwd : w d = -((ρ.re - 1 / 2) / Real.sqrt K) := by
    simp only [w, one_mul, hdK]
    change ((reflect ρ).re - 1 / 2) / Real.sqrt K = _
    rw [reflect_re]
    ring
  have hroot : Real.sqrt K ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hle
  have hsep : 2 * |ρ.re - 1 / 2| ≤ |w c - w d| := by
    rw [hwc, hwd, sub_neg_eq_add, ← two_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_div, abs_of_nonneg (Real.sqrt_nonneg K)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hK)).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hroot (abs_nonneg (ρ.re - 1 / 2))
  have hp : 1 / N ≤ K := (div_le_iff₀ hN).mpr (hunit q)
  exact hp.trans (linear_tail_lower_of_collision q T c d hcd ho w _ a hsep)

/-- Absolute concentration along arbitrarily high cutoffs characterizes RH.
Both the dictionary and the centre of the interval may vary with the height.
This formulation requires no uniform integrability premise. -/
theorem riemannHypothesis_iff_cofinal_interval_concentration (q : ℝ → ℕ → ℝ) :
    RiemannHypothesis ↔ ∀ r : ℝ, 0 < r → ∀ p : ℝ, 0 < p → ∀ H : ℝ,
      ∃ T : ℝ, H ≤ T ∧ ∃ a : ℝ, (limitingLaw (q T)).real
        {x | r ≤ |horizontalStatistic (q T) T (fun _ => 1) x - a|} < p := by
  have hcrit := cofinal_fejer_critical_line_iff_RH.symm.trans cofinal_fejer_critical_line_iff
  constructor
  · intro hRH r hr p hp H
    refine ⟨H, le_rfl, 0, ?_⟩
    have hS (x : Site → Bool) : horizontalStatistic (q H) H (fun _ => 1) x = 0 := by
      unfold horizontalStatistic normalizedMark linearStatistic
      apply Finset.sum_eq_zero
      intro c _
      simp only [one_mul, (hcrit.mp hRH) H c.1.1 c.1.2, sub_self, zero_div, zero_mul]
    simpa only [hS, sub_zero, abs_zero, not_le.mpr hr, Set.setOf_false, measureReal_empty] using hp
  · intro h
    apply hcrit.mpr
    intro H ρ hρ
    by_contra hoff
    obtain ⟨p, hp, hlow⟩ := persistent_tail_of_offline hρ hoff
    obtain ⟨T, hT, a, hsmall⟩ := h |ρ.re - 1 / 2| (abs_pos.mpr (sub_ne_zero.mpr hoff)) p hp ρ.im
    exact (not_lt_of_ge (hlow T hT (q T) a)) hsmall

end RiemannResearch.Analysis.ZeroDPPHorizontal
