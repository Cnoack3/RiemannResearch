import RiemannResearch.RH.QReciprocalFiniteCost
import RiemannResearch.RH.QCanonicalMobiusCostRates
import RiemannResearch.RH.QReciprocalCofinalCost
import RiemannResearch.RH.MertensLeeLeongCriterion

/-!
# An explicit full-conductor regularized minimizer

Conductors 2 through H+1 are retained. The inverse of the complete regularized Gram matrix defines the optimizer. It improves every competitor in that span, including the boundary-corrected Mobius exact-head family. Cofinal and near-linear bounds imply RH, but remain open arithmetic providers.

Research agenda: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Section 9.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QReciprocalFullMinimizer
open ZetaTwoHilbert ZetaTwoProbability QReciprocalMetric QReciprocalCostEquivalence
open QReciprocalFiniteCost QMobiusExactHead
open RiemannResearch.Analysis.FiniteHilbertGram

def fullMinimizer (H : ℕ) (α : ℝ) : QHilbert :=
  minimizer (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) qOne α

def fullValue (H : ℕ) (α : ℝ) : ℝ :=
  ‖D qOne‖^2 -
    dotProduct (load (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) qOne)
      (coefficients (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) qOne α)

theorem fullMinimizer_legal (H : ℕ) (α : ℝ) :
    fullMinimizer H α ∈ QFullResidueProjection.legalSpan :=
  residue_minimizer_legal _ (QFullResidueProjection.conductor_gt_one H) qOne α

private theorem atom_mem (H d : ℕ) (hd : 0 < d) (hle : d ≤ H+1) :
    qResidue d ∈ synthesisSpan
      (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) := by
  by_cases hd1 : d = 1
  · rw [hd1, qResidue_one]
    exact Submodule.zero_mem _
  · apply Submodule.subset_span
    refine ⟨⟨d-2,by omega⟩,?_⟩
    change qResidue (d-2+2) = qResidue d
    congr 1
    omega

theorem exactHead_mem (H : ℕ) :
    exactHead H ∈ synthesisSpan
      (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) := by
  unfold exactHead
  apply Submodule.add_mem
  · apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro d hd
    have h := Finset.mem_Icc.mp hd
    exact Submodule.smul_mem _ _ (atom_mem H d h.1 (by omega))
  · exact Submodule.smul_mem _ _ (atom_mem H (H+1) (by omega) le_rfl)

theorem full_minimum_value (H : ℕ) (α : ℝ) (hα : 0 < α) :
    cost α qOne (fullMinimizer H α) = fullValue H α :=
  minimum_value _ (QResidueTriangular.qResidue_linearIndependent_injective _
    (QFullResidueProjection.conductor_gt_one H)
    (QFullResidueProjection.conductor_injective H)) qOne α hα

theorem fullValue_nonneg (H : ℕ) (α : ℝ) (hα : 0 < α) : 0 ≤ fullValue H α := by
  rw [← full_minimum_value H α hα]
  unfold cost
  positivity

theorem fullValue_le_exactHead (H : ℕ) (α : ℝ) (hα : 0 < α) :
    fullValue H α ≤ cost α qOne (exactHead H) := by
  rw [← full_minimum_value H α hα]
  exact minimizer_le _ (QResidueTriangular.qResidue_linearIndependent_injective _
    (QFullResidueProjection.conductor_gt_one H)
    (QFullResidueProjection.conductor_injective H)) qOne (exactHead H)
    (exactHead_mem H) α hα

theorem fullValue_source_bound (H : ℕ) (hH : 0 < H) :
    fullValue H ((H : ℝ)^2)⁻¹ ≤
      (4/zetaTwo)*((H : ℝ)^2)⁻¹*‖Pareto.canonicalMobiusHilbert H‖^2 := by
  exact (fullValue_le_exactHead H _ (by positivity)).trans
    (QCanonicalMobiusCost.balanced_cost_source_upper H hH)

theorem fullValue_explicit (H : ℕ) (hH : 0 < H) :
    fullValue H ((H : ℝ)^2)⁻¹ ≤ 16/(zetaTwo*(H : ℝ)) :=
  (fullValue_le_exactHead H _ (by positivity)).trans
    (QCanonicalMobiusCost.balanced_cost_explicit H hH)

open RiemannResearch.NumberTheory.PrimeNumberTheorem

theorem fullValue_global_sqrt_log (c : ℝ) (hc : 0 < c)
    (hcE : c < Quantitative.MobiusContour.contourEndpoint) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℕ, 0 < H →
      fullValue H ((H : ℝ)^2)⁻¹ ≤
        12/(zetaTwo*(H : ℝ)^2) + C/(H : ℝ)*Real.exp (-c*Real.sqrt (Real.log (H : ℝ))) := by
  obtain ⟨C,hC,h⟩ := QCanonicalMobiusCost.balanced_cost_global_sqrt_log c hc hcE
  exact ⟨C,hC,fun H hH => (fullValue_le_exactHead H _ (by positivity)).trans (h H hH)⟩

/-- A uniform Mertens envelope bounds the actual minimum at every positive
regularization and every later conductor cutoff. The integer K is the exact head
of the trial, while H controls the full optimization space. -/
theorem fullValue_le_mertens_envelope {K H : ℕ} (hK : 0 < K) (hKH : K ≤ H)
    {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hsmall : ε * (1 + Real.log (1 / ε)) ≤ 1 / 2)
    (hM : ∀ y : ℝ, (K : ℝ) ≤ y → |M y| ≤ ε * y) :
    fullValue H α ≤ (2 / zetaTwo) * (α + 1 / ((K : ℝ) * ((K : ℝ) + 1))) *
      (3 + 260 * (K : ℝ) * (ε * (1 + Real.log (1 / ε)))) := by
  have hspan : synthesisSpan (fun i : Fin K => qResidue (QFullResidueProjection.conductor K i)) ≤
      synthesisSpan (fun i : Fin H => qResidue (QFullResidueProjection.conductor H i)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact atom_mem H _ (Nat.zero_lt_of_lt (QFullResidueProjection.conductor_gt_one K i))
      (by change i.val + 2 ≤ H + 1; omega)
  have henergy := (Pareto.canonicalMobius_energy_of_uniform_mertens_log K hK ε
    hε hεone hsmall hM).2
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hbound : ‖Pareto.canonicalMobiusHilbert K‖ ^ 2 ≤
      3 + 260 * (K : ℝ) * (ε * (1 + Real.log (1 / ε))) := by
    have h := (div_le_iff₀ hKR).mp henergy
    calc
      _ ≤ (3 / (K : ℝ) + 260 * (ε * (1 + Real.log (1 / ε)))) * (K : ℝ) := h
      _ = _ := by field_simp
  rw [← full_minimum_value H α hα]
  exact (minimizer_le _ (QResidueTriangular.qResidue_linearIndependent_injective _
    (QFullResidueProjection.conductor_gt_one H)
    (QFullResidueProjection.conductor_injective H)) qOne (exactHead K)
    (hspan (exactHead_mem K)) α hα).trans
    ((QCanonicalMobiusCost.complete_cost_source_bound K hK α hα.le).trans
      (mul_le_mul_of_nonneg_left hbound (by positivity [zetaTwo_pos])))

open RiemannResearch.Analysis QMertensFirstMoment

/-- The published Lee–Leong estimate implies a complete-minimum bound at the
Vinogradov–Korobov scale. The ordinary Mertens estimate is an explicit premise. -/
theorem fullValue_eventual_vk_of_leeLeong (hLL : LeeLeongMertensEstimate)
    {c : ℝ} (hc : 0 < c) (hcA : c < leeLeongRate) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℕ in atTop,
      fullValue H ((H : ℝ)^2)⁻¹ ≤ 12 / (zetaTwo * (H : ℝ)^2) +
        C / (H : ℝ) * Real.exp (-c * vkProfile (H : ℝ)) := by
  let A := leeLeongRate
  have hA : 0 < A := hc.trans hcA
  obtain ⟨T, hT⟩ := eventually_atTop.mp (mertens_vk_of_leeLeong hLL)
  have hnat := (tendsto_natCast_atTop_atTop : Tendsto (fun H : ℕ => (H : ℝ)) atTop atTop)
  have htop := (vkProfile_tendsto_atTop.comp hnat).const_mul_atTop hA
  let B := (A / (A - c)) * Real.exp (-(c / A))
  have hAc : 0 < A - c := sub_pos.mpr hcA
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(1040 / zetaTwo) * B, by positivity [zetaTwo_pos], ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hnat.eventually (eventually_ge_atTop T),
    hnat.eventually vkProfile_eventually_mono, htop.eventually (eventually_ge_atTop 6)] with H hH hHT hm h6
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  let u := vkProfile (H : ℝ)
  let ε := Real.exp (-A * u)
  have hε : 0 < ε := Real.exp_pos _
  have hAu : 6 ≤ A * u := h6
  have hεone : ε ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hAu])
  have hsmall : ε * (1 + Real.log (1 / ε)) ≤ 1 / 2 := by
    simpa only [ε, neg_mul] using exponential_entropy_small (A*u) hAu
  have hM (y : ℝ) (hy : (H : ℝ) ≤ y) : |M y| ≤ ε * y := by
    have hmy : u ≤ vkProfile y := hm y hy
    have hpow : Real.exp (-A * vkProfile y) ≤ ε :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hmy (neg_nonpos.mpr hA.le))
    exact (by simpa [A] using hT y (hHT.trans hy) : |M y| ≤ Real.exp (-A * vkProfile y) * y).trans
      (mul_le_mul_of_nonneg_right hpow (hHR.le.trans hy))
  have he := exponential_entropy_le_optimal_rate A c u hA hcA
  have hcost := fullValue_source_bound H hH
  have hd := (Pareto.canonicalMobius_energy_of_uniform_mertens_log H hH ε hε hεone hsmall hM).2
  have hE : ‖Pareto.canonicalMobiusHilbert H‖ ^ 2 / (H : ℝ) ≤
      3 / (H : ℝ) + 260 * (B * Real.exp (-c * u)) := by
    exact hd.trans (add_le_add (le_refl (3 / (H : ℝ)))
      (mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 260 by norm_num)))
  calc
    _ ≤ (4 / zetaTwo) * ((H : ℝ)^2)⁻¹ *
        ((3 / (H : ℝ) + 260 * (B * Real.exp (-c * u))) * (H : ℝ)) :=
      hcost.trans (mul_le_mul_of_nonneg_left ((div_le_iff₀ hHR).mp hE)
        (by positivity [zetaTwo_pos]))
    _ = _ := by dsimp [u]; field_simp; ring

theorem riemannHypothesis_of_cofinal_fullValue
    (reg : ℕ → ℝ) (hr : ∀ H, 0 < reg H)
    (hr0 : Tendsto reg atTop (𝓝 0))
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ N, ∃ H, N ≤ H ∧ fullValue H (reg H) ≤ C*reg H) :
    RiemannHypothesis := by
  apply QReciprocalCofinalCost.riemannHypothesis_of_cofinal_cost reg hr hr0
    (fun H => fullMinimizer H (reg H)) (fun H => fullMinimizer_legal H (reg H)) C hC
  intro N
  obtain ⟨H,hH,hb⟩ := h N
  exact ⟨H,hH,by simpa only [full_minimum_value H (reg H) (hr H)] using hb⟩

open QReciprocalRegularizedCriterion

theorem riemannHypothesis_of_near_linear_fullValue
    (h : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ j,
      fullValue (QCanonicalMobiusCost.stage j) (regularizationScale j) ≤
        C*(regularizationScale j)^(1-η)) : RiemannHypothesis := by
  apply riemannHypothesis_of_near_linear_D_cost
    (fun j => fullMinimizer (QCanonicalMobiusCost.stage j) (regularizationScale j))
    (fun j => fullMinimizer_legal _ _)
  intro η hη
  obtain ⟨C,hC,hCj⟩ := h η hη
  refine ⟨C,hC,fun j => ?_⟩
  have hj := hCj j
  rw [← full_minimum_value _ _ (regularizationScale_pos j)] at hj
  simpa only [cost, map_sub, norm_sub_rev] using hj

end RiemannResearch.RH.QReciprocalFullMinimizer
