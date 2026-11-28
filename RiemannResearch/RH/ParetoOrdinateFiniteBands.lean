import RiemannResearch.RH.ParetoOrdinateHeightBands
import RiemannResearch.RH.IntegerDPPGramDeterminant
import RiemannResearch.RH.IntegerDPPMellinObstruction

/-! # Finite residue Gram matrices on separated ordinate-height bands

The rank of the legal residue projection may tend to infinity at any rate.
For the original ordinate rows or the finite centered Landau estimators,
the first physical kernel entry is 32 times the limiting inverse-Gram pairing
of the two band loads. Reaching the ambient value 1/32 is equivalent to RH.
-/

noncomputable section
open Filter Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.OrdinateCosine
open CoefficientStabilization RiemannResearch.Analysis

/-- Cofinal finite residual projections preserve the limit of a strongly convergent estimator. -/
theorem moving_residual_tendsto {F : ℝ → ThresholdHilbert} {v : ThresholdHilbert}
    (hF : Tendsto F atTop (𝓝 v)) {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop) :
    Tendsto (fun T => (finiteSpace (rank T))ᗮ.starProjection (F T)) atTop
      (𝓝 (closedSpaceᗮ.starProjection v)) := by
  have hfixed : Tendsto (fun n => (finiteSpace n)ᗮ.starProjection v) atTop
      (𝓝 (closedSpaceᗮ.starProjection v)) := by
    simp only [Submodule.starProjection_orthogonal_val]
    exact tendsto_const_nhds.sub
      (RiemannResearch.Analysis.ExhaustiveWalk.walkProjection_tendsto
        residueAtom id Function.surjective_id v)
  have hsmall : Tendsto (fun T => (finiteSpace (rank T))ᗮ.starProjection (F T - v))
      atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun T => (finiteSpace (rank T))ᗮ.norm_starProjection_apply_le (F T - v))
      (tendsto_iff_norm_sub_tendsto_zero.mp hF)
  simpa only [Function.comp_def, zero_add, map_sub, sub_add_cancel] using
    hsmall.add (hfixed.comp hr)

/-- Both residuals use only the first n legal residue vectors. -/
def finiteSeparatedGram (F : ℝ → ThresholdHilbert) (n : ℕ) (T : ℝ) : ℝ :=
  inner ℝ ((finiteSpace n)ᗮ.starProjection (heightBand F (1/4) (1/2) T))
    ((finiteSpace n)ᗮ.starProjection (heightBand F (3/4) 1 T))

/-- The legal rank can increase at any rate with height. -/
theorem finiteSeparatedGram_tendsto {F : ℝ → ThresholdHilbert}
    (hF : Tendsto F atTop (𝓝 (paretoPointHilbert 0)))
    {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop) :
    Tendsto (fun T => finiteSeparatedGram F (rank T) T) atTop
      (𝓝 ((1 - IntegerDPP.limitingKernel 0 0) / 32)) := by
  have hL := moving_residual_tendsto (heightBand_tendsto hF
    (show (0 : ℝ) < 1/4 by norm_num) (show (0 : ℝ) < 1/2 by norm_num)) hr
  have hR := moving_residual_tendsto (heightBand_tendsto hF
    (show (0 : ℝ) < 3/4 by norm_num) (show (0 : ℝ) < 1 by norm_num)) hr
  have h := hL.inner (𝕜 := ℝ) hR
  have hq (x : ℝ) : (1-3/4 : ℝ) * ((1/2-1/4) * (x/2)) = x/32 := by ring
  simpa only [finiteSeparatedGram, map_smul, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, first_site_residual_sq, hq] using h

theorem rh_iff_finiteSeparatedGram_liminf {F : ℝ → ThresholdHilbert}
    (hF : Tendsto F atTop (𝓝 (paretoPointHilbert 0)))
    {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop) :
    RiemannHypothesis ↔ liminf (fun T => finiteSeparatedGram F (rank T) T) atTop ≤ 0 := by
  rw [(finiteSeparatedGram_tendsto hF hr).liminf_eq, rh_iff_first_site_vacancy_zero]
  have hn : 0 ≤ (1 - IntegerDPP.limitingKernel 0 0) / 2 := by
    rw [← first_site_residual_sq]
    exact sq_nonneg _
  constructor <;> intro h <;> linarith only [h, hn]

/-- An arithmetic test using finite Landau heads and a finite legal Gram projection. -/
theorem rh_iff_landau_finite_band :
    RiemannHypothesis ↔
      liminf (fun T : ℝ => finiteSeparatedGram (fun U => landauHead U ⌊U⌋₊) ⌊T⌋₊ T)
        atTop ≤ 0 := by
  apply rh_iff_finiteSeparatedGram_liminf landauHead_tendsto_of_ingham
  apply tendsto_atTop.mpr
  intro n
  filter_upwards [eventually_ge_atTop (n : ℝ)] with T hT
  exact Nat.le_floor hT

/-- Any single zero right of the critical line forces a persistent positive band signal. -/
theorem finiteSeparatedGram_positive_of_right_zero {F : ℝ → ThresholdHilbert}
    (hF : Tendsto F atTop (𝓝 (paretoPointHilbert 0)))
    {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop)
    (s : ℂ) (hs : (1/2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ∀ᶠ T in atTop, IntegerDPP.mellinVacancyFloor s / 64 < finiteSeparatedGram F (rank T) T := by
  have hfloor := IntegerDPP.mellinVacancyFloor_le_limitingVacancy s hs hs1 hz
  rw [IntegerDPP.limitingVacancy_eq_kernel_complement] at hfloor
  have hp := IntegerDPP.mellinVacancyFloor_pos s hs
  exact (finiteSeparatedGram_tendsto hF hr).eventually_const_lt (by linarith only [hp, hfloor])

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.rh_iff_landau_finite_band' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_landau_finite_band

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.finiteSeparatedGram_positive_of_right_zero' depends
on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finiteSeparatedGram_positive_of_right_zero

/-- Complete finite Gram formula for the signed residual, including both load vectors. -/
theorem finite_residual_inverseGram (n : ℕ) (x y : ThresholdHilbert) :
    inner ℝ ((finiteSpace n)ᗮ.starProjection x) ((finiteSpace n)ᗮ.starProjection y) =
      inner ℝ x y - dotProduct (FiniteHilbertGram.cross (fun i : Fin n => residueAtom i.val) x)
        ((IntegerDPP.fullGram n)⁻¹.mulVec
          (FiniteHilbertGram.cross (fun i : Fin n => residueAtom i.val) y)) := by
  have hp (S : Submodule ℝ ThresholdHilbert) [S.HasOrthogonalProjection] :
      inner ℝ (S.starProjection x) (S.starProjection y) = inner ℝ x (S.starProjection y) := by
    rw [S.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem y)]
  have hG : inner ℝ ((finiteSpace n).starProjection x) ((finiteSpace n).starProjection y) =
      dotProduct (FiniteHilbertGram.cross (fun i : Fin n => residueAtom i.val) x)
        ((IntegerDPP.fullGram n)⁻¹.mulVec
          (FiniteHilbertGram.cross (fun i : Fin n => residueAtom i.val) y)) :=
    FiniteHilbertGram.projection_inner_eq_inverseGram (TailCapacity.finiteAtom_independent n) x y
  rw [hp (finiteSpace n)ᗮ, Submodule.starProjection_orthogonal_val, inner_sub_right,
    ← hp (finiteSpace n), hG]


/-- Arithmetic captured correlation for the two quarter intervals. -/
def finiteBandCapture (F : ℝ → ThresholdHilbert) (n : ℕ) (T : ℝ) : ℝ :=
  let v := fun i : Fin n => residueAtom i.val
  dotProduct (FiniteHilbertGram.cross v (heightBand F (1/4) (1/2) T))
    ((IntegerDPP.fullGram n)⁻¹.mulVec (FiniteHilbertGram.cross v (heightBand F (3/4) 1 T)))

theorem finiteSeparatedGram_eq_sub_capture (F : ℝ → ThresholdHilbert) (n : ℕ) (T : ℝ) :
    finiteSeparatedGram F n T =
      inner ℝ (heightBand F (1/4) (1/2) T) (heightBand F (3/4) 1 T) -
        finiteBandCapture F n T :=
  finite_residual_inverseGram n _ _

/-- The first-site kernel is 32 times the limiting finite inverse-Gram correlation. -/
theorem finiteBandCapture_tendsto {F : ℝ → ThresholdHilbert}
    (hF : Tendsto F atTop (𝓝 (paretoPointHilbert 0)))
    {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop) :
    Tendsto (fun T => finiteBandCapture F (rank T) T) atTop
      (𝓝 (IntegerDPP.limitingKernel 0 0 / 32)) := by
  have hL := heightBand_tendsto hF
    (show (0 : ℝ) < 1/4 by norm_num) (show (0 : ℝ) < 1/2 by norm_num)
  have hR := heightBand_tendsto hF
    (show (0 : ℝ) < 3/4 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have ha : Tendsto
      (fun T => inner ℝ (heightBand F (1/4) (1/2) T) (heightBand F (3/4) 1 T))
      atTop (𝓝 (1 / 32)) := by
    have hq : (1-3/4 : ℝ) * ((1/2-1/4) * (1/2)) = 1/32 := by norm_num
    simpa only [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
      TailCapacity.firstPoint_norm_sq, hq] using hL.inner (𝕜 := ℝ) hR
  have ht := ha.sub (finiteSeparatedGram_tendsto hF hr)
  have he (x : ℝ) : (1/32 : ℝ) - (1-x)/32 = x/32 := by ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards with T
  change inner ℝ (heightBand F (1/4) (1/2) T) (heightBand F (3/4) 1 T) -
    finiteSeparatedGram F (rank T) T = finiteBandCapture F (rank T) T
  rw [finiteSeparatedGram_eq_sub_capture]
  ring

theorem rh_iff_finiteBandCapture_limsup {F : ℝ → ThresholdHilbert}
    (hF : Tendsto F atTop (𝓝 (paretoPointHilbert 0)))
    {rank : ℝ → ℕ} (hr : Tendsto rank atTop atTop) :
    RiemannHypothesis ↔ 1/32 ≤ limsup (fun T => finiteBandCapture F (rank T) T) atTop := by
  rw [(finiteBandCapture_tendsto hF hr).limsup_eq, rh_iff_first_site_vacancy_zero]
  have hn : 0 ≤ (1 - IntegerDPP.limitingKernel 0 0) / 2 := by
    rw [← first_site_residual_sq]
    exact sq_nonneg _
  constructor <;> intro h <;> linarith only [h, hn]

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.rh_iff_finiteBandCapture_limsup' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_finiteBandCapture_limsup

end RiemannResearch.RH.Pareto.OrdinateCosine
