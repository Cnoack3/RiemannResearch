import RiemannResearch.Analysis.ActualFixedFrequencyLandau
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ActualZeroSublinearEnergy
import RiemannResearch.Probability.CompactMomentConvergence
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.Separation.Connected
import Mathlib.Tactic

/-!
# An angular law of the actual zeta ordinates

The circle has period 2π. Each positive-height zero contributes its analytic
multiplicity. Fixed-strip concentration suffices for weak Haar convergence.
Every open arc is reached at arbitrarily large heights, giving one sequence
of actual zeros for all integer harmonics simultaneously.
Source for the classical equidistribution result: Hlawka (1975), as described
by Ford--Zaharescu, https://arxiv.org/abs/math/0405459, §1.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ActualZeroOrdinate

abbrev OrdinateAngle := AddCircle (2 * Real.pi)
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private def rawAngularLaw (T : ℝ) : Measure OrdinateAngle :=
  ∑ c : Copies T, ENNReal.ofReal ((Ncount 0 T : ℝ)⁻¹) •
    Measure.dirac (c.1.1.im : OrdinateAngle)

private theorem rawAngularLaw_probability (T : ℝ) (hN : 0 < Ncount 0 T) :
    IsProbabilityMeasure (rawAngularLaw T) := by
  constructor
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by positivity
  simp only [rawAngularLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_copies]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  simp [hn]

def angularLaw (T : ℝ) : ProbabilityMeasure OrdinateAngle :=
  if hN : 0 < Ncount 0 T then ⟨rawAngularLaw T, rawAngularLaw_probability T hN⟩
  else ⟨Measure.dirac 0, inferInstance⟩

def angularHaar : ProbabilityMeasure OrdinateAngle := ⟨AddCircle.haarAddCircle, inferInstance⟩

private theorem fourier_angle (k : ℤ) (t : ℝ) :
    fourier k (t : OrdinateAngle) = ZeroOrdinate.phase k t := by
  rw [fourier_coe_apply, ZeroOrdinate.phase]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem integral_fourier_angularLaw (T : ℝ) (hN : 0 < Ncount 0 T) (k : ℤ) :
    (∫ x : OrdinateAngle, fourier k x ∂(angularLaw T : Measure OrdinateAngle)) =
      ordinateSum T k / (Ncount 0 T : ℂ) := by
  have he : (angularLaw T : Measure OrdinateAngle) = rawAngularLaw T := by simp [angularLaw,hN]
  rw [he]
  unfold rawAngularLaw
  rw [integral_finsetSum_measure (fun c _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (Ncount 0 T : ℝ)⁻¹),
    ordinateSum, sum_eq_copies, Complex.real_smul, fourier_angle,
    Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]
  rw [Finset.mul_sum]

/-- A single energy hypothesis suffices for both the order-T FMZ term and
the leading Haar law, since T/N(T) tends to zero. -/
theorem fixedStripConcentration_of_sublinearHorizontalEnergy (hE : SublinearHorizontalEnergy) :
    FixedStripConcentration := by
  apply fixedStrip_of_relativeEnergy_tendsto_zero
  have h := hE.mul tendsto_height_div_count
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  change horizontalEnergy T / T * (T / (Ncount 0 T : ℝ)) =
    horizontalEnergy T / (Ncount 0 T : ℝ)
  field_simp [hT.ne']

/-- Count-normalized Hlawka equidistribution at angular scale one, with the
fixed-strip density input exposed. No finite list of computed zeros is used. -/
theorem tendsto_angularLaw_haar (hs : FixedStripConcentration) :
    Tendsto angularLaw atTop (𝓝 angularHaar) := by
  apply ProbabilityMeasure.tendsto_of_dense_test_integrals fourier
    span_fourier_closure_eq_top
  intro k
  by_cases hk : k = 0
  · subst k
    simp
  have hi : (∫ x : OrdinateAngle, fourier k x ∂(angularHaar : Measure OrdinateAngle)) = 0 := by
    have h := congrFun (fourierCoeff_fourier (T:=2*Real.pi) k) 0
    simpa [fourierCoeff,angularHaar,Pi.single_apply,hk,Ne.symm hk] using h
  rw [hi]
  have hm : Tendsto (fun T : ℝ => ordinateSum T (k:ℝ) / (Ncount 0 T : ℂ)) atTop (𝓝 0) := by
    rcases lt_or_gt_of_ne hk with h | h
    · have hpos : 0 < -(k:ℝ) := by exact_mod_cast neg_pos.mpr h
      have hstar := (tendsto_ordinate_div_count_of_pos hpos hs).star
      simpa [ordinateSum_neg] using hstar
    · exact tendsto_ordinate_div_count_of_pos (by exact_mod_cast h) hs
  apply hm.congr'
  filter_upwards [eventually_count_pos] with T hN
  exact (integral_fourier_angularLaw T hN k).symm

/-- The Haar law reaches every open arc after deletion of every bounded
initial zero window. Removing its finite set of angles costs zero Haar mass. -/
theorem exists_high_zero_in_open_angle (hs : FixedStripConcentration)
    (H : ℝ) {U : Set OrdinateAngle} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ρ : ℂ, IsNontrivialZero ρ ∧ 0 < ρ.im ∧ H < ρ.im ∧ (ρ.im : OrdinateAngle) ∈ U := by
  classical
  let F := (cutoff H).image (fun ρ : ℂ => (ρ.im : OrdinateAngle))
  let G := U \ (F : Set OrdinateAngle)
  have hopen : IsOpen G := hU.inter F.finite_toSet.isClosed.isOpen_compl
  have hpos : 0 < (angularHaar : Measure OrdinateAngle) G := by
    change 0 < (AddCircle.haarAddCircle : Measure OrdinateAngle) (U \ (F : Set OrdinateAngle))
    let e := AddCircle.homeomorphCircle (by positivity : 2 * Real.pi ≠ 0)
    let : Nontrivial OrdinateAngle := ⟨⟨(Real.pi : OrdinateAngle), 0, Real.Angle.pi_ne_zero⟩⟩
    let : ConnectedSpace OrdinateAngle := by
      first | infer_instance | exact e.symm.surjective.connectedSpace e.symm.continuous
    rw [measure_sdiff_null (F.measure_zero _)]
    exact hU.measure_pos _ hne
  by_contra ha
  have hz : ∀ᶠ T : ℝ in atTop, (angularLaw T : Measure OrdinateAngle) G = 0 := by
    filter_upwards [eventually_count_pos] with T hN
    have he : (angularLaw T : Measure OrdinateAngle) = rawAngularLaw T := by simp [angularLaw,hN]
    rw [he]
    simp only [rawAngularLaw, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro c _
    have hc := mem_cutoff.mp c.1.property
    have hmiss : (c.1.1.im : OrdinateAngle) ∉ G := by
      rintro ⟨hin,hout⟩
      by_cases hgt : H < c.1.1.im
      · exact ha ⟨c.1.1,hc.1,hc.2.1,hgt,hin⟩
      · exact hout (Finset.mem_image.mpr ⟨c.1.1,
          mem_cutoff.mpr ⟨hc.1,hc.2.1,le_of_not_gt hgt⟩,rfl⟩)
    simp [Measure.smul_apply,Measure.dirac_apply' _ hopen.measurableSet,hmiss]
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    (tendsto_angularLaw_haar hs) hopen
  have heq : (fun T : ℝ => (angularLaw T : Measure OrdinateAngle) G) =ᶠ[atTop] fun _ => 0 := hz
  have hlim := Filter.liminf_congr heq
  simp only [liminf_const] at hlim
  exact (not_lt_of_ge (by simpa only [hlim] using hle)) hpos

/-- One cofinal sequence for the target angle, independent of the harmonic. -/
theorem exists_ordinate_sequence_all_harmonics (hs : FixedStripConcentration) (θ : ℝ) :
    ∃ ρ : ℕ → ℂ, (∀ j, IsNontrivialZero (ρ j) ∧ 0 < (ρ j).im) ∧
      Tendsto (fun j => (ρ j).im) atTop atTop ∧
      ∀ k : ℤ, Tendsto (fun j => ZeroOrdinate.phase k (ρ j).im) atTop
        (𝓝 (ZeroOrdinate.phase k θ)) := by
  have hh (j : ℕ) := exists_high_zero_in_open_angle hs (j:ℝ)
    (U:=Metric.ball (θ : OrdinateAngle) (1/((j:ℝ)+1))) Metric.isOpen_ball
    ⟨_,Metric.mem_ball_self (by positivity)⟩
  choose ρ hz hp hhigh hnear using hh
  refine ⟨ρ,fun j => ⟨hz j,hp j⟩,tendsto_atTop_mono (fun j => (hhigh j).le)
    tendsto_natCast_atTop_atTop,?_⟩
  have hangle : Tendsto (fun j => ((ρ j).im : OrdinateAngle)) atTop (𝓝 (θ : OrdinateAngle)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun j => (hnear j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  intro k
  simpa only [Function.comp_def, fourier_angle] using
    ((fourier k : C(OrdinateAngle,ℂ)).continuous.tendsto _).comp hangle

end RiemannResearch.Analysis.ActualZeroOrdinate
