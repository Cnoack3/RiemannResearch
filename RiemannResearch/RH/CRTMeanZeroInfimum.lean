import RiemannResearch.RH.CRTMeanRepair
import RiemannResearch.RH.CRTPositiveMExpansion
import RiemannResearch.RH.ParetoLegalStructure
import RiemannResearch.RH.ConditionalMeanSubpolynomial

/-!
# Zero period mean does not change the legal exact-head energy infimum
Source: the explicit delayed mean repair in this continuation and the existing
legal-period theorem. This discharges periodicity for every actual legal
witness; no period-existence provider or RH assumption is added.
-/
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.CRTBlock
noncomputable section
open RiemannResearch.RH.Pareto

def zeroMeanHeadClass (Y : ℕ) : Set (ℕ → ℝ) :=
  {F | F ∈ conditionalHeadClass Y ∧
    ∃ Q : ℕ, 0 < Q ∧ (∀ n, F (n+Q)=F n) ∧ periodMean F Q=0}

def zeroMeanHeadEnergies (Y : ℕ) : Set ℝ :=
  {e | ∃ F ∈ zeroMeanHeadClass Y, conditionalMeanSquare F=e}

def zeroMeanHeadMinimum (Y : ℕ) : ℝ := sInf (zeroMeanHeadEnergies Y)

/-- Periodicity is supplied by the actual legal-span theorem. -/
theorem exists_zeroMeanHead_near (Y : ℕ) (F : ℕ → ℝ)
    (hF : F ∈ conditionalHeadClass Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ G ∈ zeroMeanHeadClass Y,
      conditionalMeanSquare G < conditionalMeanSquare F+ε := by
  obtain ⟨Q,hQ,hper⟩ := legalSeedSpan_hasLegalReflectionPeriod (Set.Ici 1)
    (by intro a ha; exact ha) hF.1
  obtain ⟨G,hG,hGP,hcost⟩ := exists_zeroMean_head_near Y F hF Q hQ
    (hper Q (dvd_refl Q)).1 ε hε
  exact ⟨G,⟨hG,hGP⟩,hcost⟩

theorem zeroMeanHeadClass_nonempty (Y : ℕ) : (zeroMeanHeadClass Y).Nonempty := by
  obtain ⟨F,hF⟩ := conditionalHeadClass_nonempty Y
  obtain ⟨G,hG,hcost⟩ := exists_zeroMeanHead_near Y F hF 1 (by norm_num)
  exact ⟨G,hG⟩

theorem zeroMeanHeadEnergies_nonempty (Y : ℕ) : (zeroMeanHeadEnergies Y).Nonempty := by
  obtain ⟨G,hG⟩ := zeroMeanHeadClass_nonempty Y
  exact ⟨conditionalMeanSquare G,G,hG,rfl⟩

theorem zeroMeanHeadEnergies_bddBelow (Y : ℕ) : BddBelow (zeroMeanHeadEnergies Y) := by
  refine ⟨0,?_⟩
  rintro e ⟨G,hG,rfl⟩
  exact conditionalMeanSquare_nonneg G

theorem zeroMeanHeadMinimum_le (Y : ℕ) (G : ℕ → ℝ)
    (hG : G ∈ zeroMeanHeadClass Y) :
    zeroMeanHeadMinimum Y ≤ conditionalMeanSquare G :=
  csInf_le (zeroMeanHeadEnergies_bddBelow Y) ⟨G,hG,rfl⟩

/-- The mean-zero infimum is a lower bound for every unrestricted exact head. -/
theorem zeroMeanHeadMinimum_le_unrestricted (Y : ℕ) (F : ℕ → ℝ)
    (hF : F ∈ conditionalHeadClass Y) :
    zeroMeanHeadMinimum Y ≤ conditionalMeanSquare F := by
  by_contra h
  have hlt : conditionalMeanSquare F < zeroMeanHeadMinimum Y := lt_of_not_ge h
  obtain ⟨G,hG,hcost⟩ := exists_zeroMeanHead_near Y F hF
    ((zeroMeanHeadMinimum Y-conditionalMeanSquare F)/2) (by linarith)
  have hmin := zeroMeanHeadMinimum_le Y G hG
  linarith

/-- Exact equality of the genuine variational infima; no attainment is asserted. -/
theorem zeroMeanHeadMinimum_eq (Y : ℕ) :
    zeroMeanHeadMinimum Y = conditionalHeadMinimum Y := by
  apply le_antisymm
  · apply le_csInf (conditionalHeadEnergies_nonempty Y)
    rintro e ⟨F,hF,rfl⟩
    exact zeroMeanHeadMinimum_le_unrestricted Y F hF
  · apply le_csInf (zeroMeanHeadEnergies_nonempty Y)
    rintro e ⟨G,hG,rfl⟩
    exact conditionalHeadMinimum_le Y hG.1

/-- The existence obligation for a cofinal subpolynomial family is unchanged. -/
theorem subpolynomial_heads_zeroMean_iff (Y : ℕ → ℕ) (hY : Tendsto Y atTop atTop) :
    (∃ F : ℕ → ℕ → ℝ, (∀ j, F j ∈ conditionalHeadClass (Y j)) ∧
      SubpolynomialConditionalMean F Y) ↔
    (∃ F : ℕ → ℕ → ℝ, (∀ j, F j ∈ zeroMeanHeadClass (Y j)) ∧
      SubpolynomialConditionalMean F Y) := by
  constructor
  · rintro ⟨F,hF,hsub⟩
    choose G hG hcost using
      (fun j => exists_zeroMeanHead_near (Y j) (F j) (hF j) 1 (by norm_num))
    refine ⟨G,hG,?_⟩
    intro ε hε
    obtain ⟨C,hC,hbound⟩ := hsub ε hε
    refine ⟨C+1,by linarith,?_⟩
    filter_upwards [hbound,hY.eventually (eventually_ge_atTop 1)] with j hj hYj
    have hYR : (1 : ℝ) ≤ Y j := by exact_mod_cast hYj
    have hp := Real.one_le_rpow hYR hε.le
    have hc := hcost j
    nlinarith
  · rintro ⟨F,hF,hsub⟩
    exact ⟨F,fun j => (hF j).1,hsub⟩

/-- An RH endpoint for the concrete finite positive polygamma energy.
The supplied subpolynomial bound is the open arithmetic hypothesis. -/
theorem riemannHypothesis_of_positiveM_subpolynomial_heads
    (F : ℕ → ℕ → ℝ) (Q Y : ℕ → ℕ)
    (hF : ∀ j, F j ∈ conditionalHeadClass (Y j))
    (hY : Tendsto Y atTop atTop)
    (hQ : ∀ j, 0 < Q j) (hp : ∀ j n, F j (n+Q j)=F j n)
    (hm : ∀ j, periodMean (F j) (Q j)=0)
    (hcore : HasSubpolynomialEnergy Y
      (fun j => positiveMCore (Q j) 1
        (fun r => periodDefect (F j) (Q j) (r.val+1)))) : RiemannHypothesis := by
  have hactual := (growing_zeroMean_positiveM_subpolynomial_iff F Q Y hQ hp hm).mpr hcore
  apply riemannHypothesis_of_subpolynomial_conditionalMean_heads
    (Set.Ici 1) (by intro a ha; exact ha) F Y
    (fun j => (hF j).1) (fun j => (hF j).2) hY
  intro ε hε
  obtain ⟨C,hC,j₀,hbound⟩ := hactual ε hε
  refine ⟨C,hC.le,?_⟩
  filter_upwards [eventually_ge_atTop j₀] with j hj
  exact hbound j hj

end
end RiemannResearch.RH.CRTBlock
