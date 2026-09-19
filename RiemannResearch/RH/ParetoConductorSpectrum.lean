import RiemannResearch.RH.ParetoConductorInnovationBasis
import RiemannResearch.LinearAlgebra.ConditionalSchurWoodbury
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The actual conductor covariance inverse and marked spectral formula

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`,
Sections 4 and 7. The synthesis maps, adjoints, covariance and Schur
inverses below come from actual full-weight conductor packets. Their
invertibility is proved from arithmetic innovation independence. The
eigensystem is constructed by the finite-dimensional spectral theorem.
No residual-mass or all-scale estimate is assumed or asserted.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra
open RiemannResearch.LinearAlgebra.ConditionalSchur
open RiemannResearch.LinearAlgebra.WeightedQuotientHilbert
noncomputable section

abbrev ConductorCoefficients (Q p : ℕ) := EuclideanSpace ℝ (conductorNewConductors Q p)
abbrev ConductorAmbient (Q p : ℕ) := EuclideanSpace ℝ (Fin (Q*p))

def conductorSynthesis (Q p : ℕ) : ConductorCoefficients Q p →ₗ[ℝ] ConductorAmbient Q p :=
  (Fintype.linearCombination ℝ (conductorNewPacket Q p)).comp
    (WithLp.linearEquiv 2 ℝ (conductorNewConductors Q p → ℝ)).toLinearMap

def conductorMeanSynthesis (Q p : ℕ) (hQ : 0 < Q) :
    ConductorCoefficients Q p →ₗ[ℝ] ConductorAmbient Q p :=
  ((LinearMap.id - (conductorOldSpace Q p).starProjection.toLinearMap).comp
    (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p)).starProjection.toLinearMap).comp
      (conductorSynthesis Q p)

def conductorInnovationSynthesis (Q p : ℕ) (hQ : 0 < Q) :
    ConductorCoefficients Q p →ₗ[ℝ] ConductorAmbient Q p :=
  (LinearMap.id -
    (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p)).starProjection.toLinearMap).comp
      (conductorSynthesis Q p)

def conductorResidualSynthesis (Q p : ℕ) :
    ConductorCoefficients Q p →ₗ[ℝ] ConductorAmbient Q p :=
  (LinearMap.id - (conductorOldSpace Q p).starProjection.toLinearMap).comp
    (conductorSynthesis Q p)

def conductorMarkedResidual (Q p : ℕ) : ConductorAmbient Q p :=
  packetResidual (conductorOldSpace Q p) (conductorHilbert Q p (fun _ => 1))

theorem conductorInnovationSynthesis_apply (Q p : ℕ) (hQ : 0 < Q)
    (c : ConductorCoefficients Q p) :
    conductorInnovationSynthesis Q p hQ c =
      Fintype.linearCombination ℝ
        (fluctuation (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p)) ∘
          conductorNewPacket Q p) c.ofLp := by
  change fluctuation (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p))
    (Fintype.linearCombination ℝ (conductorNewPacket Q p) c.ofLp) = _
  simpa only [Fintype.linearCombination_apply, finiteSchurCombination] using
    fluctuation_combination
      (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p))
      (conductorNewPacket Q p) c.ofLp

theorem conductorResidualSynthesis_apply (Q p : ℕ) (c : ConductorCoefficients Q p) :
    conductorResidualSynthesis Q p c =
      finiteSchurCombination (packetResidual (conductorOldSpace Q p) ∘
        conductorNewPacket Q p) c.ofLp := by
  change packetResidual (conductorOldSpace Q p)
    (Fintype.linearCombination ℝ (conductorNewPacket Q p) c.ofLp) = _
  simpa only [Fintype.linearCombination_apply, finiteSchurCombination] using
    packetResidual_combination (conductorOldSpace Q p) (conductorNewPacket Q p) c.ofLp

theorem conductor_synthesis_gram_split (Q p : ℕ) (hQ : 0 < Q)
    (c d : ConductorCoefficients Q p) :
    inner ℝ (conductorResidualSynthesis Q p c) (conductorResidualSynthesis Q p d) =
      inner ℝ (conductorMeanSynthesis Q p hQ c) (conductorMeanSynthesis Q p hQ d) +
      inner ℝ (conductorInnovationSynthesis Q p hQ c) (conductorInnovationSynthesis Q p hQ d) :=
  gram_split (conductorOldSpace Q p)
    (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p))
    (conductorOldSpace_le_coarse Q p hQ) (conductorSynthesis Q p c) (conductorSynthesis Q p d)

theorem conductorInnovationSynthesis_injective (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime) :
    Function.Injective (conductorInnovationSynthesis Q p hQ) := by
  intro c d h
  apply (WithLp.linearEquiv 2 ℝ (conductorNewConductors Q p → ℝ)).injective
  change c.ofLp = d.ofLp
  apply conductor_fluctuation_synthesis_injective p Q hp hQ
  simpa only [conductorInnovationSynthesis_apply, Function.comp_def] using h

theorem conductorResidualSynthesis_injective (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime) :
    Function.Injective (conductorResidualSynthesis Q p) := by
  intro c d h
  have hz : conductorResidualSynthesis Q p (c-d) = 0 := by rw [map_sub, h, sub_self]
  have hg := conductor_synthesis_gram_split Q p hQ (c-d) (c-d)
  simp only [real_inner_self_eq_norm_sq] at hg
  rw [hz, norm_zero, zero_pow (by omega : 2 ≠ 0)] at hg
  have hn : ‖conductorInnovationSynthesis Q p hQ (c-d)‖ = 0 := by
    nlinarith [sq_nonneg ‖conductorMeanSynthesis Q p hQ (c-d)‖]
  have hu : conductorInnovationSynthesis Q p hQ (c-d) = 0 := norm_eq_zero.mp hn
  have hcd : c-d = 0 := conductorInnovationSynthesis_injective Q p hQ hp (by simpa using hu)
  exact sub_eq_zero.mp hcd

private theorem adjoint_gram_injective
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (Z : E →ₗ[ℝ] H) (hZ : Function.Injective Z) :
    Function.Injective ((LinearMap.adjoint Z).comp Z) := by
  intro c d h
  have hz : ((LinearMap.adjoint Z).comp Z) (c-d) = 0 := by rw [map_sub, h, sub_self]
  have he := LinearMap.adjoint_inner_right Z (c-d) (Z (c-d))
  change inner ℝ (c-d) (((LinearMap.adjoint Z).comp Z) (c-d)) =
    inner ℝ (Z (c-d)) (Z (c-d)) at he
  rw [hz, inner_zero_right, real_inner_self_eq_norm_sq] at he
  have hn : ‖Z (c-d)‖ = 0 := by nlinarith
  have hcd : c-d = 0 := hZ (by simpa using norm_eq_zero.mp hn)
  exact sub_eq_zero.mp hcd

private def adjointGramEquiv
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (Z : E →ₗ[ℝ] H) (hZ : Function.Injective Z) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofInjectiveEndo ((LinearMap.adjoint Z).comp Z) (adjoint_gram_injective Z hZ)

/-- The genuine inverse-capable covariance operator `U* U`. -/
def conductorCovarianceEquiv (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime) :
    ConductorCoefficients Q p ≃ₗ[ℝ] ConductorCoefficients Q p :=
  adjointGramEquiv (conductorInnovationSynthesis Q p hQ)
    (conductorInnovationSynthesis_injective Q p hQ hp)

/-- The genuine inverse-capable Schur operator `T* T`. -/
def conductorSchurEquiv (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime) :
    ConductorCoefficients Q p ≃ₗ[ℝ] ConductorCoefficients Q p :=
  adjointGramEquiv (conductorResidualSynthesis Q p)
    (conductorResidualSynthesis_injective Q p hQ hp)

theorem conductorCovarianceEquiv_apply (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime)
    (c : ConductorCoefficients Q p) :
    conductorCovarianceEquiv Q p hQ hp c =
      (LinearMap.adjoint (conductorInnovationSynthesis Q p hQ))
        (conductorInnovationSynthesis Q p hQ c) := rfl

theorem conductorSchurEquiv_apply (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime)
    (c : ConductorCoefficients Q p) :
    conductorSchurEquiv Q p hQ hp c =
      (LinearMap.adjoint (conductorResidualSynthesis Q p)) (conductorResidualSynthesis Q p c) := rfl

theorem conductorSchurEquiv_split (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime)
    (c : ConductorCoefficients Q p) :
    conductorSchurEquiv Q p hQ hp c = conductorCovarianceEquiv Q p hQ hp c +
      (LinearMap.adjoint (conductorMeanSynthesis Q p hQ)) (conductorMeanSynthesis Q p hQ c) := by
  have hpair (x : ConductorCoefficients Q p) :
      inner ℝ x (conductorSchurEquiv Q p hQ hp c) =
        inner ℝ x (conductorCovarianceEquiv Q p hQ hp c +
          (LinearMap.adjoint (conductorMeanSynthesis Q p hQ)) (conductorMeanSynthesis Q p hQ c)) := by
    rw [conductorSchurEquiv_apply, conductorCovarianceEquiv_apply, inner_add_right,
      LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
    linarith [conductor_synthesis_gram_split Q p hQ x c]
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_sub_right, hpair, sub_self]

theorem conductorCovarianceEquiv_symmetric (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime)
    (c d : ConductorCoefficients Q p) :
    inner ℝ (conductorCovarianceEquiv Q p hQ hp c) d =
      inner ℝ c (conductorCovarianceEquiv Q p hQ hp d) := by
  rw [conductorCovarianceEquiv_apply, conductorCovarianceEquiv_apply,
    LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]

theorem conductorCovarianceEquiv_quadratic (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime)
    (c : ConductorCoefficients Q p) :
    inner ℝ c (conductorCovarianceEquiv Q p hQ hp c) =
      ‖conductorInnovationSynthesis Q p hQ c‖ ^ 2 := by
  rw [conductorCovarianceEquiv_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- `I + A D⁻¹ A*` for the actual conductor data. -/
def conductorResolvent (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime) :
    ConductorAmbient Q p ≃ₗ[ℝ] ConductorAmbient Q p :=
  woodburyEquiv (conductorMeanSynthesis Q p hQ)
    (LinearMap.adjoint (conductorMeanSynthesis Q p hQ))
    (conductorCovarianceEquiv Q p hQ hp) (conductorSchurEquiv Q p hQ hp)
    (conductorSchurEquiv_split Q p hQ hp)

def conductorOptimalCoefficients (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime) :
    ConductorCoefficients Q p :=
  (conductorSchurEquiv Q p hQ hp).symm
    ((LinearMap.adjoint (conductorMeanSynthesis Q p hQ)) (conductorMarkedResidual Q p))

theorem conductor_optimal_synthesis_normal (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime)
    (c : ConductorCoefficients Q p) :
    inner ℝ (conductorResidualSynthesis Q p c)
      (conductorResidualSynthesis Q p (conductorOptimalCoefficients Q p hQ hp)) =
      inner ℝ (conductorResidualSynthesis Q p c) (conductorMarkedResidual Q p) := by
  calc
    _ = inner ℝ c (conductorSchurEquiv Q p hQ hp
        (conductorOptimalCoefficients Q p hQ hp)) := by
      rw [conductorSchurEquiv_apply, LinearMap.adjoint_inner_right]
    _ = inner ℝ c ((LinearMap.adjoint (conductorMeanSynthesis Q p hQ))
        (conductorMarkedResidual Q p)) := by
      rw [conductorOptimalCoefficients, LinearEquiv.apply_symm_apply]
    _ = inner ℝ (conductorMeanSynthesis Q p hQ c) (conductorMarkedResidual Q p) :=
      LinearMap.adjoint_inner_right _ _ _
    _ = _ := by
      exact (score_eq_mean_score (conductorOldSpace Q p)
        (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p))
        (conductorOldSpace_le_coarse Q p hQ) (conductor_residual_mem_coarse Q p hQ)
        (conductorSynthesis Q p c)).symm

/-- The constructed true inverse supplies every actual packet normal equation. -/
theorem conductorOptimalCoefficients_normal (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime)
    (i : conductorNewConductors Q p) :
    inner ℝ (packetResidual (conductorOldSpace Q p) (conductorNewPacket Q p i))
      (finiteSchurCombination (packetResidual (conductorOldSpace Q p) ∘ conductorNewPacket Q p)
        (conductorOptimalCoefficients Q p hQ hp).ofLp) =
      inner ℝ (packetResidual (conductorOldSpace Q p) (conductorNewPacket Q p i))
        (conductorMarkedResidual Q p) := by
  classical
  let u : ConductorCoefficients Q p := WithLp.toLp 2 (Pi.single i 1)
  have hu : conductorResidualSynthesis Q p u =
      packetResidual (conductorOldSpace Q p) (conductorNewPacket Q p i) := by
    rw [conductorResidualSynthesis_apply]
    simp [finiteSchurCombination, u, Pi.single_apply]
  have h := conductor_optimal_synthesis_normal Q p hQ hp u
  rw [hu, conductorResidualSynthesis_apply] at h
  exact h

theorem conductorMarkedResidual_norm_sq (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime) :
    ‖conductorMarkedResidual Q p‖ ^ 2 = ConductorProjection.energy Q :=
  conductor_sampled_energy_eq Q p Q hQ hp.pos hQ (dvd_mul_right Q p)

/-- Equation (4.2) for the actual full infinite Pareto error after conductor
enlargement, with a constructed covariance inverse and constructed Schur inverse. -/
theorem conductor_resolvent_energy (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime) :
    ConductorProjection.energy (Q*p) =
      inner ℝ (conductorMarkedResidual Q p)
        ((conductorResolvent Q p hQ hp).symm (conductorMarkedResidual Q p)) := by
  let c := conductorOptimalCoefficients Q p hQ hp
  have hc := conductorOptimalCoefficients_normal Q p hQ hp
  have hproj := augmented_projection_residual (conductorOldSpace Q p)
    (conductorNewPacket Q p) (conductorHilbert Q p (fun _ => 1)) c.ofLp hc
  simp only [← conductorEnlargedSpace_eq_augmented Q p hQ hp.pos] at hproj
  have hproj' : conductorMarkedResidual Q p - conductorResidualSynthesis Q p c =
      packetResidual (conductorSampledSpace Q p (Q*p))
        (conductorHilbert Q p (fun _ => 1)) := by
    rw [conductorResidualSynthesis_apply]
    exact hproj
  calc
    _ = ‖packetResidual (conductorSampledSpace Q p (Q*p))
        (conductorHilbert Q p (fun _ => 1))‖ ^ 2 :=
      (conductor_sampled_energy_eq Q p (Q*p) hQ hp.pos
        (Nat.mul_pos hQ hp.pos) (dvd_refl _)).symm
    _ = ‖conductorMarkedResidual Q p - conductorResidualSynthesis Q p c‖ ^ 2 := by rw [hproj']
    _ = ‖conductorMarkedResidual Q p - conductorMeanSynthesis Q p hQ c‖ ^ 2 +
        ‖conductorInnovationSynthesis Q p hQ c‖ ^ 2 :=
      residual_objective (conductorOldSpace Q p)
        (coarseSpace (conductorQuotient Q p hQ) (conductorFineWeight Q p))
        (conductorOldSpace_le_coarse Q p hQ) (conductor_residual_mem_coarse Q p hQ)
        (conductorSynthesis Q p c)
    _ = _ := by
      rw [← conductorCovarianceEquiv_quadratic Q p hQ hp c]
      exact woodbury_minimum_energy (conductorMeanSynthesis Q p hQ)
        (LinearMap.adjoint (conductorMeanSynthesis Q p hQ))
        (conductorCovarianceEquiv Q p hQ hp) (conductorSchurEquiv Q p hQ hp)
        (conductorSchurEquiv_split Q p hQ hp)
        (fun b e => (LinearMap.adjoint_inner_right (conductorMeanSynthesis Q p hQ) b e).symm)
        (conductorMarkedResidual Q p)

/-- Actual `A D⁻¹ A*`, not a separately supplied positive operator. -/
def conductorInformationOperator (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime) :
    ConductorAmbient Q p →ₗ[ℝ] ConductorAmbient Q p :=
  (conductorMeanSynthesis Q p hQ).comp
    ((conductorCovarianceEquiv Q p hQ hp).symm.toLinearMap.comp
      (LinearMap.adjoint (conductorMeanSynthesis Q p hQ)))

/-- Equations (4.3) and (7.3) for the actual conductor step. The larger
ambient basis is harmless: additional zero eigenvalues keep their exact
residual weights. No marked spectral-mass lower bound is assumed. -/
theorem conductor_actual_spectral_formula (Q p : ℕ) (hQ : 0 < Q) (hp : p.Prime) :
    ∃ (v : OrthonormalBasis (Fin (Module.finrank ℝ (ConductorAmbient Q p))) ℝ
        (ConductorAmbient Q p))
      (lam : Fin (Module.finrank ℝ (ConductorAmbient Q p)) → ℝ),
      (∀ i, 0 ≤ lam i) ∧
      (∀ i, conductorInformationOperator Q p hQ hp (v i) = lam i • v i) ∧
      ConductorProjection.energy (Q*p) =
        (∑ i, (inner ℝ (v i) (conductorMarkedResidual Q p)) ^ 2 / (1 + lam i)) ∧
      ConductorProjection.gain Q (Q*p) =
        (∑ i, (lam i / (1 + lam i)) * (inner ℝ (v i) (conductorMarkedResidual Q p)) ^ 2) ∧
      ConductorProjection.relativeGain Q (Q*p) =
        (∑ i, (lam i / (1 + lam i)) * (inner ℝ (v i) (conductorMarkedResidual Q p)) ^ 2) /
          ConductorProjection.energy Q := by
  obtain ⟨v, lam, hlam, heig, henergy, hgain⟩ := exists_information_spectral_formula
    (conductorMeanSynthesis Q p hQ) (LinearMap.adjoint (conductorMeanSynthesis Q p hQ))
    (conductorCovarianceEquiv Q p hQ hp) (conductorSchurEquiv Q p hQ hp)
    (conductorSchurEquiv_split Q p hQ hp)
    (fun b e => (LinearMap.adjoint_inner_right (conductorMeanSynthesis Q p hQ) b e).symm)
    (conductorCovarianceEquiv_symmetric Q p hQ hp)
    (fun b => by rw [conductorCovarianceEquiv_quadratic]; exact sq_nonneg _)
  have he : ConductorProjection.energy (Q*p) =
      ∑ i, (inner ℝ (v i) (conductorMarkedResidual Q p)) ^ 2 / (1 + lam i) := by
    exact (conductor_resolvent_energy Q p hQ hp).trans (henergy (conductorMarkedResidual Q p))
  have hg : ConductorProjection.gain Q (Q*p) =
      ∑ i, (lam i / (1 + lam i)) * (inner ℝ (v i) (conductorMarkedResidual Q p)) ^ 2 := by
    have h := hgain (conductorMarkedResidual Q p)
    change ‖conductorMarkedResidual Q p‖ ^ 2 -
      inner ℝ (conductorMarkedResidual Q p)
        ((conductorResolvent Q p hQ hp).symm (conductorMarkedResidual Q p)) = _ at h
    rw [conductorMarkedResidual_norm_sq Q p hQ hp, ← conductor_resolvent_energy Q p hQ hp] at h
    have hs := ConductorProjection.energy_step (dvd_mul_right Q p) (Nat.mul_pos hQ hp.pos)
    linarith
  refine ⟨v, lam, hlam, heig, he, hg, ?_⟩
  unfold ConductorProjection.relativeGain
  rw [hg]

end
end RiemannResearch.RH.Pareto
