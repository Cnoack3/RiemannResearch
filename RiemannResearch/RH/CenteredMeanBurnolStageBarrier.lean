import RiemannResearch.RH.CenteredMeanLateSolveBarrier
import RiemannResearch.RH.BurnolParetoTransfer
import RiemannResearch.RH.CanonicalMobiusMovingCutoff

/-!
# The Burnol cutoff obstruction for finite Gram drift

The continuous Burnol lower envelope is an explicit analytic premise. Its
existing cutoff-preserving Pareto transfer supplies a lower bound on the
actual finite projection error. Combined with the canonical Möbius exact
head, it rules out a bounded stretched drift budget whenever the later
dictionary grows too slowly relative to the physical cutoff, including every
polynomially bounded later dictionary. The estimate uses the entire physical
base error and the complete change of solve.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
open CoefficientStabilization RamanujanCanonicalOptimizer BurnolTransfer
open RiemannResearch.Analysis

private theorem logSquare_damping_tendsto_zero (b : ℝ) (hb : 0 < b) :
    Tendsto (fun N : ℕ => MovingCovariance.logScale N ^ 2 * sectionTailDamping b N)
      atTop (𝓝 0) := by
  obtain ⟨D, hD, hdec⟩ := logProductExp_le_inverse_nat_power b (1 / 11) hb (by norm_num) 3
  have hu : Tendsto (fun N : ℕ => D / MovingCovariance.logScale N) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp MovingCovariance.logScale_tendsto).const_mul D
  apply squeeze_zero' (Eventually.of_forall fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    ?_ hu
  filter_upwards [MovingCovariance.logScale_tendsto.eventually (eventually_ge_atTop (6 : ℝ))]
    with N hN
  let L := MovingCovariance.logScale N
  have hLp : 0 < L := by change 0 < MovingCovariance.logScale N; linarith only [hN]
  have ht : sectionTailDamping b N ≤ D / L ^ 3 := hdec L hN
  calc
    _ ≤ L ^ 2 * (D / L ^ 3) := mul_le_mul_of_nonneg_left ht (sq_nonneg _)
    _ = D / L := by field_simp [hLp.ne']

/-- The finite lower bound determines how large the later dictionary must
be under any proposed bounded scaled budget. The coefficient and physical
threshold are uniform in both Gram stages. Burnol's continuous cutoff estimate
is the explicit analytic premise. -/
theorem burnol_lateSolve_drift_product_lower (c : ℝ) (hc : 0 < c) (k₀ : ℕ)
    (hburnol : ∀ m : ℕ, k₀ ≤ m → 2 ≤ m → ContinuousCutoffLowerBound m (c / Real.log m)) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop, ∀ B A : ℕ, B ≤ A → n ≤ A + 1 →
      c ^ 2 ≤ D * (1 + (n : ℝ) * sectionTailDamping lateSolveExponent.val n *
        (finiteSectionTailCost B n + finiteSectionTailDrift B A n)) *
        Real.log ((A + 2 : ℕ) : ℝ) ^ 2 * sectionTailDamping lateSolveExponent.val n := by
  obtain ⟨D, hD, hmass⟩ := lateSolve_mass_loss_upper
  refine ⟨D, hD, ?_⟩
  filter_upwards [eventually_ge_atTop k₀, hmass] with n hn hm
  intro B A hBA hNA
  let ℓ := Real.log ((A + 2 : ℕ) : ℝ)
  have hℓ : 0 < ℓ := Real.log_pos (by exact_mod_cast (show 1 < A + 2 by omega))
  have hE : c ≤ energy (A + 1) * ℓ :=
    (div_le_iff₀ hℓ).mp (energy_log_envelope c k₀ hburnol (A + 1) (by omega) (by omega))
  have hE₂ : c ^ 2 ≤ energy (A + 1) ^ 2 * ℓ ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ hc.le (hc.le.trans hE)).mpr hE
  rw [packet_energy_eq_original] at hE₂
  apply (hE₂.trans (mul_le_mul_of_nonneg_right (hm B A hBA hNA) (sq_nonneg ℓ))).trans_eq
  dsimp only [ℓ]
  ring

/-- A bounded scaled budget is incompatible with Burnol whenever the squared
logarithm of the later cutoff times the damping tends to zero. -/
theorem burnol_lateSolve_barrier (c : ℝ) (hc : 0 < c) (k₀ : ℕ)
    (hburnol : ∀ m : ℕ, k₀ ≤ m → 2 ≤ m → ContinuousCutoffLowerBound m (c / Real.log m)) :
    ∀ B A N : ℕ → ℕ, Tendsto N atTop atTop →
      (∀ᶠ j : ℕ in atTop, B j ≤ A j ∧ N j ≤ A j + 1) →
      Tendsto (fun j : ℕ => Real.log ((A j + 2 : ℕ) : ℝ) ^ 2 *
        sectionTailDamping lateSolveExponent.val (N j)) atTop (𝓝 0) →
      Tendsto (fun j : ℕ => (N j : ℝ) * sectionTailDamping lateSolveExponent.val (N j) *
        (finiteSectionTailCost (B j) (N j) + finiteSectionTailDrift (B j) (A j) (N j)))
        atTop atTop := by
  obtain ⟨D, hD, hprod⟩ := burnol_lateSolve_drift_product_lower c hc k₀ hburnol
  intro B A N hN hlate hsmall
  let S := fun j : ℕ => (N j : ℝ) * sectionTailDamping lateSolveExponent.val (N j) *
    (finiteSectionTailCost (B j) (N j) + finiteSectionTailDrift (B j) (A j) (N j))
  let Q := fun j : ℕ => D * (Real.log ((A j + 2 : ℕ) : ℝ) ^ 2 *
    sectionTailDamping lateSolveExponent.val (N j))
  have hQ : Tendsto Q atTop (𝓝 0) := by simpa only [Q, mul_zero] using hsmall.const_mul D
  have hp : ∀ᶠ j : ℕ in atTop, c ^ 2 ≤ (1 + S j) * Q j := by
    filter_upwards [hlate, hN.eventually hprod] with j hj hprodj
    apply (hprodj (B j) (A j) hj.1 hj.2).trans_eq
    dsimp only [S, Q]
    ring
  have ht : Tendsto (fun j => 1 + S j) atTop atTop :=
    tendsto_atTop_of_pos_le_mul_tendsto_zero (sq_pos_of_pos hc)
      (Eventually.of_forall fun j => by dsimp only [Q, sectionTailDamping]; positivity) hQ hp
  apply tendsto_atTop.mpr
  intro t
  filter_upwards [ht.eventually (eventually_ge_atTop (1 + t))] with j hj
  change 1 + t ≤ 1 + S j at hj
  change t ≤ S j
  linarith only [hj]

/-- In particular every polynomially bounded later dictionary lies in the
excluded range. The Burnol input is explicit and independent of the centered
boundary. The conclusion includes the natural diagonal `A j = N j`. -/
theorem burnol_polynomial_lateSolve_barrier (c : ℝ) (hc : 0 < c) (k₀ : ℕ)
    (hburnol : ∀ m : ℕ, k₀ ≤ m → 2 ≤ m → ContinuousCutoffLowerBound m (c / Real.log m)) :
    ∀ B A N : ℕ → ℕ, Tendsto N atTop atTop →
      (∀ᶠ j : ℕ in atTop, B j ≤ A j ∧ N j ≤ A j + 1) →
      ∀ d : ℝ, 0 < d →
        (∀ᶠ j : ℕ in atTop, Real.log ((A j + 2 : ℕ) : ℝ) ≤ d * MovingCovariance.logScale (N j)) →
        Tendsto (fun j : ℕ => (N j : ℝ) * sectionTailDamping lateSolveExponent.val (N j) *
          (finiteSectionTailCost (B j) (N j) + finiteSectionTailDrift (B j) (A j) (N j)))
          atTop atTop := by
  intro B A N hN hlate d hd hg
  apply burnol_lateSolve_barrier c hc k₀ hburnol B A N hN hlate
  have h := ((logSquare_damping_tendsto_zero
    lateSolveExponent.val lateSolveExponent.property).comp hN).const_mul (d ^ 2)
  rw [mul_zero] at h
  apply squeeze_zero' (Eventually.of_forall fun j => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    ?_ h
  filter_upwards [hg] with j hj
  have hl : 0 ≤ Real.log ((A j + 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ A j + 2 by omega))
  have hs := (sq_le_sq₀ hl (hl.trans hj)).mpr hj
  let θ := sectionTailDamping lateSolveExponent.val (N j)
  have hθ : 0 ≤ θ := (Real.exp_pos _).le
  change Real.log ((A j + 2 : ℕ) : ℝ) ^ 2 * θ ≤ d ^ 2 * (MovingCovariance.logScale (N j) ^ 2 * θ)
  calc
    _ ≤ (d * MovingCovariance.logScale (N j)) ^ 2 * θ := mul_le_mul_of_nonneg_right hs hθ
    _ = _ := by ring

/-- The actual cofinal diagonal at the *same* exponent as the RH consumer
diverges under the continuous cutoff lower bound, for every ordered base solve. -/
theorem burnol_diagonal_lateSolve_barrier (c : ℝ) (hc : 0 < c) (k₀ : ℕ)
    (hburnol : ∀ m : ℕ, k₀ ≤ m → 2 ≤ m → ContinuousCutoffLowerBound m (c / Real.log m))
    (B N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hBN : ∀ᶠ j : ℕ in atTop, B j ≤ N j) :
    Tendsto (fun j : ℕ => (N j : ℝ) * sectionTailDamping lateSolveExponent.val (N j) *
      (finiteSectionTailCost (B j) (N j) + finiteSectionTailDrift (B j) (N j) (N j)))
      atTop atTop := by
  apply burnol_polynomial_lateSolve_barrier c hc k₀ hburnol B N N hN
    (hBN.mono fun j hj => ⟨hj, Nat.le_succ _⟩) 1 zero_lt_one
  filter_upwards [hN.eventually (eventually_ge_atTop (2 : ℕ))] with j hj
  have hn : 0 < (N j : ℝ) := by exact_mod_cast (show 0 < N j by omega)
  have h : ((N j + 2 : ℕ) : ℝ) ≤ (N j : ℝ) * 2 := by
    exact_mod_cast (show N j + 2 ≤ N j * 2 by omega)
  have hlog := Real.log_le_log (by positivity) h
  rw [Real.log_mul hn.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))]
  change Real.log _ ≤ 1 * (6 + Real.log (N j : ℝ))
  linarith only [hlog, htwo]

/-- info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection.burnol_diagonal_lateSolve_barrier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms burnol_diagonal_lateSolve_barrier

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
