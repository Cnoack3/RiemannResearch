import RiemannResearch.RH.CanonicalMobiusStretchedEnergy
import RiemannResearch.RH.ParetoAnnihilatorTail

/-!
# Stretched lower barriers for complete arithmetic annihilator tails

Source: the user's requested transfer audit, 28 September 2026, and the
repository's exact-head Cauchy--Schwarz argument. No novelty is asserted.

The checked full canonical energy estimate transfers to an unconditional
necessary tail-growth condition on every annihilator with nonzero mean.
Frequently bounded tails at the improved scale suffice to force zero mean.
The tail upper bound itself remains an explicit, open hypothesis.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- A vanishing additive term does not affect a positive-product obstruction. -/
theorem tendsto_atTop_of_pos_le_add_mul_tendsto_zero
    {u b t : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hu : Tendsto u atTop (𝓝 0))
    (hb0 : ∀ᶠ n in atTop, 0 ≤ b n)
    (hb : Tendsto b atTop (𝓝 0))
    (hprod : ∀ᶠ n in atTop, c ≤ u n + t n * b n) :
    Tendsto t atTop atTop := by
  apply tendsto_atTop_of_pos_le_mul_tendsto_zero (by linarith : 0 < c / 2) hb0 hb
  filter_upwards [hprod, hu.eventually_lt_const (by linarith : 0 < c / 2)] with n hn hun
  linarith

end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis

/-- A complete-energy bound transfers to every smaller stretched tail scale. -/
theorem annihilator_stretched_tail_tendsto_atTop_of_energy
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ N : ℕ in atTop,
      ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 ≤ 8 + C * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))))
    (b : ℝ) (hb : b < a) (z : ThresholdHilbert)
    (hz : z ∈ closedSpaceᗮ) (hmean : inner ℝ z hilbertOne ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℝ) *
      Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) *
      ‖hilbertTailShift z N‖ ^ 2) atTop atTop := by
  let φ : ℕ → ℝ := fun N => logProductPower (1 / 11) (6 + Real.log (N : ℝ))
  have hL : Tendsto (fun N : ℕ => 6 + Real.log (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 6
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hφ : Tendsto φ atTop atTop :=
    (tendsto_logProductPower_atTop (1 / 11) (by norm_num)).comp hL
  have heps : Tendsto (fun N => Real.exp (-(a - b) * φ N)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_comp_nhds_zero.mpr
    exact hφ.const_mul_atTop_of_neg (by linarith)
  have hsmall : Tendsto (fun N => C * Real.exp (-(a - b) * φ N))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using heps.const_mul C
  have htail : Tendsto (fun N => 8 * ‖hilbertTailShift z N‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (hilbertTailShift_energy_tendsto_zero z).const_mul 8
  apply tendsto_atTop_of_pos_le_add_mul_tendsto_zero
    (sq_pos_of_ne_zero hmean) htail
    (Eventually.of_forall (fun N => mul_nonneg hC (Real.exp_pos _).le)) hsmall
  filter_upwards [henergy] with N hN
  have hlower := annihilator_tail_product_lower z hz N
    (canonicalMobiusHilbert_mem_closedSpace N) (canonicalMobiusHilbert_exact N)
  have hexp : Real.exp (-b * φ N) * Real.exp (-(a - b) * φ N) =
      Real.exp (-a * φ N) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    (inner ℝ z hilbertOne) ^ 2 ≤ ‖hilbertTailShift z N‖ ^ 2 *
        (8 + C * (N : ℝ) * Real.exp (-a * φ N)) :=
      hlower.trans (mul_le_mul_of_nonneg_left hN (sq_nonneg _))
    _ = 8 * ‖hilbertTailShift z N‖ ^ 2 +
        ((N : ℝ) * Real.exp (-b * φ N) * ‖hilbertTailShift z N‖ ^ 2) *
          (C * Real.exp (-(a - b) * φ N)) := by
      rw [← hexp]
      ring

/-- The arithmetic provider supplies a universal positive exponent. Every
strictly smaller positive exponent improves the previous normalized-tail
divergence theorem by a stretched exponential factor. -/
theorem exists_annihilator_stretched_tail_barrier :
    ∃ a : ℝ, 0 < a ∧ ∀ b : ℝ, 0 < b → b < a →
      ∀ z : ThresholdHilbert, z ∈ closedSpaceᗮ → inner ℝ z hilbertOne ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℝ) *
        Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) *
        ‖hilbertTailShift z N‖ ^ 2) atTop atTop := by
  obtain ⟨a, ha, C, hC, henergy⟩ := canonicalMobiusResidual_eventual_stretched_energy
  refine ⟨a, ha, ?_⟩
  intro b _hb hb z hz hmean
  exact annihilator_stretched_tail_tendsto_atTop_of_energy hC henergy b hb z hz hmean

/-- At one universal positive stretched scale, a cofinal bounded tail forces
zero mean. This is a conditional transfer theorem, not a tail upper bound. -/
theorem exists_annihilator_inner_one_eq_zero_of_frequently_bounded_stretched_tail :
    ∃ b : ℝ, 0 < b ∧ ∀ z : ThresholdHilbert, z ∈ closedSpaceᗮ →
      ∀ K : ℝ, (∃ᶠ N : ℕ in atTop, (N : ℝ) *
        Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) *
        ‖hilbertTailShift z N‖ ^ 2 ≤ K) → inner ℝ z hilbertOne = 0 := by
  obtain ⟨a, ha, hbarrier⟩ := exists_annihilator_stretched_tail_barrier
  refine ⟨a / 2, by linarith, ?_⟩
  intro z hz K hbounded
  by_contra hmean
  have ht := hbarrier (a / 2) (by linarith) (by linarith) z hz hmean
  obtain ⟨N, hN, hN'⟩ :=
    (hbounded.and_eventually (ht.eventually_gt_atTop K)).exists
  linarith

/-- A weaker cofinal tail bound than the old O(1/N) condition already suffices
for RH. No such bound on the actual limiting residual is supplied here. -/
theorem exists_riemannHypothesis_of_frequently_bounded_stretched_residual_tail :
    ∃ b : ℝ, 0 < b ∧ ∀ K : ℝ,
      (∃ᶠ N : ℕ in atTop, (N : ℝ) *
        Real.exp (-b * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) *
        residualTailEnergy N ≤ K) → RiemannHypothesis := by
  obtain ⟨b, hb, hzero⟩ :=
    exists_annihilator_inner_one_eq_zero_of_frequently_bounded_stretched_tail
  refine ⟨b, hb, ?_⟩
  intro K hbounded
  have hm := hzero limitResidual limitResidual_mem_orthogonal K hbounded
  rw [limitResidual_inner_one] at hm
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (limitEnergy_zero_iff_mem.mp hm))

/-- At the full provider exponent, arbitrarily small cofinal weighted tail
products suffice. This is the direct quantitative hypothesis left by the
energy estimate; no positive decay margin in the exponent is required. -/
theorem limitEnergy_eq_zero_of_cofinally_small_stretched_tail
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ N : ℕ in atTop,
      ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 ≤ 8 + C * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop,
      (N : ℝ) * Real.exp (-a * logProductPower (1 / 11)
        (6 + Real.log (N : ℝ))) * residualTailEnergy N < ε) :
    limitEnergy = 0 := by
  by_contra hne
  have hc : 0 < limitEnergy ^ 2 := sq_pos_of_ne_zero hne
  have hden : 0 < 2 * (C + 1) := by linarith
  have heps : 0 < limitEnergy ^ 2 / (2 * (C + 1)) := div_pos hc hden
  have htail : ∀ᶠ N : ℕ in atTop,
      residualTailEnergy N < limitEnergy ^ 2 / 16 :=
    residualTailEnergy_tendsto_zero.eventually_lt_const (by positivity)
  obtain ⟨N, hsmallN, henergyN, htailN⟩ :=
    ((hsmall _ heps).and_eventually (henergy.and htail)).exists
  let X : ℝ := (N : ℝ) * Real.exp (-a * logProductPower (1 / 11)
    (6 + Real.log (N : ℝ))) * residualTailEnergy N
  have hX : 0 ≤ X :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (Real.exp_pos _).le)
      (residualTailEnergy_nonneg N)
  have hXsmall : X * (2 * (C + 1)) < limitEnergy ^ 2 :=
    (lt_div_iff₀ hden).mp hsmallN
  have hlower := residual_tail_product_lower N
    (canonicalMobiusHilbert_mem_closedSpace N) (canonicalMobiusHilbert_exact N)
  have hbound : limitEnergy ^ 2 ≤ 8 * residualTailEnergy N + C * X := by
    calc
      limitEnergy ^ 2 ≤ residualTailEnergy N *
          (8 + C * (N : ℝ) * Real.exp (-a * logProductPower (1 / 11)
            (6 + Real.log (N : ℝ)))) :=
        hlower.trans (mul_le_mul_of_nonneg_left henergyN (residualTailEnergy_nonneg N))
      _ = 8 * residualTailEnergy N + C * X := by dsimp [X]; ring
  nlinarith

/-- The checked arithmetic estimate leaves only the explicit cofinal-small
tail product assumption at its own exponent. -/
theorem exists_riemannHypothesis_of_cofinally_small_stretched_residual_tail :
    ∃ a : ℝ, 0 < a ∧
      ((∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop,
        (N : ℝ) * Real.exp (-a * logProductPower (1 / 11)
          (6 + Real.log (N : ℝ))) * residualTailEnergy N < ε) → RiemannHypothesis) := by
  obtain ⟨a, ha, C, hC, henergy⟩ := canonicalMobiusResidual_eventual_stretched_energy
  refine ⟨a, ha, ?_⟩
  intro hsmall
  have hz := limitEnergy_eq_zero_of_cofinally_small_stretched_tail hC henergy hsmall
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (limitEnergy_zero_iff_mem.mp hz))

end RiemannResearch.RH.Pareto.CoefficientStabilization
