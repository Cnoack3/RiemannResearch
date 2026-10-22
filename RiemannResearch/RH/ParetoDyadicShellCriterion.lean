import RiemannResearch.RH.ParetoResidualShell
import RiemannResearch.RH.ParetoStretchedAnnihilatorTail

/-!
# Dyadic signed-shell criteria at the stretched tail scale

Source: user-requested shell audit, 28 September 2026. The proofs combine
the existing exact shell identities with the checked stretched annihilator
barrier. No mathematical novelty is claimed.

The telescoping identities are unconditional. Every upper-control statement
is explicitly a conditional research reduction: no signed-shell provider
is proved here, and no unconditional RH conclusion is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto

/-- Weighted dyadic bookkeeping for any Hilbert vector and any real weight.
There is no positivity or decay assumption on the weight. -/
theorem hilbert_weighted_dyadic_shell_telescope
    (f : ThresholdHilbert) (w : ℕ → ℝ) (N K : ℕ) :
    w (2 ^ K * N) * ‖hilbertTailShift f (2 ^ K * N)‖ ^ 2 =
      w N * ‖hilbertTailShift f N‖ ^ 2 -
        ∑ j ∈ Finset.range K,
          (w (2 * (2 ^ j * N)) * hilbertShellPairing f f (2 ^ j * N) (2 ^ j * N) -
            (w (2 * (2 ^ j * N)) - w (2 ^ j * N)) *
              ‖hilbertTailShift f (2 ^ j * N)‖ ^ 2) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hn : 2 ^ (K + 1) * N = 2 * (2 ^ K * N) := by
      rw [pow_succ]
      ring
    have hs := hilbert_tail_shell_pairing f f (2 ^ K * N) (2 ^ K * N)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      ← two_mul (2 ^ K * N)] at hs
    rw [hn, Finset.sum_range_succ]
    nlinarith [congrArg (fun t : ℝ => w (2 * (2 ^ K * N)) * t) hs]

/-- Positive starting cutoffs have a cofinal dyadic orbit. -/
theorem dyadicCutoff_tendsto_atTop (N : ℕ) (hN : 0 < N) :
    Tendsto (fun K : ℕ => 2 ^ K * N) atTop atTop := by
  apply tendsto_atTop_mono (f := fun K : ℕ => K) _ tendsto_id
  intro K
  calc
    K ≤ 2 ^ K := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ 2 ^ K * N := by
      have h := Nat.mul_le_mul_left (2 ^ K) hN
      simpa using h

namespace CoefficientStabilization

/-- The signed expression that actually equals shell energy. The local
projection term cannot be dropped using global orthogonality. -/
def residualSignedShell (N : ℕ) : ℝ :=
  hilbertShellPairing limitResidual
      (canonicalMobiusHilbert N - limitProjection) N N -
    inner ℝ (hilbertTailShift limitResidual (2 * N))
      (hilbertTailShift (canonicalMobiusHilbert (2 * N) - canonicalMobiusHilbert N)
        (2 * N))

theorem residualSignedShell_eq_energy (N : ℕ) :
    residualSignedShell N = hilbertShellPairing limitResidual limitResidual N N := by
  have h := residual_canonicalMobius_shell_pairing N N
  rw [← two_mul N] at h
  have he :
      hilbertShellPairing limitResidual (hilbertOne - canonicalMobiusHilbert N) N N =
      hilbertShellPairing limitResidual limitResidual N N -
        hilbertShellPairing limitResidual (canonicalMobiusHilbert N - limitProjection) N N := by
    unfold hilbertShellPairing
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    change limitResidual (n + N) * (hilbertOne (n + N) - canonicalMobiusHilbert N (n + N)) =
      limitResidual (n + N) * (hilbertOne (n + N) - limitProjection (n + N)) -
        limitResidual (n + N) * (canonicalMobiusHilbert N (n + N) - limitProjection (n + N))
    ring
  rw [he] at h
  dsimp [residualSignedShell]
  linarith

/-- The net shell gain after paying for growth of the chosen weight. -/
def residualWeightedShellGain (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  w (2 * N) * residualSignedShell N -
    (w (2 * N) - w N) * residualTailEnergy N

theorem residual_weighted_dyadic_telescope (w : ℕ → ℝ) (N K : ℕ) :
    w (2 ^ K * N) * residualTailEnergy (2 ^ K * N) =
      w N * residualTailEnergy N -
        ∑ j ∈ Finset.range K, residualWeightedShellGain w (2 ^ j * N) := by
  simpa only [residualWeightedShellGain, residualSignedShell_eq_energy,
    residualTailEnergy] using hilbert_weighted_dyadic_shell_telescope limitResidual w N K

/-- Exact cofinal criterion on one dyadic orbit, retaining signs and allowing
individual shells to have negative gain. This is a reformulation, not a bound. -/
theorem cofinally_small_dyadic_tail_iff_signed_gain (w : ℕ → ℝ) (N : ℕ) :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ K : ℕ in atTop,
      w (2 ^ K * N) * residualTailEnergy (2 ^ K * N) < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ᶠ K : ℕ in atTop,
      w N * residualTailEnergy N - ε <
        ∑ j ∈ Finset.range K, residualWeightedShellGain w (2 ^ j * N)) := by
  constructor <;> intro h ε hε
  · exact (h ε hε).mono (fun K hK => by
      rw [residual_weighted_dyadic_telescope] at hK
      linarith)
  · exact (h ε hε).mono (fun K hK => by
      rw [residual_weighted_dyadic_telescope]
      linarith)

/-- The smallest direct cofinal gain hypothesis at the supplied exponent.
Its signed cumulative estimate remains Open. -/
theorem limitEnergy_eq_zero_of_cofinal_dyadic_signed_gain
    {a C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ᶠ N : ℕ in atTop,
      ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 ≤ 8 + C * (N : ℝ) *
        Real.exp (-a * RiemannResearch.Analysis.logProductPower (1 / 11)
          (6 + Real.log (N : ℝ))))
    (N : ℕ) (hN : 0 < N)
    (hgain : ∀ ε : ℝ, 0 < ε → ∃ᶠ K : ℕ in atTop,
      (N : ℝ) * Real.exp (-a * RiemannResearch.Analysis.logProductPower (1 / 11)
          (6 + Real.log (N : ℝ))) * residualTailEnergy N - ε <
        ∑ j ∈ Finset.range K, residualWeightedShellGain
          (fun n => (n : ℝ) * Real.exp (-a *
            RiemannResearch.Analysis.logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
          (2 ^ j * N)) :
    limitEnergy = 0 := by
  apply limitEnergy_eq_zero_of_cofinally_small_stretched_tail hC henergy
  intro ε hε
  apply (dyadicCutoff_tendsto_atTop N hN).frequently
  exact ((cofinally_small_dyadic_tail_iff_signed_gain
    (fun n => (n : ℝ) * Real.exp (-a * RiemannResearch.Analysis.logProductPower (1 / 11)
      (6 + Real.log (n : ℝ)))) N).mpr hgain) ε hε

/-- At every strictly smaller positive stretched exponent, a cumulative gain
bounded below on a cofinal set already forces zero residual. This is an exact
criterion for zero residual; no bound on the gains is supplied. -/
theorem exists_stretched_signed_shell_criterion :
    ∃ a : ℝ, 0 < a ∧ ∀ b : ℝ, 0 < b → b < a → ∀ N : ℕ, 0 < N →
      (limitResidual = 0 ↔
        ∃ C : ℝ, ∃ᶠ K : ℕ in atTop, -C ≤
          ∑ j ∈ Finset.range K, residualWeightedShellGain
            (fun n => (n : ℝ) * Real.exp (-b *
              RiemannResearch.Analysis.logProductPower (1 / 11) (6 + Real.log (n : ℝ))))
            (2 ^ j * N)) := by
  obtain ⟨a, ha, hbarrier⟩ := exists_annihilator_stretched_tail_barrier
  refine ⟨a, ha, ?_⟩
  intro b hb hba N hN
  let w : ℕ → ℝ := fun n => (n : ℝ) * Real.exp (-b *
    RiemannResearch.Analysis.logProductPower (1 / 11) (6 + Real.log (n : ℝ)))
  constructor
  · intro hz
    refine ⟨0, (Eventually.of_forall ?_).frequently⟩
    intro K
    have ht (n : ℕ) : residualTailEnergy n = 0 := by
      have hs : hilbertTailShift limitResidual n = 0 := by
        ext i
        simp [hilbertTailShift, hz]
      simp [residualTailEnergy, hs]
    have he := residual_weighted_dyadic_telescope w N K
    simp only [ht, mul_zero, zero_sub] at he
    change - (0 : ℝ) ≤ ∑ j ∈ Finset.range K, residualWeightedShellGain w (2 ^ j * N)
    linarith
  · rintro ⟨C, hgain⟩
    by_contra hne
    have he : limitEnergy ≠ 0 := fun h => hne (limitResidual_zero_iff_energy_zero.mpr h)
    have hm : inner ℝ limitResidual hilbertOne ≠ 0 := by
      rwa [limitResidual_inner_one]
    have ht := (hbarrier b hb hba limitResidual limitResidual_mem_orthogonal hm).comp
      (dyadicCutoff_tendsto_atTop N hN)
    have hlarge : ∀ᶠ K : ℕ in atTop,
        w N * residualTailEnergy N + C <
          w (2 ^ K * N) * residualTailEnergy (2 ^ K * N) :=
      ht.eventually_gt_atTop (w N * residualTailEnergy N + C)
    obtain ⟨K, hK, hlargeK⟩ := (hgain.and_eventually hlarge).exists
    have htelescope := residual_weighted_dyadic_telescope w N K
    change -C ≤ ∑ j ∈ Finset.range K, residualWeightedShellGain w (2 ^ j * N) at hK
    linarith

end CoefficientStabilization
end RiemannResearch.RH.Pareto
