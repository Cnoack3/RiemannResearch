import RiemannResearch.RH.ParetoRoughTailCertificates
import Mathlib.Analysis.Normed.Group.Tannery

/-!
Actual reciprocal-square sieve mass vanishes under factorial exhaustion.
This is not an estimate on the original full legal tail norm. The final
rational expression is the explicit relaxed contrast variance derived in
the research note; its identification with Möbius synthesis is not asserted
by this module. No full-tail convergence is inferred.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

theorem coprimePairMass_norm_le_unsieved (P p : ℕ) :
    ‖coprimePairMass P p‖ ≤ coprimePairMass 1 p := by
  by_cases hp : coprimePairIndex P p
  · have hp1 : coprimePairIndex 1 p := ⟨hp.1, hp.2.1, by simp⟩
    rw [coprimePairMass, if_pos hp, coprimePairMass, if_pos hp1]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · rw [coprimePairMass, if_neg hp, norm_zero]
    exact coprimePairMass_nonneg 1 p

theorem coprimePairMass_factorial_eventually_zero (p : ℕ) :
    ∀ᶠ n : ℕ in atTop, coprimePairMass (n+2).factorial p = 0 := by
  filter_upwards [eventually_ge_atTop p] with n hn
  have hnot : ¬ coprimePairIndex (n+2).factorial p := by
    intro hp
    have hp3 := hp.1
    have hd : p ∣ (n+2).factorial := Nat.dvd_factorial (by omega) (by omega)
    have hdone : p ∣ 1 := by
      simpa only [show Nat.gcd p (n+2).factorial = 1 from hp.2.2] using
        Nat.dvd_gcd (dvd_refl p) hd
    have hpeq := Nat.dvd_one.mp hdone
    omega
  simp [coprimePairMass, hnot]

/-- Dominated convergence of the actual arithmetic mass, without a prime-rate input. -/
theorem coprimePairMass_factorial_tsum_tendsto_zero :
    Tendsto (fun n : ℕ => ∑' p, coprimePairMass (n+2).factorial p) atTop (𝓝 0) := by
  have hp : ∀ p, Tendsto (fun n : ℕ => coprimePairMass (n+2).factorial p)
      atTop (𝓝 (0 : ℝ)) := by
    intro p
    apply tendsto_const_nhds.congr'
    exact (coprimePairMass_factorial_eventually_zero p).mono (fun n hn => hn.symm)
  have hdom : ∀ᶠ n : ℕ in atTop, ∀ p,
      ‖coprimePairMass (n+2).factorial p‖ ≤ coprimePairMass 1 p :=
    Eventually.of_forall (fun n p => coprimePairMass_norm_le_unsieved _ p)
  simpa using tendsto_tsum_of_dominated_convergence (coprimePairMass_summable 1) hp hdom

theorem coprimeReciprocalSquareMass_factorial_tendsto_one :
    Tendsto (fun n : ℕ => coprimeReciprocalSquareMass (n+2).factorial)
      atTop (𝓝 1) := by
  simpa [coprimeReciprocalSquareMass] using
    tendsto_const_nhds.add coprimePairMass_factorial_tsum_tendsto_zero

/-- Pure exact algebra for the centered two-level sieve contrast. -/
theorem sieveContrast_variance_exact (S R : ℝ) (hS : S ≠ 0) (hSR : S-R ≠ 0) :
    (((S+1)/S - (S+1)/(S-R))^2 * (S-R) + ((S+1)/S)^2 * R)/2 =
      (S+1)^2 * R / (2*S*(S-R)) := by
  field_simp
  <;> ring

/-- This exact relaxed variance tends to zero; no full-energy conclusion is claimed. -/
theorem factorial_sieveContrast_variance_tendsto_zero :
    Tendsto (fun n : ℕ =>
      ((∑' p, coprimePairMass 2 p)+1)^2 * (∑' p, coprimePairMass (n+2).factorial p) /
      (2*(∑' p, coprimePairMass 2 p)*
        ((∑' p, coprimePairMass 2 p) - (∑' p, coprimePairMass (n+2).factorial p))))
      atTop (𝓝 0) := by
  let S : ℝ := ∑' p, coprimePairMass 2 p
  have hS : 0 < S :=
    CoefficientStabilization.TailCapacity.coprimePairMass_tsum_pos 2 (by decide) (by decide)
  have hR := coprimePairMass_factorial_tsum_tendsto_zero
  have hnum := (tendsto_const_nhds (x := (S+1)^2)).mul hR
  have hden := (tendsto_const_nhds (x := 2*S)).mul
    ((tendsto_const_nhds (x := S)).sub hR)
  have hz : 2*S*(S-0) ≠ 0 := by positivity
  have ht := hnum.div hden hz
  change Tendsto (fun n : ℕ => (S+1)^2 * (∑' p, coprimePairMass (n+2).factorial p) /
    (2*S*(S-(∑' p, coprimePairMass (n+2).factorial p)))) atTop
    (𝓝 (((S+1)^2*0)/(2*S*(S-0)))) at ht
  simpa only [mul_zero, zero_div] using ht

end RiemannResearch.RH.Pareto
