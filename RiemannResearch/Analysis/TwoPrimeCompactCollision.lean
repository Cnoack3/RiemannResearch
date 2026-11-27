import RiemannResearch.Analysis.TorusCollisionReconstruction
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.PrimePhaseTorus
import RiemannResearch.Analysis.MontgomeryPhysicalGapTransfer

/-!
# Compact prime-character tests for exact collisions of zeta ordinates

Compact Orbit's infinite diagonal Parseval and FMZ comparison concerns one-ordinate
Fourier amplitudes. Here positive trigonometric polynomials on the two-prime torus
extract exact equal-ordinate pairs at fixed height. The two primes separate every
real ordinate. A uniform arithmetic bound in the subsequent height limit is a
separate input. Source for context: Compact Orbit, current proofs, “Unconditional
Parseval and FMZ convergence”; the finite-height computation is given below.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.TwoPrimeCompactCollision
open PrimePhaseTorus TorusCollisionReconstruction OrdinateCollisionCertificate
open ActualZeroOrdinate ActualZeroCollisionCertificate MontgomeryFormFactor

def unitPhase (p : ℕ) (t : ℝ) : ℂ := fourier 1 (primePhase p t)

theorem norm_unitPhase (p : ℕ) (t : ℝ) : ‖unitPhase p t‖ = 1 := by
  rw [unitPhase, fourier_one]
  exact Circle.norm_coe _

/-- Equality in both complex coordinates detects exact equality of heights. -/
theorem unitPhase_eq_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (s t : ℝ) :
    (unitPhase p s = unitPhase p t ∧ unitPhase q s = unitPhase q t) ↔ s = t := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have lift (p : ℕ) (h : unitPhase p s = unitPhase p t) : primePhase p s = primePhase p t := by
      simp only [unitPhase, fourier_one] at h
      exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext h)
    exact two_prime_phase_injective hp hq hpq (Prod.ext (lift p h₁) (lift q h₂))
  · rintro rfl
    exact ⟨rfl,rfl⟩

/-- Reading both coordinates as characters gives the physical Fourier frequency. -/
theorem unitPhase_powers (p q a b : ℕ) (t : ℝ) :
    unitPhase p t ^ a * unitPhase q t ^ b =
      occurrencePhase ((a:ℝ)*Real.log p + (b:ℝ)*Real.log q) t := by
  simp only [unitPhase, fourier_primePhase, Int.cast_one, one_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add, occurrencePhase]
  congr 1
  push_cast
  ring

variable {ι : Type*} [Fintype ι]

def compactEnergy (y : ι → ℝ) (M : ℕ) : ℝ :=
  fejerEnergy (fun i => unitPhase 2 (y i)) (fun i => unitPhase 3 (y i)) M

/-- The indices of the physical trace are logarithms of rational prime words. -/
def wordFrequency {M : ℕ} (a : Fin (M+1) × Fin (M+1)) : ℝ :=
  (a.1.val : ℝ) * Real.log 2 + (a.2.val : ℝ) * Real.log 3

theorem compactEnergy_eq_fourier (y : ι → ℝ) (M : ℕ) :
    compactEnergy y M =
      (∑ a : Fin (M+1) × Fin (M+1), ∑ b : Fin (M+1) × Fin (M+1),
        Complex.normSq (occurrenceAmplitude y (wordFrequency a - wordFrequency b))) /
        ((M+1 : ℕ) : ℝ)^4 := by
  unfold compactEnergy fejerEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [word, unitPhase_powers, wordFrequency, occurrencePhase, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phaseCollision_eq_ordinate (y : ι → ℝ) :
    phaseCollision (fun i => unitPhase 2 (y i)) (fun i => unitPhase 3 (y i)) =
      occurrenceCollision y := by
  classical
  simp only [phaseCollision, occurrenceCollision, unitPhase_eq_iff Nat.prime_two Nat.prime_three
    (by decide : (2 : ℕ) ≠ 3)]

theorem compactEnergy_tendsto (y : ι → ℝ) :
    Tendsto (compactEnergy y) atTop (𝓝 (occurrenceCollision y : ℝ)) := by
  rw [← phaseCollision_eq_ordinate y]
  exact fejerEnergy_tendsto_collision _ _ (fun i => norm_unitPhase 2 (y i))
    (fun i => norm_unitPhase 3 (y i))

theorem actualCollision_le_compactEnergy (T : ℝ) (M : ℕ) :
    (actualCollision T : ℝ) ≤ compactEnergy (copyOrdinate T) M := by
  change (occurrenceCollision (copyOrdinate T) : ℝ) ≤ _
  rw [← phaseCollision_eq_ordinate]
  exact phaseCollision_le_fejerEnergy _ _ (fun i => norm_unitPhase 2 (copyOrdinate T i))
    (fun i => norm_unitPhase 3 (copyOrdinate T i)) M

/-- The zero frequency in the compact Fourier sum forces its side length
to grow at least on the square-root occurrence-count scale of a certificate. -/
theorem compact_certificate_necessary_width {T : ℝ} {M : ℕ}
    (h : compactEnergy (copyOrdinate T) M < (Ncount 0 T : ℝ) + 2) :
    (Ncount 0 T : ℝ)^2 < ((Ncount 0 T : ℝ)+2) * ((M+1 : ℕ) : ℝ)^2 := by
  have hfloor := zero_word_floor_le_fejerEnergy
    (fun i => unitPhase 2 (copyOrdinate T i)) (fun i => unitPhase 3 (copyOrdinate T i))
    (fun i => norm_unitPhase 2 (copyOrdinate T i))
    (fun i => norm_unitPhase 3 (copyOrdinate T i)) M
  rw [card_copies] at hfloor
  exact (div_lt_iff₀ (by positivity)).mp (hfloor.trans_lt h)

/-- No fixed compact word window can certify the strict two-pair bound at
arbitrarily large heights, even though all sufficiently wide windows recover
the collision integer at each fixed height. -/
theorem fixed_window_eventually_exceeds_budget (M : ℕ) :
    ∀ᶠ T : ℝ in atTop, (Ncount 0 T : ℝ) + 2 ≤ compactEnergy (copyOrdinate T) M := by
  let c : ℝ := 1 / (4*Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall : c < 1 / (2*Real.pi) := by
    dsimp [c]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith [Real.pi_pos])
  let K := ((M+1 : ℕ) : ℝ)^2
  filter_upwards [eventually_count_ge_log_of_lt hsmall, eventually_ge_atTop ((K+2)/c),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (0:ℝ)] with T hN hT hlog hpos
  have hbase : K+2 ≤ c*T := by simpa only [mul_comm T c] using (div_le_iff₀ hc).mp hT
  have hn : K+2 ≤ (Ncount 0 T : ℝ) :=
    hbase.trans ((le_mul_of_one_le_right (mul_nonneg hc.le hpos) hlog).trans hN)
  by_contra! h
  have hstrict := compact_certificate_necessary_width h
  change (Ncount 0 T : ℝ)^2 < ((Ncount 0 T : ℝ)+2)*K at hstrict
  nlinarith [mul_nonneg (show 0 ≤ (Ncount 0 T : ℝ)+2 by positivity)
    (show 0 ≤ (Ncount 0 T : ℝ)-2-K by linarith)]

/-- A single finite compact Fourier test at each of cofinally many heights
suffices. Frequencies and cutoffs in these tests may depend on the height. -/
theorem global_iff_cofinal_compactEnergy :
    (RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1) ↔
      ∃ᶠ T : ℝ in atTop, ∃ M : ℕ, compactEnergy (copyOrdinate T) M < (Ncount 0 T : ℝ) + 2 := by
  rw [← frequently_collision_lt_count_add_two_iff_global]
  constructor
  · intro h
    apply h.mono
    intro T hT
    have hlt : (actualCollision T : ℝ) < (Ncount 0 T : ℝ) + 2 := by exact_mod_cast hT
    exact ((compactEnergy_tendsto (copyOrdinate T)).eventually_lt_const hlt).exists
  · intro h
    apply h.mono
    rintro T ⟨M, hM⟩
    have hlt := (actualCollision_le_compactEnergy T M).trans_lt hM
    exact_mod_cast hlt

end RiemannResearch.Analysis.TwoPrimeCompactCollision
