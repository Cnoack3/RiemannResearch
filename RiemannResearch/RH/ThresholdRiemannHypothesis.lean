import RiemannResearch.RH.ArithmeticMellinIdentity
import RiemannResearch.RH.WeilExplicitFormula.ZetaReflect
import RiemannResearch.RH.RiemannHypothesisStrip
/-!
# Two-seed approximation implies the actual Riemann hypothesis

Source: Christian Noack, RH_Two_Seed_Threshold.tex, September 8, 2026,
Sections 2 and 4 (statement), and the actual Mellin providers developed from
RH_CRT_Packet_Research_2026-09-09.md, Section 9 (proof ingredients).
The proof separates the target from every legal generator at a hypothetical
right-half-strip zeta zero, extends by continuous linearity to the actual
weighted Hilbert closure, then uses zeta reflection. All positive integer
dilations remain available. No Nyman--Beurling criterion, two-seed rigidity,
or RH bridge is assumed.

This proves the approximation-to-RH implication, not its converse. The
positive distance theorem also discharges ArithmeticZeroObstructionTarget.
-/

open Set
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem paretoMellin_zero_on_legalClosure_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A) :
    paretoMellin f s = 0 := by
  let L := paretoMellinContinuous s hs
  have hspan : legalSeedSpan A ≤ L.ker.map hilbertSequenceLinear := by
    apply Submodule.span_le.2
    rintro g ⟨a, ha, m, hm, rfl⟩
    refine ⟨hilbertDilation m hm (digitHilbert a 1 (hA a ha) (by omega)), ?_, ?_⟩
    · change paretoMellin _ s = 0
      rw [paretoMellin_generator_zeta a m (hA a ha) hm s hs hs1, hz]
      simp
    · exact hilbertDilation_digit_one_sequence a m (hA a ha) hm
  have hlegal : hilbertLegalSubspace A ≤ L.ker := by
    intro g hg
    obtain ⟨v, hv, hvg⟩ := hspan hg
    have he : v = g := hilbertSequence_injective hvg
    exact he ▸ hv
  have hc := Submodule.topologicalClosure_mono hlegal
  rw [L.isClosed_ker.submodule_topologicalClosure_eq] at hc
  exact hc hf

theorem zeta_ne_zero_of_hilbertOne_mem_legalClosure
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hmem : hilbertOne ∈ hilbertLegalClosure A)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have h := paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz hmem
  rw [paretoMellin_one s hs] at h
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  exact (one_div_ne_zero hs0) h

theorem riemannHypothesis_of_hilbertOne_mem_legalClosure
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hmem : hilbertOne ∈ hilbertLegalClosure A) : RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hright (s : ℂ) (hsz : riemannZeta s = 0)
      (hs0 : 0 < s.re) (hs1 : s.re < 1) : s.re ≤ 1 / 2 := by
    by_contra h
    have hs : 1 / 2 < s.re := lt_of_not_ge h
    have hsne : s ≠ 1 := by intro he; simp [he] at hs1
    exact zeta_ne_zero_of_hilbertOne_mem_legalClosure A hA hmem s hs hsne hsz
  have hr := Zeta23.zeta_reflect_zero ρ ⟨hz, h0, h1⟩
  have hrbound := hright (Zeta23.reflect ρ) hr.1 hr.2.1 hr.2.2
  have hbnd := hright ρ hz h0 h1
  simp [Zeta23.reflect] at hrbound
  linarith

theorem riemannHypothesis_of_twoSeed_closure
    (hmem : hilbertOne ∈ hilbertLegalClosure {2, 3}) : RiemannHypothesis := by
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure {2, 3} _ hmem
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> norm_num
/-- Every off-line zeta zero gives a positive distance obstruction for the
entire closed legal space, with the original weighted norm. -/
theorem legalClosure_distance_sq_lower_bound_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0)
    {f : ThresholdHilbert} (hf : f ∈ hilbertLegalClosure A) :
    (2 * s.re - 1) / ‖s‖ ^ 2 ≤ ‖hilbertOne - f‖ ^ 2 := by
  have hfzero := paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz hf
  have heval : paretoMellin (hilbertOne - f) s = 1 / s := by
    change paretoMellinContinuous s hs (hilbertOne - f) = _
    rw [map_sub]
    change paretoMellin hilbertOne s - paretoMellin f s = _
    rw [paretoMellin_one s hs, hfzero, sub_zero]
  have hb := paretoMellin_norm_sq_le (hilbertOne - f) s hs
  rw [heval, norm_div, norm_one, div_pow, one_pow] at hb
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hm := (le_div_iff₀ hd).mp hb
  have he : (1 / ‖s‖ ^ 2) * (2 * s.re - 1) = (2 * s.re - 1) / ‖s‖ ^ 2 := by ring
  rwa [he] at hm

/-- Discharges the previously recorded actual two-seed zero obstruction. -/
theorem arithmeticZeroObstruction : ArithmeticZeroObstructionTarget := by
  intro ρ hz hhalf hone F hF
  have hA : ∀ a ∈ ({2, 3} : Set ℕ), 0 < a := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> norm_num
  have hne : ρ ≠ 1 := by intro he; simp [he] at hone
  have h := legalClosure_distance_sq_lower_bound_of_zeta {2, 3} hA ρ hhalf hne hz
    ((hilbertLegalSubspace {2, 3}).le_topologicalClosure hF)
  rwa [norm_sub_rev] at h


/-- Density of the actual legal space in the Pareto Hilbert norm implies
Mathlib's Riemann hypothesis, with no separate criterion hypothesis. -/
theorem riemannHypothesis_of_legalClosure_eq_top
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hdense : hilbertLegalClosure A = ⊤) : RiemannHypothesis := by
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure A hA
  rw [hdense]
  trivial

end
end RiemannResearch.RH.Pareto
