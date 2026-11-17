import RiemannResearch.RH.ExactHeadAtomOptimizer
import RiemannResearch.RH.ParetoExactHeadResidual
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

/-!
# Audit of uniform exact-head energy bounds
Source: the audited Exact-Head Green Profiles PDF, section 2.2 and the
supplement's repeated uses of q_x <= 1. Boundedness of these *constrained*
residuals is an RH-strength hypothesis, not the unconstrained zero trial.
The results are conditional implications, not proofs of boundedness or RH.
PDF: https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadEnergyAudit
open ExactHeadAtomOptimizer MobiusHeadGreen FloorProfileExtension
open RiemannResearch.Analysis.FiniteProfileEnergy

theorem zero_coefficients_not_exact_head (x : ℕ) (hx : 1 ≤ x) :
    ¬ (∀ d : ℕ, 1 ≤ d → d ≤ x →
      (0 : ℝ) = (ArithmeticFunction.moebius d : ℝ)) := by
  intro h
  simpa using h 1 (by omega) hx

theorem atom_energy_lower_bound_at_zeta_zero
    (P x : ℕ) (hx : x < P)
    (hcover : ∀ d, 1 ≤ d → d ≤ x → ArithmeticFunction.moebius d ≠ 0 → d ∣ P)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ((2 * s.re - 1) / ‖s‖ ^ 2) * ((x : ℝ) + 1)^(2 * s.re - 1) ≤
      progressionWeight P P + atomEnergy P x := by
  have hp : 0 < P := lt_of_le_of_lt (Nat.zero_le x) hx
  obtain ⟨c,hc0,hcd,hcn⟩ := exists_mobius_head_normal_coefficients P x hx.le hcover
  have heq : q P c = atomEnergy P x := by
    unfold q atomEnergy energy
    apply Finset.sum_congr rfl
    intro r hr
    rw [floor_residual_eq_atomResidual P x hp c hc0 hcd hcn r hr]
  let f := hilbertExtension P hp (Finset.Icc 1 P) c
    (fun d hd => (Finset.mem_Icc.mp hd).1)
  have hf : f ∈ hilbertLegalClosure (Set.Ici 1) := hilbertExtension_legal _ _ _ _ _
  have hh : ∀ k, 0 < k → k ≤ x → hilbertSequence f k = 1 := by
    exact hilbertExtension_head P hp _ c _ x hx (mobius_floor_head P x hx.le c hc0)
  have he := legal_exact_head_residual_lower_bound (Set.Ici 1)
    (by intro a ha; exact ha) s hs hs1 hz hf hh
  dsimp only [f] at he
  rwa [actual_energy_split P hp c hcd, heq] at he

/-- Even boundedness on arbitrarily late stages suffices. The periods need not
be squarefree, and no energy convergence, A1, or A2 hypothesis is used. -/
theorem riemannHypothesis_of_cofinal_atom_energy_bound (B : ℝ)
    (hdata : ∀ J : ℕ, ∃ P x : ℕ, J ≤ x ∧ x < P ∧
      (∀ d, 1 ≤ d → d ≤ x → ArithmeticFunction.moebius d ≠ 0 → d ∣ P) ∧
      atomEnergy P x ≤ B) : RiemannHypothesis := by
  choose P x hx hP hcover hB using hdata
  have hp (J : ℕ) : 0 < P J := lt_of_le_of_lt (Nat.zero_le (x J)) (hP J)
  choose c hc0 hcd hcn using
    (fun J => exists_mobius_head_normal_coefficients (P J) (x J) (hP J).le (hcover J))
  let hd := fun J d (h : d ∈ Finset.Icc 1 (P J)) => (Finset.mem_Icc.mp h).1
  let f (J : ℕ) := hilbertExtension (P J) (hp J) (Finset.Icc 1 (P J)) (c J) (hd J)
  refine riemannHypothesis_of_bounded_exact_head_residuals (Set.Ici 1)
    (by intro a ha; exact ha) f (fun J => hilbertExtension_legal _ _ _ _ _) ?_ (1 + B) ?_
  · intro J k hk hkJ
    exact hilbertExtension_head (P J) (hp J) _ (c J) _ (x J) (hP J)
      (mobius_floor_head (P J) (x J) (hP J).le (c J) (hc0 J)) k hk (hkJ.trans (hx J))
  · intro J
    have heq : q (P J) (c J) = atomEnergy (P J) (x J) := by
      unfold q atomEnergy energy
      apply Finset.sum_congr rfl
      intro r hr
      rw [floor_residual_eq_atomResidual (P J) (x J) (hp J) (c J)
        (hc0 J) (hcd J) (hcn J) r hr]
    have hterm : progressionWeight (P J) (P J) ≤ 1 := by
      have h := Finset.single_le_sum (s := Finset.Icc 1 (P J))
        (f := progressionWeight (P J)) (fun r _ => progressionWeight_nonneg _ r)
        (Finset.mem_Icc.mpr ⟨hp J,le_rfl⟩)
      simpa [ExactHeadGreen.period_mass (P J) (hp J)] using h
    change ‖hilbertOne - hilbertExtension (P J) (hp J) _ (c J) _‖^2 ≤ _
    rw [actual_energy_split (P J) (hp J) (c J) (hcd J),heq]
    linarith [hB J]

theorem riemannHypothesis_of_primorial_atom_energy_le_one
    (h : ∀ x, atomEnergy (greenPeriod x) x ≤ 1) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_atom_energy_bound 1
  intro J
  exact ⟨greenPeriod J,J,le_rfl,greenPeriod_gt J,greenPeriod_covers J,h J⟩


/-- The paper uses P = primorial x, including the primes at most x. Its
claimed uniform upper bound is sufficient for RH even without a decay rate. -/
theorem riemannHypothesis_of_paper_atom_energy_bound (B : ℝ)
    (h : ∀ x : ℕ, 2 < x → atomEnergy (primorial x) x ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_atom_energy_bound B
  intro J
  refine ⟨primorial (J + 3), J + 3, by omega, lt_primorial_self (by omega), ?_,
    h (J + 3) (by omega)⟩
  intro d hd hdx hmu
  exact (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu).dvd_primorial.trans
    (primorial_dvd_primorial hdx)

end RiemannResearch.RH.Pareto.ExactHeadEnergyAudit
