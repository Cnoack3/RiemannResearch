import RiemannResearch.RH.ParetoConductorEnergy

/-!
# The actual full-divisor enlargement and its exact Schur gain

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`,
Sections 2--4. The enlarged and old spaces are represented in the same
full-weight finite Hilbert space. The divisor partition is proved, so the
normal-equation value is the actual enlarged projection error.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra
open RiemannResearch.LinearAlgebra.ConditionalSchur
noncomputable section

/-- Distinct new conductors, including prime powers when the multiplier
shares a prime with the old period. -/
def conductorNewConductors (N b : ℕ) : Finset ℕ :=
  (N*b).divisors.filter (fun q => ¬ q ∣ N)

def conductorNewPacket (N b : ℕ) (q : conductorNewConductors N b) :
    EuclideanSpace ℝ (Fin (N*b)) := conductorHilbert N b (ramanujanPacket q.val)

/-- The actual divisor enlargement is precisely the old span plus the
span of the distinct new packets. No conductor is silently omitted. -/
theorem conductorEnlargedSpace_eq_augmented (N b : ℕ) (hN : 0 < N) (hb : 0 < b) :
    conductorSampledSpace N b (N*b) = conductorOldSpace N b ⊔
      Submodule.span ℝ (Set.range (conductorNewPacket N b)) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨q, ⟨hq, hq1⟩, rfl⟩
    by_cases hqN : q ∣ N
    · apply (show conductorOldSpace N b ≤ conductorOldSpace N b ⊔
        Submodule.span ℝ (Set.range (conductorNewPacket N b)) from le_sup_left)
      exact Submodule.subset_span ⟨q, ⟨hqN, hq1⟩, rfl⟩
    · apply (show Submodule.span ℝ (Set.range (conductorNewPacket N b)) ≤
        conductorOldSpace N b ⊔ Submodule.span ℝ (Set.range (conductorNewPacket N b))
        from le_sup_right)
      apply Submodule.subset_span
      refine ⟨⟨q, ?_⟩, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hq, (Nat.mul_pos hN hb).ne'⟩, hqN⟩
  · apply sup_le
    · apply Submodule.span_le.2
      rintro _ ⟨q, ⟨hq, hq1⟩, rfl⟩
      exact Submodule.subset_span
        ⟨q, ⟨dvd_trans hq (dvd_mul_right N b), hq1⟩, rfl⟩
    · apply Submodule.span_le.2
      rintro _ ⟨q, rfl⟩
      obtain ⟨hq, hqN⟩ := Finset.mem_filter.mp q.property
      have hqdiv : q.val ∣ N*b := Nat.dvd_of_mem_divisors hq
      have hqpos : 0 < q.val := Nat.pos_of_dvd_of_pos hqdiv (Nat.mul_pos hN hb)
      have hqne : q.val ≠ 1 := by
        intro h
        apply hqN
        simp [h]
      exact Submodule.subset_span ⟨q.val, ⟨hqdiv, by omega⟩, rfl⟩

/-- Exact gain for any solution of the actual residualized new-packet
normal equations. The right side retains every signed Gram interaction. -/
theorem conductor_schur_gain (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (c : conductorNewConductors N b → ℝ)
    (hc : ∀ i, inner ℝ (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
      (finiteSchurCombination (packetResidual (conductorOldSpace N b) ∘
        conductorNewPacket N b) c) =
      inner ℝ (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
        (packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1)))) :
    ‖packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1))‖ ^ 2 -
      ‖packetResidual (conductorSampledSpace N b (N*b)) (conductorHilbert N b (fun _ => 1))‖ ^ 2 =
      ∑ i, c i * inner ℝ
        (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
        (packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1))) := by
  have hp := augmented_projection_residual (conductorOldSpace N b)
    (conductorNewPacket N b) (conductorHilbert N b (fun _ => 1)) c hc
  simp only [← conductorEnlargedSpace_eq_augmented N b hN hb] at hp
  have he := finiteSchurResidual_norm_sq
    (packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1)))
    (packetResidual (conductorOldSpace N b) ∘ conductorNewPacket N b) c hc
  rw [hp] at he
  simp only [Function.comp_apply] at he
  linarith

/-- The actual finite Schur gain is always attained. In particular, no
inverse, normal-solution, or positive-definiteness assumption is required
to obtain the exact finite update. -/
theorem conductor_exists_schur_gain (N b : ℕ) (hN : 0 < N) (hb : 0 < b) :
    ∃ c : conductorNewConductors N b → ℝ,
      (∀ i, inner ℝ (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
        (finiteSchurCombination (packetResidual (conductorOldSpace N b) ∘
          conductorNewPacket N b) c) =
        inner ℝ (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
          (packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1)))) ∧
      ‖packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1))‖ ^ 2 -
        ‖packetResidual (conductorSampledSpace N b (N*b)) (conductorHilbert N b (fun _ => 1))‖ ^ 2 =
        ∑ i, c i * inner ℝ
          (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
          (packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1))) := by
  obtain ⟨c, hc⟩ := finiteSchur_exists_normal
    (packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1)))
    (packetResidual (conductorOldSpace N b) ∘ conductorNewPacket N b)
  exact ⟨c, hc, conductor_schur_gain N b hN hb c hc⟩

/-- The full infinite Pareto projection gain equals the finite signed
Schur gain. Thus the finite matrix quantity is exactly the one that enters
the actual all-scale product and summability criterion. -/
theorem conductor_infinite_schur_gain (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (c : conductorNewConductors N b → ℝ)
    (hc : ∀ i, inner ℝ (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
      (finiteSchurCombination (packetResidual (conductorOldSpace N b) ∘
        conductorNewPacket N b) c) =
      inner ℝ (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
        (packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1)))) :
    ConductorProjection.gain N (N*b) =
      ∑ i, c i * inner ℝ
        (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
        (packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1))) := by
  have hfinite := conductor_schur_gain N b hN hb c hc
  have hold := conductor_sampled_energy_eq N b N hN hb hN (dvd_mul_right N b)
  have hnew := conductor_sampled_energy_eq N b (N*b) hN hb
    (Nat.mul_pos hN hb) (dvd_refl (N*b))
  change ‖packetResidual (conductorOldSpace N b)
    (conductorHilbert N b (fun _ => 1))‖ ^ 2 = ConductorProjection.energy N at hold
  change ‖packetResidual (conductorSampledSpace N b (N*b))
    (conductorHilbert N b (fun _ => 1))‖ ^ 2 = ConductorProjection.energy (N*b) at hnew
  rw [hold, hnew] at hfinite
  have he := ConductorProjection.energy_step (dvd_mul_right N b) (Nat.mul_pos hN hb)
  linarith

/-- The normalized gain used by the all-scale theorem is the actual
finite Schur value divided by the actual old Pareto error. -/
theorem conductor_relativeGain_eq_schur (N b : ℕ) (hN : 0 < N) (hb : 0 < b)
    (c : conductorNewConductors N b → ℝ)
    (hc : ∀ i, inner ℝ (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
      (finiteSchurCombination (packetResidual (conductorOldSpace N b) ∘
        conductorNewPacket N b) c) =
      inner ℝ (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
        (packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1)))) :
    ConductorProjection.relativeGain N (N*b) =
      (∑ i, c i * inner ℝ
        (packetResidual (conductorOldSpace N b) (conductorNewPacket N b i))
        (packetResidual (conductorOldSpace N b) (conductorHilbert N b (fun _ => 1)))) /
          ConductorProjection.energy N := by
  unfold ConductorProjection.relativeGain
  rw [conductor_infinite_schur_gain N b hN hb c hc]

end
end RiemannResearch.RH.Pareto



/-!
Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`,
Section 2. The new-prime enumeration below includes the pure prime packet.
-/

namespace RiemannResearch.RH.Pareto

/-- For a genuinely new prime, the distinct newly introduced conductors
are exactly `p*d` with `d` an old divisor, including `d = 1`. -/
theorem conductorNewConductors_prime_not_dvd (Q p : ℕ)
    (hQ : 0 < Q) (hp : p.Prime) (hpQ : ¬ p ∣ Q) :
    conductorNewConductors Q p = Q.divisors.image (fun d => p * d) := by
  classical
  ext q
  simp only [conductorNewConductors, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hq, hqQ⟩
    have hqdiv : q ∣ p * Q := by
      simpa only [Nat.mul_comm Q p] using Nat.dvd_of_mem_divisors hq
    have hpq : p ∣ q := by
      by_contra hnot
      have hcop : Nat.Coprime q p := (hp.coprime_iff_not_dvd.mpr hnot).symm
      exact hqQ (hcop.dvd_mul_left.mp hqdiv)
    obtain ⟨d, rfl⟩ := hpq
    refine ⟨d, Nat.mem_divisors.mpr ⟨?_, hQ.ne'⟩, rfl⟩
    exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hqdiv
  · rintro ⟨d, hd, rfl⟩
    have hdQ := Nat.dvd_of_mem_divisors hd
    refine ⟨Nat.mem_divisors.mpr ⟨?_, (Nat.mul_pos hQ hp.pos).ne'⟩, ?_⟩
    · simpa only [Nat.mul_comm p Q] using Nat.mul_dvd_mul_left p hdQ
    · intro h
      exact hpQ (dvd_trans (dvd_mul_right p d) h)

end RiemannResearch.RH.Pareto
