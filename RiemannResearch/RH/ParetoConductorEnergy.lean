import RiemannResearch.RH.ConductorProjectionChain
import RiemannResearch.RH.ParetoConductorSchur
import RiemannResearch.RH.ThresholdContractiveRepair

/-!
# Equality of finite full-weight conductor energy and complete Hilbert energy

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`, §§2--3,7.
The finite model is an exact representation of every finite legal optimization.
Both projected minima are compared using their actual minimizers. No density,
uniform energy bound, or arithmetic orthogonality provider is assumed.
-/

namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra.WeightedQuotientHilbert
noncomputable section

/-- Divisor packets of period Q, represented in an ambient period N*b. -/
def conductorSampledSpace (N b Q : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin (N*b))) :=
  Submodule.span ℝ ((fun q => conductorHilbert N b (ramanujanPacket q)) ''
    {q : ℕ | q ∣ Q ∧ 1 < q})

/-- Positive-coordinate sampling, with the complete periodized Pareto weights. -/
def conductorEvaluation (N b : ℕ) : ThresholdHilbert →ₗ[ℝ] EuclideanSpace ℝ (Fin (N*b)) where
  toFun f := conductorHilbert N b (hilbertSequence f)
  map_add' f g := by
    change coordinates (conductorFineWeight N b)
        (conductorSample N b (hilbertSequence (f+g))) = _
    have he : conductorSample N b (hilbertSequence (f+g)) =
        conductorSample N b (hilbertSequence f) + conductorSample N b (hilbertSequence g) := by
      funext i
      simp only [conductorSample, hilbertSequence_add, Pi.add_apply]
    rw [he, map_add] <;> rfl
  map_smul' c f := by
    change coordinates (conductorFineWeight N b)
        (conductorSample N b (hilbertSequence (c • f))) = _
    have he : conductorSample N b (hilbertSequence (c • f)) =
        c • conductorSample N b (hilbertSequence f) := by
      funext i
      simp only [conductorSample, hilbertSequence_smul, Pi.smul_apply]
    rw [he, map_smul] <;> rfl

theorem conductorEvaluation_packet (N b q : ℕ) :
    conductorEvaluation N b (ramanujanPacketHilbert q) =
      conductorHilbert N b (ramanujanPacket q) := by
  change conductorHilbert N b (hilbertSequence (ramanujanPacketHilbert q)) = _
  rw [hilbertSequence_ramanujanPacketHilbert]

theorem conductorEvaluation_one (N b : ℕ) :
    conductorEvaluation N b hilbertOne = conductorHilbert N b (fun _ => (1 : ℝ)) := by
  change coordinates (conductorFineWeight N b)
      (conductorSample N b (hilbertSequence hilbertOne)) = _
  rw [hilbertOne_sequence]
  have he : conductorSample N b (zeroAnchor (fun _ => (1 : ℝ))) =
      conductorSample N b (fun _ => (1 : ℝ)) := by
    funext i
    simp [conductorSample, zeroAnchor]
  rw [he] <;> rfl

theorem conductorEvaluation_mem_sampled (N b Q : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ ConductorProjection.space Q) :
    conductorEvaluation N b f ∈ conductorSampledSpace N b Q := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨q,rfl⟩ := hf
    rw [conductorEvaluation_packet]
    apply Submodule.subset_span
    exact ⟨q.val, ⟨Nat.dvd_of_mem_divisors (Finset.mem_filter.mp q.property).1,
      (Finset.mem_filter.mp q.property).2⟩, rfl⟩
  | zero => simp
  | add f g hf hg ihf ihg =>
    rw [map_add]
    exact (conductorSampledSpace N b Q).add_mem ihf ihg
  | smul c f hf ih =>
    rw [map_smul]
    exact (conductorSampledSpace N b Q).smul_mem c ih

theorem conductorSampledSpace_lift (N b Q : ℕ) (hQ : 0 < Q)
    {v : EuclideanSpace ℝ (Fin (N*b))} (hv : v ∈ conductorSampledSpace N b Q) :
    ∃ f : ThresholdHilbert, f ∈ ConductorProjection.space Q ∧ conductorEvaluation N b f = v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨q,hq,rfl⟩ := hv
    refine ⟨ramanujanPacketHilbert q, ?_, conductorEvaluation_packet N b q⟩
    apply Submodule.subset_span
    refine ⟨⟨q, ?_⟩, rfl⟩
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hq.1,hQ.ne'⟩,hq.2⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add v z hv hz ihv ihz =>
    obtain ⟨f,hf,he⟩ := ihv
    obtain ⟨g,hg,he'⟩ := ihz
    refine ⟨f+g,(ConductorProjection.space Q).add_mem hf hg, ?_⟩
    rw [map_add,he,he']
  | smul c v hv ih =>
    obtain ⟨f,hf,he⟩ := ih
    refine ⟨c • f,(ConductorProjection.space Q).smul_mem c hf, ?_⟩
    rw [map_smul,he]

private theorem conductor_space_sequence_properties (Q L : ℕ) (hQL : Q ∣ L)
    {f : ThresholdHilbert} (hf : f ∈ ConductorProjection.space Q) :
    (∃ C : ℝ, ∀ k, |hilbertSequence f k| ≤ C) ∧
      ∀ k, hilbertSequence f (k+L) = hilbertSequence f k := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨q,rfl⟩ := hf
    rw [hilbertSequence_ramanujanPacketHilbert]
    exact ⟨⟨_,ramanujanPacket_abs_le q⟩,
      ramanujanPacket_period_of_dvd q L
        (dvd_trans (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp q.property).1) hQL)⟩
  | zero =>
    have hz : hilbertSequence (0 : ThresholdHilbert) = 0 := hilbertSequenceLinear.map_zero
    rw [hz]
    exact ⟨⟨0, fun _ => by simp⟩, fun _ => rfl⟩
  | add f g hf hg ihf ihg =>
    obtain ⟨⟨C,hC⟩,hp⟩ := ihf
    obtain ⟨⟨D,hD⟩,hq⟩ := ihg
    refine ⟨⟨C+D, ?_⟩, ?_⟩
    · intro k
      simp only [hilbertSequence_add, Pi.add_apply]
      exact (abs_add_le _ _).trans (add_le_add (hC k) (hD k))
    · intro k
      simp only [hilbertSequence_add, Pi.add_apply, hp, hq]
  | smul c f hf ih =>
    obtain ⟨⟨C,hC⟩,hp⟩ := ih
    refine ⟨⟨|c| * C, ?_⟩, ?_⟩
    · intro k
      simpa only [hilbertSequence_smul, Pi.smul_apply, smul_eq_mul] using
        bounded_const_mul hC c k
    · intro k
      simp only [hilbertSequence_smul, Pi.smul_apply, hp]

/-- Sampling preserves the full residual objective on every old legal vector. -/
theorem conductorEvaluation_error_sq (N b Q : ℕ) (hN : 0 < N) (hb : 0 < b)
    (hQL : Q ∣ N*b) {f : ThresholdHilbert} (hf : f ∈ ConductorProjection.space Q) :
    ‖conductorHilbert N b (fun _ => (1 : ℝ)) - conductorEvaluation N b f‖^2 =
      ‖hilbertOne-f‖^2 := by
  obtain ⟨⟨C,hC⟩,hp⟩ := conductor_space_sequence_properties Q (N*b) hQL hf
  have hone : ∀ k : ℕ, |(fun _ => (1 : ℝ)) k| ≤ 1 := by intro k; norm_num
  have herror : ∀ k, |1-hilbertSequence f k| ≤ 1+C :=
    bounded_sub hone hC
  have hperiod : ∀ k, 1-hilbertSequence f (k+N*b) = 1-hilbertSequence f k := by
    intro k
    rw [hp]
  have he : conductorHilbert N b (fun _ => (1 : ℝ)) - conductorEvaluation N b f =
      conductorHilbert N b (fun k => 1-hilbertSequence f k) := by
    change coordinates (conductorFineWeight N b) (conductorSample N b (fun _ => (1 : ℝ))) -
      coordinates (conductorFineWeight N b) (conductorSample N b (hilbertSequence f)) = _
    rw [← map_sub]
    rfl
  rw [he, ← real_inner_self_eq_norm_sq,
    conductorHilbert_inner N b hN hb _ _ herror herror hperiod hperiod,
    norm_sub_rev hilbertOne f, hilbert_error_weighted]
  simp only [paretoInner, pow_two]

private theorem projection_error_sq_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] (t v : H) (hv : v ∈ K) :
    ‖t-K.starProjection t‖^2 ≤ ‖t-v‖^2 := by
  have ho : inner ℝ (t-K.starProjection t) (K.starProjection t-v) = 0 := by
    rw [real_inner_comm]
    exact (K.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal t)
      _ (K.sub_mem (K.starProjection_apply_mem t) hv)
  have he : t-v = (t-K.starProjection t) - -(K.starProjection t-v) := by abel
  rw [he, norm_sub_sq_real (t-K.starProjection t) (-(K.starProjection t-v)),
    inner_neg_right,ho,norm_neg]
  nlinarith [sq_nonneg ‖K.starProjection t-v‖]

/-- The actual finite full-weight minimum equals the complete Hilbert minimum. -/
theorem conductor_sampled_energy_eq (N b Q : ℕ)
    (hN : 0 < N) (hb : 0 < b) (hQ : 0 < Q) (hQL : Q ∣ N*b) :
    ‖conductorHilbert N b (fun _ => (1 : ℝ)) -
      (conductorSampledSpace N b Q).starProjection
        (conductorHilbert N b (fun _ => (1 : ℝ)))‖^2 = ConductorProjection.energy Q := by
  let t := conductorHilbert N b (fun _ => (1 : ℝ))
  let S := conductorSampledSpace N b Q
  let K := ConductorProjection.space Q
  apply le_antisymm
  · calc
      ‖t-S.starProjection t‖^2 ≤
          ‖t-conductorEvaluation N b (K.starProjection hilbertOne)‖^2 :=
        projection_error_sq_le S t _
          (conductorEvaluation_mem_sampled N b Q (K.starProjection_apply_mem _))
      _ = ConductorProjection.energy Q := by
        rw [conductorEvaluation_error_sq N b Q hN hb hQL (K.starProjection_apply_mem _)]
        rfl
  · obtain ⟨f,hf,he⟩ := conductorSampledSpace_lift N b Q hQ (S.starProjection_apply_mem t)
    calc
      ConductorProjection.energy Q ≤ ‖hilbertOne-f‖^2 :=
        projection_error_sq_le K hilbertOne f hf
      _ = ‖t-conductorEvaluation N b f‖^2 :=
        (conductorEvaluation_error_sq N b Q hN hb hQL hf).symm
      _ = ‖t-S.starProjection t‖^2 := by rw [he]

/-- In particular the old-space energy in a conductor step is exactly E_N. -/
theorem conductor_old_energy_eq (N b : ℕ) (hN : 0 < N) (hb : 0 < b) :
    ‖conductorHilbert N b (fun _ => (1 : ℝ)) -
      (conductorOldSpace N b).starProjection
        (conductorHilbert N b (fun _ => (1 : ℝ)))‖^2 = ConductorProjection.energy N :=
  conductor_sampled_energy_eq N b N hN hb hN (dvd_mul_right N b)

end
end RiemannResearch.RH.Pareto
