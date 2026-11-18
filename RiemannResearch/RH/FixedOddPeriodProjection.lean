import RiemannResearch.RH.OddPeriodEvenPackets
import RiemannResearch.RH.MixedCaptureLegalTrials

/-!
# A fixed odd period leaves a strictly positive mixed-projection deficit

The signed dyadic test from `OddPeriodBlock` annihilates all even mixed
packets and every sequence with a prescribed odd period on positive sites.
Closedness of the corresponding norm inequality extends it to the whole span.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.OddPeriodBlock

private theorem partial_add (Q K : ℕ) (f g : ℕ → ℝ) :
    partialSum Q K (f + g) = partialSum Q K f + partialSum Q K g := by
  simp only [partialSum, block, Pi.add_apply, add_sub_add_comm, Finset.sum_add_distrib,
    mul_add]

private theorem partial_smul (Q K : ℕ) (a : ℝ) (f : ℕ → ℝ) :
    partialSum Q K (a • f) = a * partialSum Q K f := by
  simp only [partialSum, block, Pi.smul_apply, smul_eq_mul, ← mul_sub, ← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem partial_congr_positive {Q : ℕ} (hQ : 0 < Q) (K : ℕ)
    {f g : ℕ → ℝ} (hfg : ∀ n, 0 < n → f n = g n) :
    partialSum Q K f = partialSum Q K g := by
  unfold partialSum
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  unfold block
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro u _
  rw [hfg _ (by positivity), hfg _ (by positivity)]

/-- Periodicity on the positive physical sites suffices for the signed block
test. It includes the constant Hilbert target with its zero anchor. -/
theorem partial_zero_of_positive_odd_period {Q : ℕ} (hQ : Odd Q) (K : ℕ)
    {f : ℕ → ℝ} (hf : ∀ n, 0 < n → f (n + Q) = f n) : partialSum Q K f = 0 := by
  have hp : 0 < Q := Odd.pos hQ
  let g : ℕ → ℝ := fun n => f (n + Q)
  have hg (n : ℕ) : g (n + Q) = g n := hf (n + Q) (by omega)
  rw [partial_congr_positive hp K (g := g) (fun n hn => (hf n hn).symm)]
  exact partial_eq_zero_of_odd_period hQ K hg

private def payoffKernel (Q : ℕ) : Submodule ℝ ThresholdHilbert where
  carrier := {x | Tendsto (fun K => partialSum Q K (hilbertSequence x)) atTop (𝓝 0)}
  zero_mem' := by
    have hz : hilbertSequence (0 : ThresholdHilbert) = 0 := hilbertSequenceLinear.map_zero
    simp [hz, partialSum, block]
  add_mem' := by
    intro x y hx hy
    have he : hilbertSequence (x + y) = hilbertSequence x + hilbertSequence y :=
      hilbertSequenceLinear.map_add _ _
    change Tendsto (fun K => partialSum Q K (hilbertSequence x)) atTop (𝓝 0) at hx
    change Tendsto (fun K => partialSum Q K (hilbertSequence y)) atTop (𝓝 0) at hy
    change Tendsto (fun K => partialSum Q K (hilbertSequence (x + y))) atTop (𝓝 0)
    simpa only [he, partial_add, add_zero] using hx.add hy
  smul_mem' := by
    intro a x hx
    have he : hilbertSequence (a • x) = a • hilbertSequence x :=
      hilbertSequenceLinear.map_smul a x
    change Tendsto (fun K => partialSum Q K (hilbertSequence x)) atTop (𝓝 0) at hx
    change Tendsto (fun K => partialSum Q K (hilbertSequence (a • x))) atTop (𝓝 0)
    simpa only [he, partial_smul, mul_zero] using hx.const_mul a

/-- Arbitrarily many even mixed packets together with any sequences of a
fixed odd period on positive coordinates. -/
def evenMixedAndPeriodicSpan (Q : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {x : ThresholdHilbert |
    (∃ q : ℕ, 1 < q ∧ 2 ∣ q ∧ ¬IsPrimePow q ∧ x = ramanujanPacketHilbert q) ∨
      (∀ n : ℕ, 0 < n → hilbertSequence x (n + Q) = hilbertSequence x n)}

private theorem evenMixedAndPeriodicSpan_le_payoffKernel {Q : ℕ} (hQ : Odd Q)
    (heven : ∀ q : ℕ, 1 < q → 2 ∣ q → ¬ IsPrimePow q →
      Tendsto (fun K => partialSum Q K (hilbertSequence (ramanujanPacketHilbert q)))
        atTop (𝓝 0)) :
    evenMixedAndPeriodicSpan Q ≤ payoffKernel Q := by
  apply Submodule.span_le.mpr
  intro x hx
  rcases hx with ⟨q, hq, h2, hm, rfl⟩ | hx
  · exact heven q hq h2 hm
  · change Tendsto (fun K => partialSum Q K (hilbertSequence x)) atTop (𝓝 0)
    simpa only [fun K => partial_zero_of_positive_odd_period hQ K hx] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

private theorem odd_period_closure_assembly {Q : ℕ} (hQ : Odd Q)
    (hbound : ∀ x : ThresholdHilbert,
      Tendsto (fun K => partialSum Q K (hilbertSequence x)) atTop (𝓝 ((Q : ℝ) / 4)) →
      21 * (Q : ℝ) / (16 * (49 * (Q : ℝ) ^ 2 - 1)) ≤ ‖x‖ ^ 2)
    (heven : ∀ q : ℕ, 1 < q → 2 ∣ q → ¬IsPrimePow q →
      Tendsto (fun K => partialSum Q K (hilbertSequence (ramanujanPacketHilbert q)))
        atTop (𝓝 0))
    (htwo : Tendsto (fun K => partialSum Q K (hilbertSequence (ramanujanPacketHilbert 2)))
      atTop (𝓝 ((Q : ℝ) / 4))) {c : ThresholdHilbert}
    (hc : c ∈ (evenMixedAndPeriodicSpan Q).topologicalClosure) :
    21 * (Q : ℝ) / (16 * (49 * (Q : ℝ) ^ 2 - 1)) ≤
      ‖(ramanujanPacketHilbert 2 - Real.log 2 • hilbertOne) - c‖ ^ 2 := by
  let z := ramanujanPacketHilbert 2 - Real.log 2 • hilbertOne
  let b := 21 * (Q : ℝ) / (16 * (49 * (Q : ℝ) ^ 2 - 1))
  have hone : hilbertOne ∈ payoffKernel Q := by
    apply evenMixedAndPeriodicSpan_le_payoffKernel hQ heven
    apply Submodule.subset_span
    right
    intro n hn
    rw [hilbertOne_sequence]
    simp [zeroAnchor, hn.ne']
  have hy (y : ThresholdHilbert) (hy : y ∈ evenMixedAndPeriodicSpan Q) :
      b ≤ ‖z - y‖ ^ 2 := by
    have hy0 := evenMixedAndPeriodicSpan_le_payoffKernel hQ heven hy
    let w := -(Real.log 2 • hilbertOne) - y
    have hw : w ∈ payoffKernel Q :=
      (payoffKernel Q).sub_mem ((payoffKernel Q).neg_mem ((payoffKernel Q).smul_mem _ hone)) hy0
    change Tendsto (fun K => partialSum Q K (hilbertSequence w)) atTop (𝓝 0) at hw
    have hw' : z - y = ramanujanPacketHilbert 2 + w := by dsimp [z, w]; abel
    apply hbound
    rw [hw']
    have hseq : hilbertSequence (ramanujanPacketHilbert 2 + w) =
        hilbertSequence (ramanujanPacketHilbert 2) + hilbertSequence w :=
      hilbertSequenceLinear.map_add _ _
    simpa only [hseq, partial_add, add_zero] using htwo.add hw
  have hcset : IsClosed {y : ThresholdHilbert | b ≤ ‖z - y‖ ^ 2} :=
    isClosed_le continuous_const ((continuous_const.sub continuous_id).norm.pow 2)
  have hi : (evenMixedAndPeriodicSpan Q : Set ThresholdHilbert) ⊆
      {y : ThresholdHilbert | b ≤ ‖z - y‖ ^ 2} := fun y hy' => hy y hy'
  exact closure_minimal hi hcset hc

theorem mixedSpace_le_evenMixedAndPeriodicSpan (Q : ℕ) (F : Finset ℕ)
    (hF : ∀ q ∈ PrimePowerSchur.mixedConductors F, 1 < q ∧ (Odd q → q ∣ Q)) :
    PrimePowerSchur.mixedSpace F ≤ evenMixedAndPeriodicSpan Q := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  have hq : q.val ∈ F ∧ ¬IsPrimePow q.val := Finset.mem_filter.mp q.property
  have hg := hF q.val q.property
  apply Submodule.subset_span
  rcases Nat.even_or_odd q.val with he | ho
  · exact Or.inl ⟨q.val, hg.1, even_iff_two_dvd.mp he, hq.2, rfl⟩
  · right
    intro n _
    rw [hilbertSequence_ramanujanPacketHilbert]
    exact ramanujanPacket_period_of_dvd q.val Q (hg.2 ho) n

private theorem odd_period_capture_from_floor (Q : ℕ) (F : Finset ℕ)
    (hF : ∀ q ∈ PrimePowerSchur.mixedConductors F, 1 < q ∧ (Odd q → q ∣ Q))
    (hh : ∀ c ∈ (evenMixedAndPeriodicSpan Q).topologicalClosure,
      21 * (Q : ℝ) / (16 * (49 * (Q : ℝ) ^ 2 - 1)) ≤
        ‖(ramanujanPacketHilbert 2 - Real.log 2 • hilbertOne) - c‖ ^ 2) :
    21 * (Q : ℝ) / (16 * (49 * (Q : ℝ) ^ 2 - 1)) ≤ Real.log 2 - (Real.log 2) ^ 2 -
      ‖(PrimePowerSchur.mixedSpace F).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 := by
  let K := PrimePowerSchur.mixedSpace F
  let z := ramanujanPacketHilbert 2
  let y := K.starProjection z
  have hy : y ∈ K := K.starProjection_apply_mem z
  have hzy : inner ℝ z y = ‖y‖ ^ 2 := by
    have ho := K.starProjection_inner_eq_zero z y hy
    change inner ℝ (z - y) y = 0 at ho
    rw [inner_sub_left, real_inner_self_eq_norm_sq, sub_eq_zero] at ho
    exact ho
  have hyn : inner ℝ y hilbertOne = 0 :=
    (K.mem_orthogonal _).mp (PrimePowerSchur.one_mem_mixed_orthogonal _) y hy
  have hzn : inner ℝ z hilbertOne = Real.log 2 := by
    dsimp only [z]
    rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
      paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hzsq : ‖z‖ ^ 2 = Real.log 2 := PrimePowerSchur.ramanujanPacketHilbert_two_norm_sq
  have h := hh y (Submodule.le_topologicalClosure _
    (mixedSpace_le_evenMixedAndPeriodicSpan Q F hF hy))
  have hs : (z - Real.log 2 • hilbertOne) - y = (z - y) - Real.log 2 • hilbertOne := by abel
  change _ ≤ ‖(z - Real.log 2 • hilbertOne) - y‖ ^ 2 at h
  rw [hs, norm_sub_sq_real, norm_sub_sq_real, hzy, hzsq, real_inner_smul_right, inner_sub_left,
    hzn, hyn, sub_zero, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hilbertOne_norm_sq] at h
  change _ ≤ _ - ‖y‖ ^ 2
  linarith only [h]

/-- Any fixed odd period leaves a positive distance, even after adjoining
all even mixed conductors and taking the complete Hilbert closure. -/
theorem centered_parity_error_floor_of_fixed_odd_period (Q : ℕ) (hQ : Odd Q)
    {c : ThresholdHilbert} (hc : c ∈ (evenMixedAndPeriodicSpan Q).topologicalClosure) :
    21 * (Q : ℝ) / (16 * (49 * (Q : ℝ) ^ 2 - 1)) ≤
      ‖(ramanujanPacketHilbert 2 - Real.log 2 • hilbertOne) - c‖ ^ 2 := by
  apply odd_period_closure_assembly hQ (odd_period_floor_of_partial_tendsto Q hQ.pos) _ _ hc
  · intro q hq he hm
    rw [hilbertSequence_ramanujanPacketHilbert]
    exact partialSum_even_mixed_tendsto_zero Q q hq he hm
  · rw [hilbertSequence_ramanujanPacketHilbert]
    have hev : (fun K => partialSum Q K (ramanujanPacket 2)) =ᶠ[atTop]
        (fun _ : ℕ => (Q : ℝ) / 4) := by
      filter_upwards [eventually_ge_atTop 1] with K hK
      obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
      exact partialSum_succ_parity Q N
    exact (tendsto_congr' hev).mpr tendsto_const_nhds

/-- A mixed cutoff whose odd conductors divide one prescribed odd period
leaves this much of the full RH saturation target uncaptured. -/
theorem fixed_odd_period_projection_deficit (Q : ℕ) (hQ : Odd Q) (F : Finset ℕ)
    (hF : ∀ q ∈ PrimePowerSchur.mixedConductors F, 1 < q ∧ (Odd q → q ∣ Q)) :
    21 * (Q : ℝ) / (16 * (49 * (Q : ℝ) ^ 2 - 1)) ≤ Real.log 2 - (Real.log 2) ^ 2 -
      ‖(PrimePowerSchur.mixedSpace F).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 :=
  odd_period_capture_from_floor Q F hF
    (fun _ hc => centered_parity_error_floor_of_fixed_odd_period Q hQ hc)

/-- Saturating mixed fits must eventually use an odd conductor outside every
prescribed odd divisor dictionary. -/
theorem eventually_odd_conductor_not_dvd_of_capture_saturation
    (F : ℕ → Finset ℕ) (hF : ∀ N q, q ∈ PrimePowerSchur.mixedConductors (F N) → 1 < q)
    (hsat : Tendsto (fun N => ‖(PrimePowerSchur.mixedSpace (F N)).starProjection
      (ramanujanPacketHilbert 2)‖ ^ 2) atTop (𝓝 (Real.log 2 - (Real.log 2) ^ 2)))
    (Q : ℕ) (hQ : Odd Q) :
    ∀ᶠ N in atTop, ∃ q ∈ PrimePowerSchur.mixedConductors (F N), Odd q ∧ ¬ q ∣ Q := by
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ.pos
  let b := 21 * (Q : ℝ) / (16 * (49 * (Q : ℝ) ^ 2 - 1))
  have hb : 0 < b := by
    have hnum : (0 : ℝ) < Q := by linarith
    have hden : 0 < 49 * (Q : ℝ) ^ 2 - 1 := by nlinarith [sq_nonneg ((Q : ℝ) - 1)]
    dsimp only [b]
    positivity
  have he := hsat.eventually (lt_mem_nhds (show Real.log 2 - (Real.log 2) ^ 2 - b <
      Real.log 2 - (Real.log 2) ^ 2 by linarith))
  filter_upwards [he] with N hN
  by_contra! ha
  have hg := fixed_odd_period_projection_deficit Q hQ (F N)
    (fun q hq => ⟨hF N q hq, ha q hq⟩)
  change b ≤ _ at hg
  linarith only [hN, hg]

/-- Arbitrarily large odd mixed conductors must actually occur along every
saturating sequence, eventually beyond each prescribed finite cutoff. -/
theorem eventually_large_odd_mixed_conductor_of_saturation
    (F : ℕ → Finset ℕ)
    (hF : ∀ N q, q ∈ PrimePowerSchur.mixedConductors (F N) → 1 < q)
    (hsat : Tendsto (fun N => ‖(PrimePowerSchur.mixedSpace (F N)).starProjection
      (ramanujanPacketHilbert 2)‖ ^ 2) atTop (𝓝 (Real.log 2 - (Real.log 2) ^ 2)))
    (B : ℕ) :
    ∀ᶠ N in atTop, ∃ q ∈ PrimePowerSchur.mixedConductors (F N), Odd q ∧ B < q := by
  have hperiod (k : ℕ) : ∃ Q : ℕ, Odd Q ∧ ∀ q ≤ k, Odd q → q ∣ Q := by
    induction k with
    | zero =>
      refine ⟨1, by decide, ?_⟩
      intro q hq ho
      have := ho.pos
      omega
    | succ k ih =>
      obtain ⟨Q, hQ, hd⟩ := ih
      by_cases hp : Odd (k + 1)
      · refine ⟨Q * (k + 1), hQ.mul hp, ?_⟩
        intro q hq ho
        by_cases he : q ≤ k
        · exact dvd_mul_of_dvd_left (hd q he ho) _
        · rw [show q = k + 1 by omega]
          exact dvd_mul_left _ _
      · refine ⟨Q, hQ, ?_⟩
        intro q hq ho
        exact hd q (by by_contra! hn; exact hp (by rwa [← show q = k + 1 by omega])) ho
  obtain ⟨Q, hQ, hd⟩ := hperiod B
  filter_upwards [eventually_odd_conductor_not_dvd_of_capture_saturation F hF hsat Q hQ]
    with N hN
  obtain ⟨q, hq, ho, hx⟩ := hN
  exact ⟨q, hq, ho, lt_of_not_ge (fun hb => hx (hd q hb ho))⟩

/-- The dyadic block test leaves at least 7/256 uncaptured in every even-only window. -/
theorem even_mixed_projection_deficit (F : Finset ℕ)
    (hF : ∀ q ∈ F, 1 < q ∧ 2 ∣ q) :
    (7 / 256 : ℝ) ≤ Real.log 2 - (Real.log 2) ^ 2 -
      ‖(PrimePowerSchur.mixedSpace F).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 := by
  have h := fixed_odd_period_projection_deficit 1 (by decide) F (fun q hq => by
    have hd := hF q (Finset.mem_filter.mp hq).1
    refine ⟨hd.1, ?_⟩
    rintro ⟨k, hk⟩
    obtain ⟨d, he⟩ := hd.2
    omega)
  norm_num at h ⊢
  exact h

/-- Adding odd mixed directions secures a strictly positive overshoot of every
even-only window, already from the completely evaluated period-5040 trial. -/
theorem full_capture_gain_over_even_period5040 (F : Finset ℕ)
    (hF : ∀ q ∈ F, 1 < q ∧ 2 ∣ q) :
    (7 / 256 : ℝ) - (39 / 961 : ℝ) * (Real.log 2) ^ 2 <
      ‖PrimePowerSchur.mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 -
      ‖(PrimePowerSchur.mixedSpace F).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 := by
  linarith only [even_mixed_projection_deficit F hF,
    PrimePowerSchur.full_mixed_capture_lower_period5040]

end RiemannResearch.RH.Pareto.OddPeriodBlock
