import RiemannResearch.RH.IntegratedRamanujanBasis

/-!
# New divisor packets are independent modulo the old period

Source: user-provided argument, `RH_Controlled_Conductor_Schur_2026-09-10.md`,
§3.  The proof below replaces the informal Fourier argument by a finite
divisibility argument.  In particular, arbitrary old-periodic functions are
allowed; this is stronger than independence modulo the old legal packet span.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Every multiple of the conductor is a period of its integrated packet. -/
theorem ramanujanPacket_period_of_dvd (q Q : ℕ) (hq : q ∣ Q) (k : ℕ) :
    ramanujanPacket q (k + Q) = ramanujanPacket q k := by
  unfold ramanujanPacket
  apply Finset.sum_congr rfl
  intro d hd
  have hdQ : d ∣ Q := dvd_trans (Nat.dvd_of_mem_divisors hd) hq
  simp [residue, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdQ]

/-- Adjacent fine residues in one old-period fiber cannot both be multiples
of new divisors. -/
theorem new_divisor_not_dvd_add_period (p Q m d : ℕ)
    (hp : p.Prime) (hQ : 0 < Q)
    (hm : m ∣ p * Q) (hd : d ∣ p * Q)
    (hmQ : ¬ m ∣ Q) (hdQ : ¬ d ∣ Q) : ¬ d ∣ m + Q := by
  obtain ⟨b, hb⟩ := hm
  obtain ⟨a, ha⟩ := hd
  have hbp : ¬ p ∣ b := by
    rintro ⟨c, rfl⟩
    apply hmQ
    refine ⟨c, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p * Q = m * (p * c) := hb
      _ = p * (m * c) := by ring
  have hap : ¬ p ∣ a := by
    rintro ⟨c, rfl⟩
    apply hdQ
    refine ⟨c, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    calc
      p * Q = d * (p * c) := ha
      _ = p * (d * c) := by ring
  have hdpos : 0 < d := by
    exact Nat.pos_of_dvd_of_pos ⟨a, ha⟩ (Nat.mul_pos hp.pos hQ)
  rintro ⟨t, ht⟩
  have he : a * (p + b) = p * (t * b) := by
    apply Nat.eq_of_mul_eq_mul_left hdpos
    calc
      d * (a * (p + b)) = p * (d * a) + (d * a) * b := by ring
      _ = p * (p * Q) + (p * Q) * b := by rw [← ha]
      _ = p * (m * b) + (p * Q) * b := by rw [hb]
      _ = p * ((m + Q) * b) := by ring
      _ = d * (p * (t * b)) := by rw [ht]; ring
  have hdiv : p ∣ a * (p + b) := by
    rw [he]
    exact dvd_mul_right p (t * b)
  have hpb : p ∣ p + b := (hp.dvd_mul.mp hdiv).resolve_left hap
  exact hbp ((Nat.dvd_add_iff_right (dvd_refl p)).mpr hpb)

/-- A finite residue combination supported on divisors of `pQ` can be
`Q`-periodic only if every new residue coefficient vanishes. -/
theorem residue_new_coefficients_zero_of_periodic (p Q : ℕ)
    (hp : p.Prime) (hQ : 0 < Q) (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, d ∣ p * Q)
    (hper : ∀ k : ℕ, (∑ d ∈ s, c d * residue d (k + Q)) =
      ∑ d ∈ s, c d * residue d k) :
    ∀ m ∈ s, ¬ m ∣ Q → c m = 0 := by
  classical
  have hincr (k : ℕ) (hk : 0 < k) :
      (∑ d ∈ s, c d * residue d k) -
        (∑ d ∈ s, c d * residue d (k - 1)) =
      ∑ d ∈ s, c d * (1 - if d ∣ k then (d : ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← mul_sub, residue_difference d k hk]
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hms hmQ
    have hmpos : 0 < m := Nat.pos_of_dvd_of_pos (hs m hms) (Nat.mul_pos hp.pos hQ)
    have hdiff :
        (∑ d ∈ s, c d * residue d (m + Q)) -
          (∑ d ∈ s, c d * residue d (m + Q - 1)) =
        (∑ d ∈ s, c d * residue d m) -
          (∑ d ∈ s, c d * residue d (m - 1)) := by
      rw [hper m, show m + Q - 1 = (m - 1) + Q by omega, hper (m - 1)]
    rw [hincr (m + Q) (by omega), hincr m hmpos] at hdiff
    simp_rw [mul_sub, mul_one] at hdiff
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hdiff
    have hz :
        (∑ d ∈ s, c d * ((if d ∣ m then (d : ℝ) else 0) -
          (if d ∣ m + Q then (d : ℝ) else 0))) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      linarith
    have he :
        (∑ d ∈ s, c d * ((if d ∣ m then (d : ℝ) else 0) -
          (if d ∣ m + Q then (d : ℝ) else 0))) = c m * (m : ℝ) := by
      rw [Finset.sum_eq_single m]
      · have hnot : ¬ m ∣ m + Q :=
          new_divisor_not_dvd_add_period p Q m m hp hQ (hs m hms) (hs m hms) hmQ hmQ
        simp [hnot]
      · intro d hds hdm
        by_cases hdQ : d ∣ Q
        · have hiff : d ∣ m + Q ↔ d ∣ m := (Nat.dvd_add_iff_left hdQ).symm
          simp only [hiff, sub_self, mul_zero]
        · have hnot : ¬ d ∣ m + Q :=
            new_divisor_not_dvd_add_period p Q m d hp hQ (hs m hms) (hs d hds) hmQ hdQ
          by_cases hd : d ∣ m
          · have hdlt : d < m := lt_of_le_of_ne (Nat.le_of_dvd hmpos hd) hdm
            rw [ih d hdlt hds hdQ]
            simp
          · simp [hd, hnot]
      · exact fun h => False.elim (h hms)
    rw [he] at hz
    exact (mul_eq_zero.mp hz).resolve_right (by exact_mod_cast (ne_of_gt hmpos))

/-- Independence of the actual new Ramanujan divisor packets modulo all
`Q`-periodic functions, including repeated-prime conductor enlargements. -/
theorem ramanujanPacket_new_independent_mod_periodic (p Q : ℕ)
    (hp : p.Prime) (hQ : 0 < Q) (s : Finset ℕ) (b : ℕ → ℝ)
    (hs : ∀ q ∈ s, q ∣ p * Q ∧ ¬ q ∣ Q)
    (hper : ∀ k : ℕ, (∑ q ∈ s, b q * ramanujanPacket q (k + Q)) =
      ∑ q ∈ s, b q * ramanujanPacket q k) :
    ∀ q ∈ s, b q = 0 := by
  classical
  let a : ℕ → ℝ := fun d =>
    ∑ q ∈ s, if d ∣ q then b q * (ArithmeticFunction.moebius (q / d) : ℝ) else 0
  have hL : 0 < p * Q := Nat.mul_pos hp.pos hQ
  have hqpos (q : ℕ) (hq : q ∈ s) : 0 < q :=
    Nat.pos_of_dvd_of_pos (hs q hq).1 hL
  have hexpand (k : ℕ) :
      (∑ q ∈ s, b q * ramanujanPacket q k) =
        ∑ d ∈ (p * Q).divisors, a d * residue d k := by
    calc
      _ = ∑ q ∈ s, ∑ d ∈ (p * Q).divisors,
          if d ∣ q then (b q * (ArithmeticFunction.moebius (q / d) : ℝ)) *
            residue d k else 0 := by
        apply Finset.sum_congr rfl
        intro q hqs
        have hfilter : ((p * Q).divisors.filter (fun d => d ∣ q)) = q.divisors := by
          ext d
          simp only [Finset.mem_filter, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨_, _⟩, hdq⟩
            exact ⟨hdq, ne_of_gt (hqpos q hqs)⟩
          · rintro ⟨hdq, _⟩
            exact ⟨⟨dvd_trans hdq (hs q hqs).1, ne_of_gt hL⟩, hdq⟩
        rw [ramanujanPacket, ← hfilter, Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdq : d ∣ q <;> simp [hdq, mul_assoc]
      _ = ∑ d ∈ (p * Q).divisors, ∑ q ∈ s,
          if d ∣ q then (b q * (ArithmeticFunction.moebius (q / d) : ℝ)) *
            residue d k else 0 := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [a, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q hq
        by_cases hdq : d ∣ q <;> simp [hdq]
  have ha : ∀ m ∈ (p * Q).divisors, ¬ m ∣ Q → a m = 0 := by
    apply residue_new_coefficients_zero_of_periodic p Q hp hQ (p * Q).divisors a
    · intro d hd
      exact Nat.dvd_of_mem_divisors hd
    · intro k
      rw [← hexpand (k + Q), ← hexpand k]
      exact hper k
  by_contra h
  push Not at h
  obtain ⟨q, hqs, hbq⟩ := h
  let t := s.filter (fun q => b q ≠ 0)
  have ht : t.Nonempty := ⟨q, Finset.mem_filter.mpr ⟨hqs, hbq⟩⟩
  let m := t.max' ht
  have hmt : m ∈ t := Finset.max'_mem t ht
  have hms : m ∈ s := (Finset.mem_filter.mp hmt).1
  have hbm : b m ≠ 0 := (Finset.mem_filter.mp hmt).2
  have hmpos := hqpos m hms
  have ham : a m = 0 := ha m (Nat.mem_divisors.mpr ⟨(hs m hms).1, ne_of_gt hL⟩)
    (hs m hms).2
  have he : a m = b m := by
    dsimp [a]
    rw [Finset.sum_eq_single m]
    · simp [Nat.div_self hmpos]
    · intro q hqs hqm
      by_cases hbq : b q = 0
      · simp [hbq]
      · have hqt : q ∈ t := Finset.mem_filter.mpr ⟨hqs, hbq⟩
        have hqmle : q ≤ m := Finset.le_max' t q hqt
        have hnot : ¬ m ∣ q := by
          intro hd
          have hmqle := Nat.le_of_dvd (hqpos q hqs) hd
          exact hqm (by omega)
        simp [hnot]
    · exact fun h => False.elim (h hms)
  exact hbm (he.symm.trans ham)

end
end RiemannResearch.RH.Pareto
