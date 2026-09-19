import RiemannResearch.RH.MultiRangePrimorialCoordinates

/-! Exact finite-support rebase to the original primorial sieve. All overlapping
coefficients are added with their signs before any energy is formed. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

private theorem sum_extended_to_union (s t : Finset ℕ) (a f : ℕ → ℝ) :
    (∑ d ∈ s ∪ t, (if d ∈ s then a d else 0) * f d) = ∑ d ∈ s, a d * f d := by
  classical
  have h : (∑ d ∈ s, (if d ∈ s then a d else 0) * f d) =
      ∑ d ∈ s ∪ t, (if d ∈ s then a d else 0) * f d := by
    apply Finset.sum_subset (Finset.subset_union_left : s ⊆ s ∪ t)
    intro d _ hd
    simp [hd]
  rw [← h]
  exact Finset.sum_congr rfl (fun d hd => by simp [hd])

private theorem sum_extended_to_union_right (s t : Finset ℕ) (a f : ℕ → ℝ) :
    (∑ d ∈ s ∪ t, (if d ∈ t then a d else 0) * f d) = ∑ d ∈ t, a d * f d := by
  rw [Finset.union_comm]
  exact sum_extended_to_union t s a f

/-- The primorial sieve with its distinguished coefficient at modulus one separated. -/
theorem correctionSieve_floor_coordinates (Y : ℕ) :
    correctionSieve Y = finiteFloorSynthesis ((correctionPrimorial Y).divisors.erase 1)
      (fun d => (ArithmeticFunction.moebius d : ℝ)) 1 := by
  funext n
  have h1 : 1 ∈ (correctionPrimorial Y).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, ne_of_gt (correctionPrimorial_pos Y)⟩
  have h := Finset.sum_erase_add (s := (correctionPrimorial Y).divisors)
    (f := fun d => (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ)) h1
  simpa [correctionSieve, finiteFloorSynthesis, add_comm] using h.symm

theorem correctionAlpha_erase_one (Y : ℕ) :
    correctionAlpha Y = 1 + ∑ d ∈ (correctionPrimorial Y).divisors.erase 1,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
  have h1 : 1 ∈ (correctionPrimorial Y).divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, ne_of_gt (correctionPrimorial_pos Y)⟩
  have h := Finset.sum_erase_add (s := (correctionPrimorial Y).divisors)
    (f := fun d => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) h1
  rw [correctionAlpha_eq_divisor_sum]
  simpa [add_comm] using h.symm

/-- The source's original finite correction characterization, with the exact
reciprocal balance `-α`. No disjointness of the sieve and correction supports
is imposed: overlapping coefficients are added algebraically. -/
theorem conditionalHeadClass_iff_primorial_corrections
    (Y : ℕ) (hY : 0 < Y) (F : ℕ → ℝ) :
    F ∈ conditionalHeadClass Y ↔
      ∃ (t : Finset ℕ) (x : ℕ → ℝ),
        (∀ d ∈ t, Y < d) ∧
        (∑ d ∈ t, x d / (d : ℝ)) = -correctionAlpha Y ∧
        F = fun n => correctionSieve Y n + ∑ d ∈ t, x d * ((n / d : ℕ) : ℝ) := by
  classical
  let b := (correctionPrimorial Y).divisors.erase 1
  let μ : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ)
  have hb : ∀ d ∈ b, 2 ≤ d := by
    intro d hd
    have hp := Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase hd)
    have hn := Finset.ne_of_mem_erase hd
    omega
  have hblow : ∀ n, 1 < n → n ≤ Y → (if n ∈ b then μ n else 0) = μ n := by
    intro n hn hnY
    have h := correctionPrimorial_low_moebius Y n (by omega) hnY
    have hn1 : n ≠ 1 := by omega
    simpa [b, hn1, μ] using h
  have hbalpha : 1 + (∑ d ∈ b, μ d / (d : ℝ)) = correctionAlpha Y :=
    (correctionAlpha_erase_one Y).symm
  have hbsieve (n : ℕ) : correctionSieve Y n =
      (n : ℝ) + ∑ d ∈ b, μ d * ((n / d : ℕ) : ℝ) := by
    rw [correctionSieve_floor_coordinates]
    simp only [finiteFloorSynthesis, one_mul, b, μ]
  constructor
  · intro hF
    obtain ⟨s, a, hs, ha, hlo, he⟩ :=
      (conditionalHeadClass_iff_balanced_floor_coordinates Y hY F).mp hF
    let u := s ∪ b
    let t := u.filter (fun d => Y < d)
    let x : ℕ → ℝ := fun d => (if d ∈ s then a d else 0) - (if d ∈ b then μ d else 0)
    have hxlow : ∀ d ∈ u, d ∉ t → x d = 0 := by
      intro d hd hdt
      have hdY : d ≤ Y := by
        by_contra h
        exact hdt (Finset.mem_filter.mpr ⟨hd, by omega⟩)
      have hd2 : 2 ≤ d := by
        rcases Finset.mem_union.mp hd with hds | hdb
        · exact hs d hds
        · exact hb d hdb
      dsimp [x]
      rw [hlo d (by omega) hdY, hblow d (by omega) hdY]
      exact sub_self _
    have hxsum (f : ℕ → ℝ) :
        (∑ d ∈ t, x d * f d) = (∑ d ∈ s, a d * f d) - ∑ d ∈ b, μ d * f d := by
      calc
        _ = ∑ d ∈ u, x d * f d := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro d hd hdt
          rw [hxlow d hd hdt, zero_mul]
        _ = _ := by
          simp only [u, x, sub_mul, Finset.sum_sub_distrib]
          rw [sum_extended_to_union, sum_extended_to_union_right]
    refine ⟨t, x, fun d hd => (Finset.mem_filter.mp hd).2, ?_, ?_⟩
    · have hh := hxsum (fun d => (d : ℝ)⁻¹)
      simp only [← div_eq_mul_inv] at hh
      linarith
    · funext n
      have hn := congrFun he n
      simp only [finiteFloorSynthesis, one_mul] at hn
      rw [hbsieve, hxsum]
      linarith
  · rintro ⟨t, x, ht, hx, rfl⟩
    let s := b ∪ t
    let a : ℕ → ℝ := fun d => (if d ∈ b then μ d else 0) + (if d ∈ t then x d else 0)
    have hs : ∀ d ∈ s, 2 ≤ d := by
      intro d hd
      rcases Finset.mem_union.mp hd with hdb | hdt
      · exact hb d hdb
      · have := ht d hdt; omega
    have hasum (f : ℕ → ℝ) :
        (∑ d ∈ s, a d * f d) = (∑ d ∈ b, μ d * f d) + ∑ d ∈ t, x d * f d := by
      simp only [s, a, add_mul, Finset.sum_add_distrib]
      rw [sum_extended_to_union, sum_extended_to_union_right]
    have ha : 1 + ∑ d ∈ s, a d / (d : ℝ) = 0 := by
      have hh := hasum (fun d => (d : ℝ)⁻¹)
      simp only [← div_eq_mul_inv] at hh
      linarith
    have he : finiteFloorSynthesis s a 1 =
        fun n => correctionSieve Y n + ∑ d ∈ t, x d * ((n / d : ℕ) : ℝ) := by
      funext n
      rw [finiteFloorSynthesis, one_mul, hasum, hbsieve]
      ring
    rw [← he]
    refine ⟨finiteFloorSynthesis_legal_of_balance s a 1 hs ha, ?_⟩
    intro n hn hnY
    rw [he]
    change correctionSieve Y n + (∑ d ∈ t, x d * ((n / d : ℕ) : ℝ)) = 1
    rw [correctionSieve_exact Y n hn hnY]
    have hz : (∑ d ∈ t, x d * ((n / d : ℕ) : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [Nat.div_eq_of_lt (lt_of_le_of_lt hnY (ht d hd))]
      simp
    rw [hz, add_zero]

end RiemannResearch.RH.Pareto
