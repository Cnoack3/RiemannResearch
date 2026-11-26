import RiemannResearch.Analysis.MontgomeryFiniteIndexGap
import RiemannResearch.Analysis.MicroscopicPrimeVacancy
import RiemannResearch.Analysis.LamzouriGap285OriginalReplay
import RiemannResearch.Analysis.MontgomeryAdjacentWindowFloor

/-! First strictly positive consecutive gaps and the deleted fraction. The finite
identity separates precisely the equal-height adjacent pairs from Lamzouri's
small-gap count, which permits zero gaps. -/
noncomputable section
open Filter Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate OrdinateCollisionCertificate
open ZeroDPPCollisionLoss MicroscopicPrimeVacancy

private theorem support_add_ties (x : ℕ → ℝ) (hx : Monotone x) (n : ℕ) :
    (((Finset.range n).image x).card : ℝ) +
      (∑ i ∈ Finset.range (n-1), if x (i+1) = x i then (1 : ℝ) else 0) = n := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ k =>
      have hmem : x (k+1) ∈ (Finset.range (k+1)).image x ↔ x (k+1) = x k := by
        constructor
        · intro h
          obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
          have hil : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          exact le_antisymm (he ▸ (show x i ≤ x k from hx hil)) (hx (Nat.le_succ k))
        · intro h
          exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), h.symm⟩
      rw [Finset.range_add_one (n := k + 1), Finset.image_insert]
      simp only [Nat.succ_sub_one] at ih ⊢
      rw [Finset.sum_range_succ]
      by_cases h : x (k+1) = x k
      · rw [if_pos h, Finset.insert_eq_of_mem (hmem.mpr h)]
        push_cast
        push_cast at ih
        linarith
      · rw [if_neg h, Finset.card_insert_of_notMem (fun m => h (hmem.mp m))]
        push_cast
        push_cast at ih
        linarith

private theorem cutoff_support (T : ℝ) :
    (Finset.range (Ncount 0 T)).image (cutoffOrdinate T) = actualOrdinateSupport T := by
  classical
  ext y
  change (y ∈ (Finset.range (Ncount 0 T)).image (cutoffOrdinate T)) ↔
    y ∈ (Finset.univ : Finset (Copies T)).image (copyOrdinate T)
  constructor
  · intro hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨c,hc⟩ := mem_chronologicalList.mp (cutoffOrdinate_mem (Finset.mem_range.mp hi))
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, hc⟩
  · intro hy
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (mem_chronologicalList.mpr ⟨c,rfl⟩)
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_range.mpr (by simpa using hi), (cutoffOrdinate_eq_get hi).trans he⟩

private theorem drop_last_guard (n : ℕ) (w : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, if i+1 < n then w i else 0) = ∑ i ∈ Finset.range (n-1), w i := by
  cases n with
  | zero => simp
  | succ k =>
    rw [Finset.sum_range_succ, if_neg (show ¬ k+1 < k+1 by omega), add_zero]
    simp only [Nat.succ_sub_one]
    exact Finset.sum_congr rfl (fun i hi => if_pos (by have := Finset.mem_range.mp hi; omega))

/-- Each fiber of size m contributes exactly m−1 tied consecutive gaps.
Removing this measured atom leaves precisely the strictly positive first-rank mass. -/
theorem firstGap_add_primeDeleted_eq {T q : ℝ} (hT : 1 < T) (hq : 0 ≤ q) :
    positiveIndexGapMass T q 1 + primeDeletedFraction T =
      ((smallGapIndices q T).card : ℝ) / normalizer T := by
  let n := Ncount 0 T
  let x := cutoffOrdinate T
  let L := unfoldingScale T
  let w := fun i : ℕ =>
    if 0 < L * (x (i+1)-x i) ∧ L * (x (i+1)-x i) ≤ q then (1 : ℝ) else 0
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hgap (i : ℕ) : (L * (x (i+1)-x i) ≤ q) ↔
      cutoffGap T i * Real.log T ≤ 2 * Real.pi * q := by
    change Real.log T / (2 * Real.pi) * cutoffGap T i ≤ q ↔ _
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2 * Real.pi)]
    ring_nf
  have hsplit (i : ℕ) :
      w i + (if x (i+1) = x i then (1 : ℝ) else 0) =
        if cutoffGap T i * Real.log T ≤ 2 * Real.pi * q then 1 else 0 := by
    dsimp only [w]
    simp only [← hgap i]
    by_cases he : x (i+1) = x i
    · simp [he,hq]
    · have hp : 0 < L * (x (i+1)-x i) :=
        mul_pos hL (sub_pos.mpr (lt_of_le_of_ne
          (cutoffOrdinate_monotone T (Nat.le_succ i)) (Ne.symm he)))
      simp [he,hp]
  have hties := support_add_ties x (cutoffOrdinate_monotone T) n
  change (((Finset.range (Ncount 0 T)).image (cutoffOrdinate T)).card : ℝ) +
    (∑ i ∈ Finset.range (n-1), if x (i+1) = x i then (1 : ℝ) else 0) = n at hties
  rw [cutoff_support] at hties
  have he : positiveIndexGapMass T q 1 =
      (∑ i ∈ Finset.range (n-1), w i) / normalizer T :=
    congrArg (fun z => z / normalizer T) (drop_last_guard n w)
  rw [he, primeDeletedFraction, ← add_div]
  congr 1
  change _ + ((n : ℝ) - (actualOrdinateSupport T).card) = _
  rw [show ((n : ℝ) - (actualOrdinateSupport T).card) =
      (∑ i ∈ Finset.range (n-1), if x (i+1) = x i then (1 : ℝ) else 0) by linarith,
    ← Finset.sum_add_distrib]
  simp_rw [hsplit]
  exact Finset.sum_boole _ _

/-- A positive first-rank mass follows if the measured vacancy stays below
the lower small-gap proportion. This estimate does not prescribe its sine value. -/
theorem eventually_firstGap_lower {q a d : ℝ} (hq : 0 ≤ q)
    (hd : ∀ᶠ T : ℝ in atTop, primeDeletedFraction T ≤ d)
    (ha : a + d < smallGapProportion q) :
    ∀ᶠ T : ℝ in atTop, a < positiveIndexGapMass T q 1 := by
  obtain ⟨b,hab,hb⟩ := exists_between ha
  have hf := eventually_lt_of_lt_liminf hb
    (show (atTop : Filter ℝ).IsBoundedUnder (· ≥ ·) (smallGapFraction q) from
      ⟨0, eventually_map.mpr (Eventually.of_forall (smallGapFraction_nonneg q))⟩)
  have hratio := tendsto_count_div_mainTerm.mul_const b
  simp only [one_mul] at hratio
  filter_upwards [hd,hf,hratio.eventually_const_lt hab, eventually_gt_atTop (1 : ℝ),
    tendsto_count_div_mainTerm.eventually_const_lt (by norm_num : (0 : ℝ) < 1)]
    with T hv hf hr hT hn
  have hD : 0 < normalizer T :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  change 0 < (Ncount 0 T : ℝ) / normalizer T at hn
  have hN : (Ncount 0 T : ℝ) ≠ 0 := (pos_of_mul_pos_left
    (show 0 < (Ncount 0 T : ℝ) * (normalizer T)⁻¹ by simpa [div_eq_mul_inv] using hn)
    (inv_nonneg.mpr hD.le)).ne'
  have hx := mul_lt_mul_of_pos_left hf hn
  have hmain := firstGap_add_primeDeleted_eq hT hq
  have hf' : (Ncount 0 T : ℝ)/normalizer T * smallGapFraction q T =
      ((smallGapIndices q T).card : ℝ) / normalizer T := by
    unfold smallGapFraction
    field_simp [hN, hD.ne']
  rw [hf'] at hx
  change a + d < ((Ncount 0 T : ℝ)/normalizer T)*b at hr
  linarith

/-- Under density-one vacancy, the certified degree-285 input ensures positive
mass of strictly positive consecutive spacings at the indicated physical width. -/
theorem eventually_certified_firstGap_positive [LamzouriCompactDeletion2026]
    (hv : Tendsto primeDeletedFraction atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      c < positiveIndexGapMass T (392391339 / 500000000) 1 := by
  let q : ℝ := 392391339 / 500000000
  have hp : 0 < smallGapProportion q := LamzouriGapKernel285.smallGapProportion_certified285
  let d := smallGapProportion q / 3
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨d, hd, eventually_firstGap_lower (d := d) (by norm_num [q])
    ((hv.eventually_lt_const hd).mono (fun _ ht => ht.le)) ?_⟩
  dsimp [d]
  linarith

/-- Packing for the first strictly positive chronological spacing. Each
distinct height after the first gives one positive adjacent gap. The sum
of all internal physical gaps is at most T, so at most D/q exceed q/L. -/
theorem firstGap_distinct_packing {T q : ℝ} (hT : 1 < T) (hq : 0 < q) :
    (((actualOrdinateSupport T).card : ℝ) - 1) / normalizer T - 1/q ≤
      positiveIndexGapMass T q 1 := by
  let n := Ncount 0 T
  let s := Finset.range (n-1)
  let L := unfoldingScale T
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hD : 0 < normalizer T :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hrow (i : ℕ) : (1 : ℝ) ≤
      (if cutoffGap T i * Real.log T ≤ 2 * Real.pi * q then 1 else 0) +
        (L/q) * cutoffGap T i := by
    by_cases hs : cutoffGap T i * Real.log T ≤ 2 * Real.pi * q
    · rw [if_pos hs]
      linarith only [mul_nonneg (div_nonneg hL.le hq.le) (cutoffGap_nonneg T i)]
    · rw [if_neg hs, zero_add]
      have hl : q < L * cutoffGap T i := by
        change q < Real.log T / (2 * Real.pi) * cutoffGap T i
        rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
        simpa [mul_comm] using lt_of_not_ge hs
      rw [div_mul_eq_mul_div, le_div_iff₀ hq, one_mul]
      exact hl.le
  have hsub : s ⊆ Finset.range n := Finset.range_mono (Nat.sub_le _ _)
  have hfirst : 0 ≤ cutoffOrdinate T 0 := by
    by_cases hn : 0 < Ncount 0 T
    · exact (cutoffOrdinate_bounds hn).1.le
    · rw [cutoffOrdinate_of_count_le (by omega : Ncount 0 T ≤ 0)]
      exact (zero_lt_one.trans hT).le
  have hsum : ∑ i ∈ s, cutoffGap T i ≤ T := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, cutoffGap T i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => cutoffGap_nonneg T i)
      _ = T - cutoffOrdinate T 0 := sum_cutoffGap T
      _ ≤ T := by linarith
  have hcount : (n : ℝ) - 1 ≤ (s.card : ℝ) := by
    cases hn : n with
    | zero => simp [s,hn]
    | succ k => simp [s,hn]
  have hsumrow := Finset.sum_le_sum (s := s) (fun i _ => hrow i)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_add_distrib,
    Finset.sum_boole, ← Finset.mul_sum] at hsumrow
  have hbound : (n : ℝ) - 1 ≤ ((smallGapIndices q T).card : ℝ) + (L/q)*T :=
    hcount.trans (hsumrow.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hsum (div_nonneg hL.le hq.le))))
  have hdEq : normalizer T = T*L := by
    dsimp [normalizer, L, unfoldingScale]
    ring
  have hident : (L/q)*T = normalizer T/q := by rw [hdEq]; ring
  rw [hident] at hbound
  have hscaled := div_le_div_of_nonneg_right hbound hD.le
  have he := firstGap_add_primeDeleted_eq hT hq.le
  unfold primeDeletedFraction at he
  have hunit : normalizer T/q/normalizer T = 1/q := by field_simp [hD.ne', hq.ne']
  rw [add_div, hunit, sub_div] at hscaled
  rw [sub_div] at he
  change (Ncount 0 T : ℝ) / normalizer T - 1 / normalizer T ≤ _ at hscaled
  rw [sub_div]
  linarith

end RiemannResearch.Analysis.MontgomeryPositiveGap
