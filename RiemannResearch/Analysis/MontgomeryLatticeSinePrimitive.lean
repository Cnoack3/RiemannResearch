import RiemannResearch.Analysis.MontgomeryLatticeSineComparison

/-! Bounded primitives in the discrete sine comparison from
`RIEMANN_MICROSCOPIC_SELBERG_TRACE_20261125.md`. On complete cells the sawtooth
integrates to zero. An inverse-square bound for the remaining hole discrepancy
then gives an inverse-width rate for the Cesàro discrepancy at every real width. -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryLatticeSine
open MontgomeryPositiveGap MeasureTheory Set Filter
open scoped Topology BigOperators

private def cellSaw (a x : ℝ) : ℝ := a/2 + (⌊x/a⌋₊ : ℝ)*a - x

private theorem cellSaw_integrable {a : ℝ} (ha : 0 < a) (u v : ℝ) :
    IntervalIntegrable (cellSaw a) volume u v := by
  have hm : Monotone (fun x : ℝ => (⌊x/a⌋₊ : ℝ)) := by
    intro x y hxy
    change (⌊x/a⌋₊ : ℝ) ≤ (⌊y/a⌋₊ : ℝ)
    exact_mod_cast Nat.floor_mono (div_le_div_of_nonneg_right hxy ha.le)
  exact (intervalIntegrable_const.add (hm.intervalIntegrable.mul_const a)).sub
    (continuous_id.intervalIntegrable _ _)

private theorem integral_cellSaw_mesh {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ x in (0:ℝ)..((n:ℝ)*a), cellSaw a x) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    let L := (n:ℝ)*a
    let R := ((n:ℝ)+1)*a
    have hR : R = L+a := by dsimp [L,R]; ring
    have hLR : L ≤ R := by linarith only [hR,ha]
    have hcell : (∫ x in L..R, cellSaw a x) = ∫ x in L..R, (a/2+L)-x := by
      apply intervalIntegral.integral_congr_Ioo_of_le hLR
      intro x hx
      have hx0 : 0 ≤ x := (mul_nonneg (Nat.cast_nonneg _) ha.le).trans hx.1.le
      have hf : ⌊x/a⌋₊ = n := (Nat.floor_eq_iff (div_nonneg hx0 ha.le)).2
        ⟨(le_div_iff₀ ha).2 hx.1.le, (div_lt_iff₀ ha).2 hx.2⟩
      simp only [cellSaw, hf, L]
    have hz : (∫ x in L..R, cellSaw a x) = 0 := by
      have hid : IntervalIntegrable (fun x : ℝ => x) volume L R :=
        continuous_id.intervalIntegrable _ _
      have hc : IntervalIntegrable (fun _ : ℝ => a/2+L) volume L R := intervalIntegrable_const
      rw [hcell, intervalIntegral.integral_sub hc hid, intervalIntegral.integral_const,
        smul_eq_mul, integral_id, hR]
      ring
    rw [Nat.cast_succ]
    change (∫ x in (0:ℝ)..R, cellSaw a x) = 0
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (cellSaw_integrable ha 0 L) (cellSaw_integrable ha L R), hz, add_zero]
    exact ih

private theorem primitive_bound_of_inverse_square {f : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hi : ∀ u v : ℝ, IntervalIntegrable f volume u v)
    (hf : ∀ x : ℝ, 1 ≤ x → |f x| ≤ C/x^2) {Q : ℝ} (hQ : 0 ≤ Q) :
    |∫ x in (0:ℝ)..Q, f x| ≤ (∫ x in (0:ℝ)..1, |f x|) + C := by
  by_cases h : Q ≤ 1
  · have ha := intervalIntegral.integral_add_adjacent_intervals (hi 0 Q).abs (hi Q 1).abs
    have hn := intervalIntegral.integral_nonneg (μ := volume) (f := fun x => |f x|) h
      (fun x _ => abs_nonneg _)
    have hb := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := f) hQ
    linarith only [ha, hn, hb, hC]
  · have h1 : 1 ≤ Q := (lt_of_not_ge h).le
    have hpos {x : ℝ} (hx : x ∈ uIcc 1 Q) : 0 < x := by
      rw [uIcc_of_le h1] at hx
      exact zero_lt_one.trans_le hx.1
    have hk : IntervalIntegrable (fun x : ℝ => 1/x^2) volume 1 Q :=
      (continuousOn_const.div (continuous_id.pow 2).continuousOn
        (fun x hx => pow_ne_zero 2 (hpos hx).ne')).intervalIntegrable
    have hd (x : ℝ) (hx : x ∈ uIcc 1 Q) : HasDerivAt (fun x : ℝ => -x⁻¹) (1/x^2) x := by
      have hh : HasDerivAt (fun y : ℝ => (-1)/y) ((0*x-(-1)*1)/x^2) x :=
        (hasDerivAt_const x (-1:ℝ)).div (hasDerivAt_id x) (hpos hx).ne'
      simpa [neg_div,one_div] using hh
    have hk' : (∫ x in (1:ℝ)..Q, 1/x^2) ≤ 1 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hk]
      simp
      positivity
    have htail : |∫ x in (1:ℝ)..Q, f x| ≤ C := calc
      _ ≤ ∫ x in (1:ℝ)..Q, |f x| := intervalIntegral.abs_integral_le_integral_abs h1
      _ ≤ ∫ x in (1:ℝ)..Q, C*(1/x^2) := intervalIntegral.integral_mono_on h1
        (hi 1 Q).abs (hk.const_mul C) (fun x hx => (hf x hx.1).trans_eq (by ring))
      _ = C * ∫ x in (1:ℝ)..Q, 1/x^2 := intervalIntegral.integral_const_mul _ _
      _ ≤ C := by simpa using mul_le_mul_of_nonneg_left hk' hC
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 Q)]
    exact (abs_add_le _ _).trans (add_le_add
      (intervalIntegral.abs_integral_le_integral_abs zero_le_one) htail)

/-- The pointwise inverse-square error in the two hole tails is sufficient
for boundedness of the unnormalized discrepancy at all complete cells. -/
theorem mesh_bound_of_tail_bound {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hC : 0 ≤ C)
    (h : ∀ q : ℝ, 1 ≤ q →
      |(∑' j : ℕ, (a - gapWeight a (j + ⌊q/a⌋₊))) -
        ∫ x in Ioi q, Real.sinc (Real.pi*x)^2| ≤ C/q^2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, |integratedError a ((n:ℝ)*a)| ≤ B := by
  let D := fun x => latticeGapMass a x - sineGapMass x
  let f := fun x => D x - cellSaw a x
  have hD (u v : ℝ) : IntervalIntegrable D volume u v :=
    (latticeGapMass_mono ha).intervalIntegrable.sub sineGapMass_mono.intervalIntegrable
  have hi (u v : ℝ) : IntervalIntegrable f volume u v := (hD u v).sub (cellSaw_integrable ha u v)
  have hf (q : ℝ) (hq : 1 ≤ q) : |f q| ≤ C/q^2 := by
    have hid := gap_discrepancy_tail_identity ha ha1 (zero_le_one.trans hq)
    dsimp only at hid
    have hs : a*(1/2-(q/a-(⌊q/a⌋₊:ℝ))) = cellSaw a q := by
      unfold cellSaw
      field_simp [ha.ne']
      ring
    rw [hs] at hid
    have heq : f q = (∑' j : ℕ, (a - gapWeight a (j + ⌊q/a⌋₊))) -
        ∫ x in Ioi q, Real.sinc (Real.pi*x)^2 := by
      dsimp only [f,D]
      linarith only [hid]
    rw [heq]
    exact h q hq
  let B := 2*((∫ x in (0:ℝ)..1, |f x|) + C)
  have hhead := intervalIntegral.integral_nonneg (μ := volume) (f := fun x => |f x|)
    (zero_le_one : (0:ℝ) ≤ 1) (fun x _ => abs_nonneg _)
  refine ⟨B, mul_nonneg (by norm_num) (add_nonneg hhead hC), ?_⟩
  intro n
  let Q := (n:ℝ)*a
  have hq : 0 ≤ Q := mul_nonneg (Nat.cast_nonneg _) ha.le
  have hz : (∫ x in (0:ℝ)..Q, cellSaw a x) = 0 := integral_cellSaw_mesh ha n
  have he : (∫ x in (0:ℝ)..Q, f x) = ∫ x in (0:ℝ)..Q, D x := by
    rw [show f = fun x => D x - cellSaw a x from rfl,
      intervalIntegral.integral_sub (hD 0 Q) (cellSaw_integrable ha 0 Q),
      hz, sub_zero]
  change |2 * (∫ x in (0:ℝ)..Q, D x)| ≤ B
  rw [← he, abs_mul, abs_of_pos (by norm_num : 0 < (2:ℝ))]
  exact mul_le_mul_of_nonneg_left (primitive_bound_of_inverse_square hC hi hf hq) (by norm_num)

/-- The inverse-width Cesàro estimate, given the pointwise hole-tail comparison. -/
theorem cesaro_inverse_width_of_tail_bound {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hC : 0 ≤ C)
    (h : ∀ q : ℝ, 1 ≤ q →
      |(∑' j : ℕ, (a - gapWeight a (j + ⌊q/a⌋₊))) -
        ∫ x in Ioi q, Real.sinc (Real.pi*x)^2| ≤ C/q^2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Q : ℝ, 0 < Q → |integratedError a Q / Q| ≤ K/Q := by
  obtain ⟨B,hB,hmesh⟩ := mesh_bound_of_tail_bound ha ha1 hC h
  exact ⟨B+a^2/4, by positivity, fun _ hQ => cesaro_error_of_mesh_bound ha hQ hmesh⟩

end RiemannResearch.Analysis.MontgomeryLatticeSine
