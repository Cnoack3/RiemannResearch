import RiemannResearch.RH.RawMobiusSubpowerCriterion

/-!
# Fixed-exponent consequences of the actual finite Möbius budget

Source: continuation of the user's NymanBeurlingSubpowerAudit20260924.md,
September 24, 2026. The proofs use only that module's actual zero obstruction; every arithmetic
growth hypothesis remains explicit. No external theorem is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- A frequent fixed-power budget bound excludes zeros strictly to the right
of `(1 + α) / 2`. Each exponent has its own precise zero-free half-plane. -/
theorem zeta_ne_zero_of_frequently_raw_square_budget_power
    (α : ℝ) (hα : 0 ≤ α) (C : ℝ)
    (hC : ∃ᶠ N : ℕ in atTop,
      rawMobiusSquareBudget N ≤ C * ((N : ℝ) + 1) ^ α)
    (s : ℂ) (hs : (1 + α) / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hscrit : (1 / 2 : ℝ) < s.re := by linarith
  have hsne0 : s ≠ 0 := by
    intro he
    norm_num [he] at hscrit
  let δ : ℝ := 2 * s.re - 1 - α
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let c : ℝ := (2 * s.re - 1) / (4 * ‖s‖ ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (by linarith)
      (mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hsne0) 2))
  have hbase : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp hbase
  obtain ⟨N, hCN, hN, hlarge⟩ :=
    (hC.and_eventually ((eventually_ge_atTop 3).and
      (hpow.eventually_gt_atTop ((12 * |C| + 8) / c + 1)))).exists
  let q : ℝ := ((N : ℝ) + 1) ^ α
  let r : ℝ := ((N : ℝ) + 1) ^ δ
  have hq : 0 < q := Real.rpow_pos_of_pos (by positivity) _
  have hq1 : 1 ≤ q :=
    Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) N]) hα
  have hsplit : ((N : ℝ) + 1) ^ (2 * s.re - 1) = q * r := by
    change ((N : ℝ) + 1) ^ (2 * s.re - 1) =
      ((N : ℝ) + 1) ^ α * ((N : ℝ) + 1) ^ δ
    rw [← Real.rpow_add (by positivity : 0 < (N : ℝ) + 1)]
    congr 1
    dsimp [δ]
    ring
  have hl := rawMobiusSquareBudget_lower_of_zeta_zero N hN s hscrit hs1 hz
  change c * ((N : ℝ) + 1) ^ (2 * s.re - 1) ≤ _ at hl
  rw [hsplit] at hl
  have hupper : rawMobiusSquareBudget N ≤ |C| * q :=
    hCN.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hq.le)
  have hlinear : (c * r) * q ≤ (12 * |C| + 8) * q := by nlinarith
  have hbound : c * r ≤ 12 * |C| + 8 := by
    by_contra h
    have hgap : 0 < c*r-(12*|C|+8) := by linarith
    have hp := mul_pos hgap hq
    nlinarith only [hlinear, hp]
  have hlarge' : (12 * |C| + 8) / c + 1 < r := hlarge
  have hmul : 12 * |C| + 8 + c < c * r := by
    have hm := mul_lt_mul_of_pos_left hlarge' hc
    field_simp [hc.ne'] at hm
    nlinarith
  linarith

/-- Arbitrarily small frequent coefficients exclude also the boundary line.
The frequent sets may depend on the coefficient. This is weaker than requiring
the normalized budget to converge to zero along the whole sequence. -/
theorem zeta_ne_zero_of_frequently_small_raw_square_budget_power
    (α : ℝ) (hα : 0 < α)
    (hsmall : ∀ C : ℝ, 0 < C → ∃ᶠ N : ℕ in atTop,
      rawMobiusSquareBudget N ≤ C * ((N : ℝ) + 1) ^ α)
    (s : ℂ) (hs : (1 + α) / 2 ≤ s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hscrit : (1 / 2 : ℝ) < s.re := by linarith
  have hsne0 : s ≠ 0 := by
    intro he
    norm_num [he] at hscrit
  let c : ℝ := (2 * s.re - 1) / (4 * ‖s‖ ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (by linarith)
      (mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hsne0) 2))
  have hbase : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp hbase
  have hC := hsmall (c / 24) (by positivity)
  obtain ⟨N, hCN, hN, hlarge⟩ :=
    (hC.and_eventually ((eventually_ge_atTop 3).and
      (hpow.eventually_gt_atTop (16 / c)))).exists
  let q : ℝ := ((N : ℝ) + 1) ^ α
  have hdom : q ≤ ((N : ℝ) + 1) ^ (2 * s.re - 1) :=
    Real.rpow_le_rpow_of_exponent_le
      (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by linarith)
  have hl := rawMobiusSquareBudget_lower_of_zeta_zero N hN s hscrit hs1 hz
  change c * ((N : ℝ) + 1) ^ (2 * s.re - 1) ≤ _ at hl
  have hlow : c * q ≤ 12 * rawMobiusSquareBudget N + 8 :=
    (mul_le_mul_of_nonneg_left hdom hc.le).trans hl
  have hupper : rawMobiusSquareBudget N ≤ (c / 24) * q := hCN
  have hbound : c * q ≤ 16 := by nlinarith
  have hlarge' : 16 / c < q := hlarge
  have hmul : 16 < c * q := by
    have hm := mul_lt_mul_of_pos_left hlarge' hc
    field_simp [hc.ne'] at hm
    nlinarith
  linarith

/-- Whole-sequence normalized decay is one concrete provider for the stronger
boundary zero-free theorem. The normalization exponent must be positive. -/
theorem zeta_ne_zero_of_raw_square_budget_normalized_tendsto_zero
    (α : ℝ) (hα : 0 < α)
    (hlim : Tendsto
      (fun N : ℕ => rawMobiusSquareBudget N / ((N : ℝ) + 1) ^ α)
      atTop (𝓝 0))
    (s : ℂ) (hs : (1 + α) / 2 ≤ s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  apply zeta_ne_zero_of_frequently_small_raw_square_budget_power α hα _ s hs hs1
  intro C hC
  have he : ∀ᶠ N : ℕ in atTop,
      rawMobiusSquareBudget N / ((N : ℝ) + 1) ^ α < C :=
    hlim.eventually (gt_mem_nhds hC)
  apply Filter.Eventually.frequently
  filter_upwards [he] with N hN
  exact le_of_lt ((div_lt_iff₀
    (Real.rpow_pos_of_pos (by positivity : 0 < (N : ℝ) + 1) α)).mp hN)


end RiemannResearch.RH.Pareto
