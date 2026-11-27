import RiemannResearch.Analysis.MontgomeryPrimeProbeEnergy
import RiemannResearch.Analysis.MontgomeryGapMesh
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! # Positive gaps of the translated discrete sine model

The explicit pair weights are the ones in Lagarias and Rodgers,
*Higher Correlations and the Alternative Hypothesis*,
arXiv:1905.12123, and in RIEMANN_MICROSCOPIC_SELBERG_TRACE_20261125.md.
We work with the deterministic pair law. The cell estimate reduces a
uniform inverse-width bound to bounded errors at the integer lattice widths. -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryLatticeSine
open MontgomeryPositiveGap MontgomeryPrimeTrace MeasureTheory Set Filter
open scoped Topology BigOperators

/-- The mass per unit length at the positive separation `a * (j+1)`. -/
def gapWeight (a : ℝ) (j : ℕ) : ℝ :=
  a * (1 - Real.sinc (Real.pi * (a * ((j : ℝ) + 1))) ^ 2)

/-- Unweighted positive-gap count per unit length in the discrete sine pair law. -/
def latticeGapMass (a q : ℝ) : ℝ :=
  ∑ j ∈ Finset.range ⌊q / a⌋₊, gapWeight a j

theorem gapWeight_nonneg {a : ℝ} (ha : 0 ≤ a) (j : ℕ) : 0 ≤ gapWeight a j := by
  apply mul_nonneg ha
  have h := Real.abs_sinc_le_one (Real.pi * (a * ((j : ℝ) + 1)))
  have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).2 h
  simpa [sq_abs] using sub_nonneg.mpr hs

theorem latticeGapMass_mono {a : ℝ} (ha : 0 < a) : Monotone (latticeGapMass a) := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.floor_mono (div_le_div_of_nonneg_right hxy ha.le))
  · exact fun j _ _ => gapWeight_nonneg ha.le j

theorem latticeGapMass_below_spacing {a q : ℝ} (ha : 0 < a) (hq : q < a) :
    latticeGapMass a q = 0 := by
  have hf : ⌊q / a⌋₊ = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hp
    have hh := (Nat.one_le_floor_iff (q / a)).mp hp
    linarith [(le_div_iff₀ ha).mp hh]
  simp [latticeGapMass, hf]

theorem sineGapMass_strictly_pos {q : ℝ} (hq : 0 < q) : 0 < sineGapMass q := by
  unfold sineGapMass
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    ((show Continuous (fun u : ℝ => 1 - Real.sinc (Real.pi * u) ^ 2) by
      fun_prop).intervalIntegrable _ _)
    ?_ hq
  intro x hx
  have hz := mul_ne_zero Real.pi_ne_zero (ne_of_gt hx.1)
  have hs : |Real.sinc (Real.pi * x)| < 1 := by
    rw [Real.sinc_of_ne_zero hz, abs_div, div_lt_one (abs_pos.mpr hz)]
    exact Real.abs_sin_lt_abs hz
  have hsq := (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).2 hs
  simpa [sq_abs] using sub_pos.mpr hsq

set_option maxHeartbeats 1500000 in
/-- The total mass removed from the positive lattice comb by the sine hole. -/
theorem lattice_hole_hasSum {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    HasSum (fun j : ℕ => a - gapWeight a j) ((1 - a) / 2) := by
  have hc := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero (x := a) ⟨ha.le, ha1⟩
  change HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * a))
    ((-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 / (Nat.factorial 2 : ℝ) * bernoulliFun 2 a) at hc
  rw [bernoulliFun_two] at hc
  let f := fun n : ℕ =>
    (1 / (2 * Real.pi ^ 2 * a)) *
      ((1 / (n : ℝ) ^ 2) - (1 / (n : ℝ) ^ 2) * Real.cos (2 * Real.pi * n * a))
  have hf : HasSum f ((1 - a) / 2) := by
    have hv : (1 / (2 * Real.pi ^ 2 * a)) *
        (Real.pi ^ 2 / 6 - (-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 /
          (Nat.factorial 2 : ℝ) * (a ^ 2 - a + 6⁻¹)) = (1 - a) / 2 := by
      norm_num [Nat.factorial_succ]
      field_simp [Real.pi_ne_zero, ha.ne']
      <;> ring
    rw [← hv]
    exact (hasSum_zeta_two.sub hc).mul_left (1 / (2 * Real.pi ^ 2 * a))
  have h0 : f 0 = 0 := by simp [f]
  have hshift : HasSum (fun j : ℕ => f (j + 1)) ((1 - a) / 2) := by
    apply (hasSum_nat_add_iff (f := f) 1).mpr
    simpa only [Finset.sum_range_one, h0, add_zero] using hf
  apply hshift.congr_fun
  intro j
  have hn : (j : ℝ) + 1 ≠ 0 := by positivity
  have hz := mul_ne_zero Real.pi_ne_zero (mul_ne_zero ha.ne' hn)
  simp only [f, gapWeight, Nat.cast_add, Nat.cast_one, Real.sinc_of_ne_zero hz]
  rw [show 2 * Real.pi * ((j : ℝ) + 1) * a = 2 * (Real.pi * (a * ((j : ℝ) + 1))) by ring,
    Real.cos_two_mul_eq_one_sub]
  field_simp [ha.ne', Real.pi_ne_zero, hn]
  <;> ring

/-- At integer lattice widths the signed first-order offset is exact in the limit. -/
theorem mesh_gap_deficit_tendsto {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun n : ℕ => (n : ℝ) * a - latticeGapMass a ((n : ℝ) * a))
      atTop (𝓝 ((1 - a) / 2)) := by
  have h := (lattice_hole_hasSum ha ha1).tendsto_sum_nat
  apply h.congr'
  filter_upwards with n
  simp [latticeGapMass, mul_div_cancel_right₀ _ ha.ne', Finset.sum_sub_distrib]

private theorem continuous_hole_integrable :
    IntegrableOn (fun x : ℝ => Real.sinc (Real.pi * x) ^ 2) (Ioi 0) := by
  by_contra hn
  have hh := integral_undef hn
  rw [integral_sinc_sq_pi_Ioi] at hh
  norm_num at hh

/-- The signed error is an explicit sawtooth plus the difference of two
positive tails. The leading sawtooth has zero integral on every lattice cell. -/
theorem gap_discrepancy_tail_identity {a q : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hq : 0 ≤ q) :
    let n := ⌊q / a⌋₊
    latticeGapMass a q - sineGapMass q =
      a * (1 / 2 - (q / a - (n : ℝ))) + (∑' j : ℕ, (a - gapWeight a (j + n))) -
        ∫ x in Ioi q, Real.sinc (Real.pi * x) ^ 2 := by
  dsimp only
  have ht := ((hasSum_nat_add_iff' ⌊q / a⌋₊).mpr (lattice_hole_hasSum ha ha1)).tsum_eq
  have hi := intervalIntegral.integral_Ioi_sub_Ioi continuous_hole_integrable hq
  rw [integral_sinc_sq_pi_Ioi, primeSineHoleMass_eq] at hi
  rw [ht]
  simp only [latticeGapMass, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have halg (k : ℕ) : a * (1 / 2 - (q / a - (k : ℝ))) = a / 2 - q + (k : ℝ) * a := by
    field_simp [ha.ne']
    ring
  rw [halg]
  linarith only [hi]

private theorem continuous_hole_tendsto {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    {Q : ι → ℝ}
    (htop : Tendsto Q F atTop) :
    Tendsto (fun n => Q n - sineGapMass (Q n)) F (𝓝 (1 / 2)) := by
  have hcont := intervalIntegral_tendsto_integral_Ioi 0 continuous_hole_integrable htop
  simpa only [integral_sinc_sq_pi_Ioi, primeSineHoleMass_eq] using hcont

/-- Raw large-width discrepancy remembers the fractional position in the cell.
In particular it tends to `a/2` on lattice widths and to zero at midpoints. -/
theorem phase_gap_discrepancy_tendsto {a t : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (ht : t ∈ Ico 0 1) :
    Tendsto (fun n : ℕ => latticeGapMass a (((n : ℝ) + t) * a) -
      sineGapMass (((n : ℝ) + t) * a)) atTop (𝓝 (a * (1 / 2 - t))) := by
  let Q : ℕ → ℝ := fun n => ((n : ℝ) + t) * a
  have htop : Tendsto Q atTop atTop :=
    (tendsto_atTop_add_const_right atTop t tendsto_natCast_atTop_atTop).atTop_mul_const ha
  have hcont := continuous_hole_tendsto htop
  have h := (hcont.sub (mesh_gap_deficit_tendsto ha ha1)).sub_const (t * a)
  rw [show 1 / 2 - (1 - a) / 2 - t * a = a * (1 / 2 - t) by ring] at h
  apply h.congr'
  filter_upwards with n
  have hf : ⌊(n : ℝ) + t⌋₊ = n :=
    (Nat.floor_eq_iff (by linarith [ht.1, Nat.cast_nonneg (α := ℝ) n])).2
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  dsimp [Q, latticeGapMass]
  simp only [mul_div_cancel_right₀ _ ha.ne', hf, Nat.floor_natCast]
  ring

/-- The same finite arithmetic probe is used for the lattice and actual zeros. -/
theorem latticeSignedTrace_below_spacing {a q : ℝ} (hq : 0 < q) (hqa : q < a) :
    Tendsto (fun T : ℝ => latticeGapMass a q - q + primeProbeEnergy T q)
      atTop (𝓝 (-sineGapMass q)) ∧ -sineGapMass q < 0 := by
  refine ⟨?_, neg_neg_of_pos (sineGapMass_strictly_pos hq)⟩
  rw [latticeGapMass_below_spacing (hq.trans hqa) hqa]
  have h := (primeProbeEnergy_tendsto hq.le).const_add (0 - q)
  simpa only [show (0 - q) + (q - sineGapMass q) = -sineGapMass q by ring] using h

/-- Individual noncentral tent translates have no support inside the comparison band. -/
theorem alias_tent_zero {a ξ : ℝ} (ha : 0 < a) (hξ : |ξ| < 1 / a - 1)
    {m : ℤ} (hm : m ≠ 0) : max (1 - |ξ - (m : ℝ) / a|) 0 = 0 := by
  have hm' : (1 : ℝ) ≤ |(m : ℝ)| := by
    have h : (1 : ℤ) ≤ |m| := by
      cases le_total 0 m with
      | inl h => rw [abs_of_nonneg h]; omega
      | inr h => rw [abs_of_nonpos h]; omega
    exact_mod_cast h
  have htri := abs_sub_abs_le_abs_sub ((m : ℝ) / a) ξ
  rw [abs_div, abs_of_pos ha, abs_sub_comm ((m : ℝ) / a) ξ] at htri
  exact max_eq_right (by linarith [div_le_div_of_nonneg_right hm' ha.le])

/-- The noncentral Dirac atoms in the reciprocal comb also lie outside the band. -/
theorem reciprocal_comb_off_band {a ξ : ℝ} (ha : 0 < a) (hξ : |ξ| < 1 / a - 1)
    {m : ℤ} (hm : m ≠ 0) : ξ ≠ (m : ℝ) / a := by
  intro h
  have hh := alias_tent_zero ha hξ hm
  rw [h, sub_self, abs_zero] at hh
  norm_num at hh

/-- In the open comparison band the entire periodized triangular density reduces
to its central translate. This evaluates the continuous part of the Poisson formula. -/
theorem periodized_tent_eq_in_band {a ξ : ℝ} (ha : 0 < a) (hξ : |ξ| < 1 / a - 1) :
    (∑' m : ℤ, max (1 - |ξ - (m : ℝ) / a|) 0) = max (1 - |ξ|) 0 := by
  rw [tsum_eq_single 0]
  · simp
  · intro m hm
    exact alias_tent_zero ha hξ hm

/-- Any prescribed finite bandwidth admits a lattice pair law with the
same reciprocal comb and central tent on that band and a missing positive
gap interval. Lagarias and Rodgers, Theorem 1.8(i), gives the corresponding
point process and its all-order band-limited agreement:
https://arxiv.org/abs/1907.03391. Here the Fourier and gap claims are
proved directly for the pair formula. -/
theorem finite_band_lattice_gap_obstruction {B : ℝ} (hB : 0 ≤ B) :
    ∃ a q : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 < q ∧
      (∀ ξ : ℝ, |ξ| ≤ B →
        (∑' m : ℤ, max (1 - |ξ - (m : ℝ) / a|) 0) = max (1 - |ξ|) 0 ∧
        ∀ m : ℤ, m ≠ 0 → ξ ≠ (m : ℝ) / a) ∧
      latticeGapMass a q = 0 ∧ 0 < sineGapMass q := by
  let a := (B + 2)⁻¹
  have hpos : 0 < B + 2 := by linarith
  have ha : 0 < a := inv_pos.mpr hpos
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [← one_div, div_le_one hpos]
    linarith
  have hband : B < 1 / a - 1 := by
    dsimp [a]
    simp only [one_div, inv_inv]
    linarith
  refine ⟨a, a / 2, ha, ha1, by positivity, ?_,
    latticeGapMass_below_spacing ha (by linarith), sineGapMass_strictly_pos (by positivity)⟩
  intro ξ hξ
  exact ⟨periodized_tent_eq_in_band ha (hξ.trans_lt hband),
    fun _ hm => reciprocal_comb_off_band ha (hξ.trans_lt hband) hm⟩

/-- Twice the discrepancy of the integrated positive-gap counts, before width normalization. -/
def integratedError (a Q : ℝ) : ℝ :=
  2 * ∫ x in (0 : ℝ)..Q, latticeGapMass a x - sineGapMass x

private theorem integratedError_increment {a : ℝ} (ha : 0 < a) (L R : ℝ) :
    integratedError a R - integratedError a L =
      2 * ∫ x in L..R, latticeGapMass a x - sineGapMass x := by
  have hi (u v : ℝ) : IntervalIntegrable (fun x => latticeGapMass a x - sineGapMass x)
      volume u v :=
    (latticeGapMass_mono ha).intervalIntegrable.sub sineGapMass_mono.intervalIntegrable
  have h := intervalIntegral.integral_add_adjacent_intervals (hi 0 L) (hi L R)
  unfold integratedError
  linarith only [h]

private theorem cell_increment {a l r : ℝ} (ha : 0 < a) {n : ℕ}
    (hl : (n : ℝ) * a ≤ l) (hlr : l ≤ r) (hr : r ≤ ((n : ℝ) + 1) * a) :
    integratedError a r - integratedError a l =
      2 * ((r - l) * (∑ j ∈ Finset.range n, gapWeight a j) - ∫ x in l..r, sineGapMass x) := by
  rw [integratedError_increment ha, intervalIntegral.integral_sub
    (latticeGapMass_mono ha).intervalIntegrable sineGapMass_mono.intervalIntegrable]
  have hh : (∫ x in l..r, latticeGapMass a x) =
      ∫ _x in l..r, (∑ j ∈ Finset.range n, gapWeight a j) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hlr
    intro x hx
    have hx0 : 0 ≤ x := le_trans (by positivity : 0 ≤ (n : ℝ) * a) (hl.trans hx.1.le)
    have hf : ⌊x / a⌋₊ = n := (Nat.floor_eq_iff (div_nonneg hx0 ha.le)).2
      ⟨(le_div_iff₀ ha).2 (hl.trans hx.1.le), (div_lt_iff₀ ha).2 (hx.2.trans_le hr)⟩
    simp [latticeGapMass, hf]
  rw [hh, intervalIntegral.integral_const, smul_eq_mul]

/-- Unconditional decay of the Cesàro discrepancy at lattice widths. -/
theorem mesh_cesaro_error_tendsto {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun n : ℕ => integratedError a ((n : ℝ) * a) / ((n : ℝ) * a))
      atTop (𝓝 0) := by
  let L := fun n : ℕ => (n : ℝ) * a
  let F := fun x : ℝ => x - sineGapMass x
  have hmono : Monotone F := fun x y hxy => by
    dsimp [F]; linarith [(sineGapMass_increment_bounds hxy).2]
  have hf : Tendsto (fun n => F (L n)) atTop (𝓝 (1 / 2)) :=
    continuous_hole_tendsto (tendsto_natCast_atTop_atTop.atTop_mul_const ha)
  have hf' : Tendsto (fun n : ℕ => F (L (n + 1))) atTop (𝓝 (1 / 2)) :=
    hf.comp (tendsto_add_atTop_nat 1)
  have hw (n : ℕ) : L (n + 1) - L n = a := by simp [L, add_mul]
  have hab (n : ℕ) : L n ≤ L (n + 1) := by linarith only [hw n, ha]
  let I := fun n : ℕ => ∫ x in L n..L (n + 1), F x
  have hI : Tendsto I atTop (𝓝 (a * (1 / 2))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (hf.const_mul a) (hf'.const_mul a)
    · intro n
      have hh := intervalIntegral.integral_mono_on (μ := volume) (hab n)
        (f := fun _ => F (L n)) (g := F) intervalIntegrable_const hmono.intervalIntegrable
        (fun x hx => hmono hx.1)
      simpa [I, intervalIntegral.integral_const, smul_eq_mul, hw] using hh
    · intro n
      have hh := intervalIntegral.integral_mono_on (μ := volume) (hab n)
        (f := F) (g := fun _ => F (L (n + 1))) hmono.intervalIntegrable intervalIntegrable_const
        (fun x hx => hmono hx.2)
      simpa [I, intervalIntegral.integral_const, smul_eq_mul, hw] using hh
  let E := fun n : ℕ => integratedError a (L n)
  have hstep (n : ℕ) : E (n + 1) - E n =
      2 * (I n - a * ((L n - latticeGapMass a (L n)) + a / 2)) := by
    have hR : L (n + 1) = ((n : ℝ) + 1) * a := by simp [L]
    have h := cell_increment ha (n := n) (l := L n) (r := L (n + 1)) le_rfl (hab n) hR.le
    have he : latticeGapMass a (L n) = ∑ j ∈ Finset.range n, gapWeight a j := by
      simp [L, latticeGapMass, mul_div_cancel_right₀ _ ha.ne']
    have hi : I n = ((L (n + 1)) ^ 2 - (L n) ^ 2) / 2 - ∫ x in L n..L (n + 1), sineGapMass x := by
      dsimp [I, F]
      have hid : IntervalIntegrable (fun x : ℝ => x) volume (L n) (L (n + 1)) :=
        continuous_id.intervalIntegrable _ _
      rw [intervalIntegral.integral_sub hid sineGapMass_mono.intervalIntegrable, integral_id]
    dsimp only [E]
    rw [h, he, hi, show L (n + 1) = L n + a by linarith only [hw n]]
    ring
  have hdiff : Tendsto (fun n : ℕ => E (n + 1) - E n) atTop (𝓝 0) := by
    have h :=
      (hI.sub (((mesh_gap_deficit_tendsto ha ha1).add_const (a / 2)).const_mul a)).const_mul 2
    rw [show 2 * (a * (1 / 2) - a * ((1 - a) / 2 + a / 2)) = 0 by ring] at h
    exact h.congr (fun n => (hstep n).symm)
  have h := hdiff.cesaro.div_const a
  rw [zero_div] at h
  apply h.congr
  intro n
  have hsum : (∑ j ∈ Finset.range n, (E (j + 1) - E j)) = E n - E 0 :=
    Finset.sum_range_sub E n
  have h0 : E 0 = 0 := by simp [E, L, integratedError]
  rw [hsum, h0, sub_zero]
  dsimp [E, L]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem sine_integral_tangent {l r : ℝ} (hlr : l ≤ r) :
    0 ≤ (r - l) * sineGapMass r - (∫ x in l..r, sineGapMass x) ∧
    (r - l) * sineGapMass r - (∫ x in l..r, sineGapMass x) ≤ (r - l) ^ 2 / 2 ∧
    0 ≤ (∫ x in l..r, sineGapMass x) - (r - l) * sineGapMass l ∧
    (∫ x in l..r, sineGapMass x) - (r - l) * sineGapMass l ≤ (r - l) ^ 2 / 2 := by
  have hi : IntervalIntegrable sineGapMass volume l r := sineGapMass_mono.intervalIntegrable
  have hj : IntervalIntegrable (fun x : ℝ => x) volume l r := continuous_id.intervalIntegrable _ _
  have hc : ∀ c : ℝ, IntervalIntegrable (fun _ : ℝ => c) volume l r :=
    fun _ => intervalIntegrable_const
  have h1 := intervalIntegral.integral_mono_on (μ := volume) hlr hi (hc (sineGapMass r))
    (fun _ hx => sineGapMass_mono hx.2)
  have h2 := intervalIntegral.integral_mono_on (μ := volume) hlr (hc (sineGapMass l)) hi
    (fun _ hx => sineGapMass_mono hx.1)
  have h3 := intervalIntegral.integral_mono_on (μ := volume) hlr
    ((hc (sineGapMass r - r)).add hj) hi (fun x hx => by
      change sineGapMass r - r + x ≤ sineGapMass x
      linarith [(sineGapMass_increment_bounds hx.2).2])
  have h4 := intervalIntegral.integral_mono_on (μ := volume) hlr hi
    ((hc (sineGapMass l - l)).add hj) (fun x hx => by
      change sineGapMass x ≤ sineGapMass l - l + x
      linarith [(sineGapMass_increment_bounds hx.1).2])
  simp only [intervalIntegral.integral_add (hc _) hj,
    intervalIntegral.integral_const, smul_eq_mul, integral_id] at h1 h2 h3 h4
  exact ⟨by linarith, by nlinarith only [h3], by linarith, by nlinarith only [h4]⟩

/-- The integrated discrepancy lies above its lattice-cell chord; the one-sided
interpolation error is at most the exact Bernoulli variance factor. -/
theorem integratedError_cell_bounds {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc 0 1) (n : ℕ) :
    let L := (n : ℝ) * a
    let R := ((n : ℝ) + 1) * a
    let Q := ((n : ℝ) + t) * a
    let e := integratedError a Q - ((1 - t) * integratedError a L + t * integratedError a R)
    0 ≤ e ∧ e ≤ a ^ 2 * t * (1 - t) := by
  dsimp only
  let L := (n : ℝ) * a
  let R := ((n : ℝ) + 1) * a
  let Q := ((n : ℝ) + t) * a
  have hL : L ≤ Q := by dsimp [L, Q]; exact mul_le_mul_of_nonneg_right (by linarith [ht.1]) ha.le
  have hR : Q ≤ R := by dsimp [Q, R]; exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) ha.le
  have h1 := cell_increment ha (n := n) (l := L) le_rfl hL hR
  have h2 := cell_increment ha (n := n) (r := R) hL hR le_rfl
  let A := (Q - L) * sineGapMass Q - ∫ x in L..Q, sineGapMass x
  let B := (∫ x in Q..R, sineGapMass x) - (R - Q) * sineGapMass Q
  have hA : 0 ≤ A ∧ A ≤ (Q - L) ^ 2 / 2 :=
    ⟨(sine_integral_tangent hL).1, (sine_integral_tangent hL).2.1⟩
  have hB : 0 ≤ B ∧ B ≤ (R - Q) ^ 2 / 2 := (sine_integral_tangent hR).2.2
  have hcancel : (1 - t) * (Q - L) = t * (R - Q) := by dsimp [L, Q, R]; ring
  have hid : integratedError a Q - ((1 - t) * integratedError a L + t * integratedError a R) =
      2 * ((1 - t) * A + t * B) := by
    dsimp [A, B]
    linear_combination (1 - t) * h1 - t * h2 +
      ((∑ j ∈ Finset.range n, gapWeight a j) - sineGapMass Q) * 2 * hcancel
  change 0 ≤ integratedError a Q - _ ∧ integratedError a Q - _ ≤ _
  rw [hid]
  refine ⟨mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hA.1) (mul_nonneg ht.1 hB.1)), ?_⟩
  calc
    _ ≤ 2 * ((1 - t) * ((Q - L) ^ 2 / 2) + t * ((R - Q) ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hA.2 (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left hB.2 ht.1)) (by norm_num)
    _ = a ^ 2 * t * (1 - t) := by dsimp [Q, L, R]; ring

/-- A mesh-point estimate controls every real width, with an explicit interpolation cost. -/
theorem cesaro_error_of_mesh_bound {a C Q : ℝ} (ha : 0 < a) (hQ : 0 < Q)
    (hmesh : ∀ n : ℕ, |integratedError a ((n : ℝ) * a)| ≤ C) :
    |integratedError a Q / Q| ≤ (C + a ^ 2 / 4) / Q := by
  let n := ⌊Q / a⌋₊
  let t := Q / a - (n : ℝ)
  have ht : t ∈ Icc 0 1 := ⟨sub_nonneg.mpr (Nat.floor_le (div_nonneg hQ.le ha.le)),
    by dsimp [t,n]; linarith [Nat.lt_floor_add_one (Q / a)]⟩
  have hQeq : ((n : ℝ) + t) * a = Q := by dsimp [t]; field_simp [ha.ne']; ring
  have h := integratedError_cell_bounds ha ht n
  dsimp only at h
  rw [hQeq] at h
  have h1 := abs_le.mp (hmesh n)
  have h2 := abs_le.mp (hmesh (n + 1))
  simp only [Nat.cast_add, Nat.cast_one] at h2
  have hlow := add_le_add (mul_le_mul_of_nonneg_left h1.1 (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left h2.1 ht.1)
  have hhigh := add_le_add (mul_le_mul_of_nonneg_left h1.2 (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left h2.2 ht.1)
  have hquad : a ^ 2 * t * (1 - t) ≤ a ^ 2 / 4 := by nlinarith only [sq_nonneg (a * (t - 1 / 2))]
  rw [abs_div, abs_of_pos hQ]
  apply div_le_div_of_nonneg_right _ hQ.le
  apply abs_le.mpr
  constructor <;> nlinarith only [h.1, h.2, hquad, sq_nonneg a, hlow, hhigh]

/-- The Cesàro discrepancy tends to zero through all real widths. The
inverse-width estimate above requires a bounded unnormalized error on the mesh. -/
theorem cesaro_error_tendsto {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Tendsto (fun Q : ℝ => integratedError a Q / Q) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 (Metric.tendsto_nhds.mp
    (mesh_cesaro_error_tendsto ha ha1) (ε / 4) (by positivity))
  filter_upwards [eventually_gt_atTop (((M : ℝ) + 1) * a),
    eventually_gt_atTop a, eventually_gt_atTop (a ^ 2 / ε)] with Q hMQ haQ hsize
  let n := ⌊Q / a⌋₊
  let t := Q / a - (n : ℝ)
  have hQ : 0 < Q := ha.trans haQ
  have hn : M + 1 ≤ n := (Nat.le_floor_iff (div_nonneg hQ.le ha.le)).2
    (by rw [Nat.cast_add, Nat.cast_one]; exact (le_div_iff₀ ha).2 hMQ.le)
  have ht : t ∈ Icc 0 1 := ⟨sub_nonneg.mpr (Nat.floor_le (div_nonneg hQ.le ha.le)),
    by dsimp [t, n]; linarith [Nat.lt_floor_add_one (Q / a)]⟩
  have hQeq : ((n : ℝ) + t) * a = Q := by dsimp [t]; field_simp [ha.ne']; ring
  have hL : (n : ℝ) * a ≤ Q := (le_div_iff₀ ha).1 (Nat.floor_le (div_nonneg hQ.le ha.le))
  have hR : ((n : ℝ) + 1) * a ≤ 2 * Q := by nlinarith only [hL, haQ]
  have hbound (m : ℕ) (hm : M ≤ m) (hm0 : 0 < m) (hmQ : (m : ℝ) * a ≤ 2 * Q) :
      |integratedError a ((m : ℝ) * a)| ≤ (ε / 2) * Q := by
    have hu := hM m hm
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (mul_pos (Nat.cast_pos.mpr hm0) ha)] at hu
    have hlt := (div_lt_iff₀ (mul_pos (Nat.cast_pos.mpr hm0) ha)).mp hu
    nlinarith only [hlt, mul_le_mul_of_nonneg_left hmQ (by positivity : 0 ≤ ε / 4)]
  have h1 := abs_le.mp (hbound n (by omega) (by omega) (by linarith))
  have h2 := abs_le.mp (hbound (n + 1) (by omega) (by omega) (by simpa using hR))
  simp only [Nat.cast_add, Nat.cast_one] at h2
  have h := integratedError_cell_bounds ha ht n
  dsimp only at h
  rw [hQeq] at h
  have hlo := add_le_add (mul_le_mul_of_nonneg_left h1.1 (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left h2.1 ht.1)
  have hhi := add_le_add (mul_le_mul_of_nonneg_left h1.2 (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left h2.2 ht.1)
  have ht2 : a ^ 2 * t * (1 - t) ≤ a ^ 2 / 4 := by nlinarith only [sq_nonneg (a * (t - 1/2))]
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hQ, div_lt_iff₀ hQ, abs_lt]
  constructor <;> nlinarith only [h.1, h.2, hlo, hhi, ht2, (div_lt_iff₀ hε).mp hsize,
    mul_pos hε hQ]

end RiemannResearch.Analysis.MontgomeryLatticeSine
