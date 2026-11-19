/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Size - biased exponential bounds for finite second moments

The weights may have arbitrary total mass. The exponential tilt under the law
with weights proportional to `w i * x i` controls the second raw moment.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteSizeBiasedExponential

/-- Jensen's exponential inequality for size-biased finite weights. -/
theorem sum_sizeBiased_exp {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (a : ℝ)
    (hwx : ∀ i ∈ s, 0 ≤ w i * x i) (hm : 0 < ∑ i ∈ s, w i * x i) :
    (∑ i ∈ s, w i * x i) *
        Real.exp (a * ((∑ i ∈ s, w i * (x i) ^ 2) / (∑ i ∈ s, w i * x i))) ≤
      ∑ i ∈ s, w i * x i * Real.exp (a * x i) := by
  let m := ∑ i ∈ s, w i * x i
  let q := ∑ i ∈ s, w i * (x i) ^ 2
  let μ := q / m
  let e := Real.exp (a * μ)
  have hμ : μ * m = q := div_mul_cancel₀ q hm.ne'
  have ht (z : ℝ) : e + (a * e) * (z - μ) ≤ Real.exp (a * z) := by
    calc
      _ = e * ((a * z - a * μ) + 1) := by ring
      _ ≤ e * Real.exp (a * z - a * μ) :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Real.exp_pos _).le
      _ = _ := by dsimp only [e]; rw [← Real.exp_add]; congr 1; ring
  change m * e ≤ _
  calc
    _ = m * e + (a * e) * (q - μ * m) := by rw [hμ]; ring
    _ = ∑ i ∈ s, (w i * x i * e + (a * e) * (w i * (x i) ^ 2 - μ * (w i * x i))) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = w i * x i * (e + (a * e) * (x i - μ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (ht (x i)) (hwx i hi)

/-- The same estimate in units of an arbitrary positive common normalizer. -/
theorem normalized_sizeBiased_exp {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (a : ℝ)
    {Z m q : ℝ} (hZ : 0 < Z) (hm : 0 < m)
    (hwx : ∀ i ∈ s, 0 ≤ w i * x i) (hmass : ∑ i ∈ s, w i * x i = Z * m)
    (hsecond : ∑ i ∈ s, w i * (x i) ^ 2 = Z * q) :
    m * Real.exp (a * (q / m)) ≤ (∑ i ∈ s, w i * x i * Real.exp (a * x i)) / Z := by
  have hfirst : 0 < ∑ i ∈ s, w i * x i := hmass ▸ mul_pos hZ hm
  have h := sum_sizeBiased_exp s w x a hwx hfirst
  rw [hmass, hsecond] at h
  have hcancel : Z * q / (Z * m) = q / m := by field_simp [hZ.ne', hm.ne']
  rw [hcancel] at h
  apply (le_div_iff₀ hZ).mpr
  linarith only [h]

/-- Inverting the tilt yields the logarithmic gain at small first moment. -/
theorem secondMoment_le_log_of_tilt {a m q M : ℝ} (ha : 0 < a) (hm : 0 < m)
    (h : m * Real.exp (a * (q / m)) ≤ M) :
    q ≤ (m / a) * Real.log (M / m) := by
  have he : Real.exp (a * (q / m)) ≤ M / m := (le_div_iff₀ hm).mpr (by simpa [mul_comm] using h)
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hl
  calc
    q = (m / a) * (a * (q / m)) := by field_simp [hm.ne', ha.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (div_nonneg hm.le ha.le)


open Filter
open scoped Topology

/-- A fixed tilt bounds the logarithmically scaled second moment eventually
by every constant strictly above the reciprocal tilt. -/
theorem eventually_secondMoment_ratio_le {ι : Type*} {l : Filter ι} {m q : ι → ℝ}
    {a c M : ℝ} (ha : 0 < a) (hc : 1 / a < c) (hM : 0 < M)
    (hm : Tendsto m l (𝓝 0)) (hmpos : ∀ᶠ i in l, 0 < m i)
    (htilt : ∀ᶠ i in l, m i * Real.exp (a * (q i / m i)) ≤ M) :
    ∀ᶠ i in l, q i / (m i * Real.log (1 / m i)) ≤ c := by
  have hd : 0 < a * c - 1 := by
    have := (div_lt_iff₀ ha).mp hc
    linarith only [this]
  let R := max 1 (Real.log M / (a * c - 1))
  have hR : 1 ≤ R := le_max_left _ _
  have hM' : Real.log M ≤ (a * c - 1) * R := by
    have := (div_le_iff₀ hd).mp (le_max_right 1 (Real.log M / (a * c - 1)))
    simpa only [mul_comm] using this
  have hmR := hm.eventually (eventually_lt_nhds (Real.exp_pos (-R)))
  filter_upwards [hmpos, htilt, hmR] with i hi ht hsmall
  have hlog := Real.log_le_log hi hsmall.le
  rw [Real.log_exp] at hlog
  let L := Real.log (1 / m i)
  have hL : L = -Real.log (m i) := by
    simp only [L, Real.log_div one_ne_zero hi.ne', Real.log_one, zero_sub]
  have hRL : R ≤ L := by rw [hL]; linarith only [hlog]
  have hLpos : 0 < L := zero_lt_one.trans_le (hR.trans hRL)
  have hMscale : Real.log M ≤ (a * c - 1) * L :=
    hM'.trans (mul_le_mul_of_nonneg_left hRL hd.le)
  have hraw := secondMoment_le_log_of_tilt ha hi ht
  rw [Real.log_div hM.ne' hi.ne'] at hraw
  apply (div_le_iff₀ (mul_pos hi hLpos)).mpr
  calc
    _ ≤ (m i / a) * (Real.log M + L) := by simpa only [hL, sub_eq_add_neg] using hraw
    _ ≤ (m i / a) * ((a * c - 1) * L + L) :=
      mul_le_mul_of_nonneg_left (add_le_add hMscale le_rfl) (div_nonneg hi.le ha.le)
    _ = _ := by field_simp [ha.ne']; ring

/-- Every strictly available tilt yields the closed upper limit for the
scaled moments. The bound on the exponential moment may depend on the tilt. -/
theorem eventually_secondMoment_ratio_le_of_open_tilts {ι : Type*} {l : Filter ι}
    {m q : ι → ℝ} {A c : ℝ} (hA : 0 < A) (hc : 1 / A < c)
    (hm : Tendsto m l (𝓝 0)) (hmpos : ∀ᶠ i in l, 0 < m i)
    (htilt : ∀ a : ℝ, 0 < a → a < A → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ i in l, m i * Real.exp (a * (q i / m i)) ≤ M) :
    ∀ᶠ i in l, q i / (m i * Real.log (1 / m i)) ≤ c := by
  have hcpos : 0 < c := (one_div_pos.mpr hA).trans hc
  have hca : 1 / c < A := (div_lt_iff₀ hcpos).mpr (by
    simpa only [mul_comm] using (div_lt_iff₀ hA).mp hc)
  obtain ⟨a, hlo, hhi⟩ := exists_between hca
  have ha : 0 < a := (one_div_pos.mpr hcpos).trans hlo
  have hac : 1 / a < c := (div_lt_iff₀ ha).mpr (by
    simpa only [mul_comm] using (div_lt_iff₀ hcpos).mp hlo)
  obtain ⟨M, hM, h⟩ := htilt a ha hhi
  exact eventually_secondMoment_ratio_le ha hac hM hm hmpos h

/-- Specialization to the Conrey–Baluyot open tilt range. -/
theorem eventually_secondMoment_ratio_le_of_tilts_lt_eight_sevenths
    {ι : Type*} {l : Filter ι} {m q : ι → ℝ} {c : ℝ} (hc : 7 / 8 < c)
    (hm : Tendsto m l (𝓝 0)) (hmpos : ∀ᶠ i in l, 0 < m i)
    (htilt : ∀ a : ℝ, 0 < a → a < 8 / 7 → ∃ M : ℝ, 0 < M ∧
      ∀ᶠ i in l, m i * Real.exp (a * (q i / m i)) ≤ M) :
    ∀ᶠ i in l, q i / (m i * Real.log (1 / m i)) ≤ c :=
  eventually_secondMoment_ratio_le_of_open_tilts (A := 8 / 7) (by norm_num)
    (by norm_num at hc ⊢; exact hc) hm hmpos htilt

end RiemannResearch.Analysis.FiniteSizeBiasedExponential
