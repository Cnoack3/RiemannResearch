import RiemannResearch.RH.CompactFrequencyMellinRigidity
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Critical Mellin mixtures: precise logarithmic-energy obstruction

Source: user-provided argument,
`RH_Obstruction_Compact_Frequency_Rigidity_2026-09-21.md`, Sections 4--5.
The logarithmic-energy asymptotic below is an explicitly named analytic
obligation, not a theorem asserted without its provider. The consequences
of that asymptotic are proved from the actual weighted coordinate sequence.

The physical coordinate represented by the index `n` is `n + 1`.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.SpectralObstruction

/-- The actual coordinatewise countable mixture. Absolute convergence under
first-moment control is proved by `criticalMixture_coordinate_summable`. -/
def criticalMixture (a : ℕ → ℂ) (γ : ℕ → ℝ) (n : ℕ) : ℂ :=
  ∑' j, a j * mellinMode (MellinFrequency.criticalPoint (γ j)) n

def criticalAmplitude (a : ℕ → ℂ) (γ : ℕ → ℝ) (j : ℕ) : ℂ :=
  a j * MellinFrequency.criticalPoint (γ j)

def partialEnergy (v : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, paretoWeight n * ‖v n‖ ^ 2

/-- The harmless shift avoids the singular normalization `log 0`. -/
def logEnergy (v : ℕ → ℂ) (N : ℕ) : ℝ :=
  partialEnergy v N / Real.log ((N : ℝ) + 1)

def coefficientEnergy (a : ℕ → ℂ) (γ : ℕ → ℝ) : ℝ :=
  ∑' j, ‖criticalAmplitude a γ j‖ ^ 2

theorem criticalPoint_norm_lower (t : ℝ) :
    (1 / 2 : ℝ) ≤ ‖MellinFrequency.criticalPoint t‖ := by
  have he : ‖MellinFrequency.criticalPoint t‖ ^ 2 = (1 / 2 : ℝ) ^ 2 + t ^ 2 := by
    simp [MellinFrequency.criticalPoint, Complex.sq_norm, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg (MellinFrequency.criticalPoint t), sq_nonneg t]

theorem coefficient_norm_summable (a : ℕ → ℂ) (γ : ℕ → ℝ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖)) :
    Summable (fun j => ‖a j‖) := by
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) _ (ha.mul_left 2)
  intro j
  have h := mul_le_mul_of_nonneg_left (criticalPoint_norm_lower (γ j)) (norm_nonneg (a j))
  simp only [criticalAmplitude, norm_mul]
  nlinarith

private theorem critical_cpow_norm (x t : ℝ) (hx : 0 < x) :
    ‖(x : ℂ) ^ (-MellinFrequency.criticalPoint t)‖ = x ^ (-(1 / 2 : ℝ)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- A frequency-independent bound for a fixed physical coordinate. -/
def criticalModeBound (n : ℕ) : ℝ :=
  ‖((n : ℂ) + 1) * ((n : ℂ) + 2)‖ *
    (((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) + ((n : ℝ) + 2) ^ (-(1 / 2 : ℝ)))

theorem criticalMode_norm_le (t : ℝ) (n : ℕ) :
    ‖mellinMode (MellinFrequency.criticalPoint t) n‖ ≤ criticalModeBound n := by
  rw [mellinMode, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖((n : ℂ) + 1) ^ (-MellinFrequency.criticalPoint t)‖ +
          ‖((n : ℂ) + 2) ^ (-MellinFrequency.criticalPoint t)‖ := norm_sub_le _ _
    _ = _ := by
      have h₁ := critical_cpow_norm ((n : ℝ) + 1) t (by positivity)
      have h₂ := critical_cpow_norm ((n : ℝ) + 2) t (by positivity)
      simpa using congrArg₂ (fun x y : ℝ => x + y) h₁ h₂

/-- Absolute first-moment control makes every actual coordinate series
convergent, even when the ordinates are unbounded. -/
theorem criticalMixture_coordinate_summable (a : ℕ → ℂ) (γ : ℕ → ℝ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖)) (n : ℕ) :
    Summable (fun j => a j * mellinMode (MellinFrequency.criticalPoint (γ j)) n) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) _
    ((coefficient_norm_summable a γ ha).mul_right (criticalModeBound n))
  intro j
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (criticalMode_norm_le (γ j) n) (norm_nonneg (a j))

/-- Absolute first-moment control already proves summability of the
diagonal coefficient energy; this is not an open analytic input. -/
theorem coefficient_square_summable (a : ℕ → ℂ) (γ : ℕ → ℝ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖)) :
    Summable (fun j => ‖criticalAmplitude a γ j‖ ^ 2) := by
  let B : ℝ := ∑' j, ‖criticalAmplitude a γ j‖
  have hb (j : ℕ) : ‖criticalAmplitude a γ j‖ ≤ B :=
    ha.le_tsum j (fun k _ => norm_nonneg _)
  apply Summable.of_nonneg_of_le (fun j => sq_nonneg _) _ (ha.mul_left B)
  intro j
  have h := mul_le_mul_of_nonneg_right (hb j) (norm_nonneg (criticalAmplitude a γ j))
  nlinarith

theorem coefficientEnergy_pos (a : ℕ → ℂ) (γ : ℕ → ℝ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖))
    (hne : ∃ j, a j ≠ 0) : 0 < coefficientEnergy a γ := by
  obtain ⟨j, hj⟩ := hne
  have hb : criticalAmplitude a γ j ≠ 0 :=
    mul_ne_zero hj (MellinFrequency.criticalPoint_ne_zero (γ j))
  have hp : 0 < ‖criticalAmplitude a γ j‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hb) 2
  have hle := (coefficient_square_summable a γ ha).le_tsum j
    (fun k _ => sq_nonneg ‖criticalAmplitude a γ k‖)
  exact lt_of_lt_of_le hp hle

/-- The complete analytic obligation for the actual countable critical-line
mixture. No declaration in this module supplies this provider. Its inputs
are distinct ordinates and absolute first-moment coefficient control. -/
def CriticalPurePointEnergyProvider : Prop :=
  ∀ (a : ℕ → ℂ) (γ : ℕ → ℝ), Function.Injective γ →
    Summable (fun j => ‖criticalAmplitude a γ j‖) →
    Tendsto (logEnergy (criticalMixture a γ)) atTop
      (𝓝 (coefficientEnergy a γ))

/-- Finite weighted energy forces the logarithmically normalized partial
energy to zero. This is independent of any spectral representation. -/
theorem summable_logEnergy_tendsto_zero (v : ℕ → ℂ)
    (hs : Summable (fun n => paretoWeight n * ‖v n‖ ^ 2)) :
    Tendsto (logEnergy v) atTop (𝓝 0) := by
  have he : Tendsto (partialEnergy v) atTop
      (𝓝 (∑' n, paretoWeight n * ‖v n‖ ^ 2)) := by
    change Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      paretoWeight n * ‖v n‖ ^ 2) atTop _
    exact hs.hasSum.tendsto_sum_nat
  have hn : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop.mpr (fun b => by
      have hb : ∀ᶠ N : ℕ in atTop, b ≤ (N : ℝ) :=
        (tendsto_atTop.mp tendsto_natCast_atTop_atTop) b
      filter_upwards [hb] with N hN
      linarith)
  have hl : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  exact he.div_atTop hl

/-- A positive limiting logarithmic energy is an obstruction to membership
in the genuine Pareto square-summable sequence space. -/
theorem not_summable_of_positive_logEnergy_limit (v : ℕ → ℂ) {C : ℝ}
    (hC : 0 < C) (hlim : Tendsto (logEnergy v) atTop (𝓝 C)) :
    ¬ Summable (fun n => paretoWeight n * ‖v n‖ ^ 2) := by
  intro hs
  have hzero : C = 0 :=
    tendsto_nhds_unique hlim (summable_logEnergy_tendsto_zero v hs)
  linarith

/-- Conditional research reduction. The substantive premise is the named
analytic energy provider, together with positive actual coefficient mass.
No zeta-zero or RH assumption is used. -/
theorem criticalMixture_not_summable_of_provider
    (hprovider : CriticalPurePointEnergyProvider)
    (a : ℕ → ℂ) (γ : ℕ → ℝ) (hγ : Function.Injective γ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖))
    (hpos : 0 < coefficientEnergy a γ) :
    ¬ Summable (fun n => paretoWeight n * ‖criticalMixture a γ n‖ ^ 2) := by
  exact not_summable_of_positive_logEnergy_limit (criticalMixture a γ)
    hpos (hprovider a γ hγ ha)

/-- The actual countable critical mixture is excluded by the energy law
as soon as any coefficient is nonzero. The named analytic provider remains
the sole substantive unresolved hypothesis. -/
theorem nonzero_criticalMixture_not_summable_of_provider
    (hprovider : CriticalPurePointEnergyProvider)
    (a : ℕ → ℂ) (γ : ℕ → ℝ) (hγ : Function.Injective γ)
    (ha : Summable (fun j => ‖criticalAmplitude a γ j‖))
    (hne : ∃ j, a j ≠ 0) :
    ¬ Summable (fun n => paretoWeight n * ‖criticalMixture a γ n‖ ^ 2) := by
  exact criticalMixture_not_summable_of_provider hprovider a γ hγ ha
    (coefficientEnergy_pos a γ ha hne)



private theorem sqrt_gap_sq_lower {x : ℝ} (hx : 0 < x) :
    1 / (4 * (x + 1)) ≤ (Real.sqrt (x + 1) - Real.sqrt x) ^ 2 := by
  let A := Real.sqrt x
  let B := Real.sqrt (x + 1)
  have hA : 0 < A := Real.sqrt_pos.mpr hx
  have hB : 0 < B := Real.sqrt_pos.mpr (by linarith)
  have hA2 : A ^ 2 = x := Real.sq_sqrt hx.le
  have hB2 : B ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hsum : 0 < A + B := by positivity
  have hprod : (B - A) * (A + B) = 1 := by nlinarith
  have hbound : (A + B) ^ 2 ≤ 4 * (x + 1) := by
    nlinarith [sq_nonneg (A - B)]
  have he : (B - A) ^ 2 = 1 / (A + B) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hsum.ne')).2
    calc
      _ = ((B - A) * (A + B)) ^ 2 := by ring
      _ = 1 := by rw [hprod]; norm_num
  change 1 / (4 * (x + 1)) ≤ (B - A) ^ 2
  rw [he]
  exact one_div_le_one_div_of_le (pow_pos hsum 2) hbound

/-- Reverse triangle already forces harmonic-scale energy for every
individual critical-line mode, independently of its ordinate. -/
theorem criticalMode_energy_ge_sqrt_gap (t : ℝ) (n : ℕ) :
    (Real.sqrt ((n : ℝ) + 2) - Real.sqrt ((n : ℝ) + 1)) ^ 2 ≤
      paretoWeight n * ‖mellinMode (MellinFrequency.criticalPoint t) n‖ ^ 2 := by
  let x : ℝ := (n : ℝ) + 1
  let y : ℝ := (n : ℝ) + 2
  let A := Real.sqrt x
  let B := Real.sqrt y
  let z : ℂ := ((n : ℂ) + 1) ^ (-MellinFrequency.criticalPoint t)
  let w : ℂ := ((n : ℂ) + 2) ^ (-MellinFrequency.criticalPoint t)
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hA : 0 < A := Real.sqrt_pos.mpr hx
  have hB : 0 < B := Real.sqrt_pos.mpr hy
  have hA2 : A ^ 2 = x := Real.sq_sqrt hx.le
  have hB2 : B ^ 2 = y := Real.sq_sqrt hy.le
  have hnz : ‖z‖ = 1 / A := by
    have hh := critical_cpow_norm x t hx
    rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow] at hh
    simpa [z, x, A, one_div] using hh
  have hnw : ‖w‖ = 1 / B := by
    have hh := critical_cpow_norm y t hy
    rw [Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow] at hh
    simpa [w, y, B, one_div] using hh
  have hAB : A ≤ B := Real.sqrt_le_sqrt (by dsimp [x, y]; linarith)
  have hnonneg : 0 ≤ 1 / A - 1 / B :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hA hAB)
  have hr : 1 / A - 1 / B ≤ ‖z - w‖ := by
    simpa only [hnz, hnw] using norm_sub_norm_le z w
  have hrsq : (1 / A - 1 / B) ^ 2 ≤ ‖z - w‖ ^ 2 := by
    nlinarith [norm_nonneg (z - w)]
  have hm := mul_le_mul_of_nonneg_left hrsq (mul_pos hx hy).le
  have he : x * y * (1 / A - 1 / B) ^ 2 = (B - A) ^ 2 := by
    calc
      _ = A ^ 2 * B ^ 2 * (1 / A - 1 / B) ^ 2 := by rw [hA2, hB2]
      _ = _ := by field_simp [hA.ne', hB.ne']
  have hcast : ((n : ℂ) + 1) * ((n : ℂ) + 2) = ((x * y : ℝ) : ℂ) := by
    simp [x, y]
  have hc : ‖((n : ℂ) + 1) * ((n : ℂ) + 2)‖ = x * y := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hx hy)]
  have henergy :
      paretoWeight n * ‖mellinMode (MellinFrequency.criticalPoint t) n‖ ^ 2 =
        x * y * ‖z - w‖ ^ 2 := by
    rw [mellinMode, norm_mul, hc]
    change (1 / (x * y)) * (x * y * ‖z - w‖) ^ 2 = _
    field_simp [hx.ne', hy.ne']
  change (B - A) ^ 2 ≤ _
  rw [henergy]
  exact he ▸ hm

theorem criticalMode_energy_lower (t : ℝ) (n : ℕ) :
    1 / (4 * ((n : ℝ) + 2)) ≤
      paretoWeight n * ‖mellinMode (MellinFrequency.criticalPoint t) n‖ ^ 2 := by
  have h := sqrt_gap_sq_lower (show 0 < (n : ℝ) + 1 by positivity)
  have h' : 1 / (4 * ((n : ℝ) + 2)) ≤
      (Real.sqrt ((n : ℝ) + 2) - Real.sqrt ((n : ℝ) + 1)) ^ 2 := by
    have he : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
    simpa only [he] using h
  exact h'.trans (criticalMode_energy_ge_sqrt_gap t n)

/-- No individual critical-line Mellin mode belongs to the Pareto Hilbert
space. Unlike the mixture theorem, this has no open analytic provider. -/
theorem criticalMode_not_summable (t : ℝ) :
    ¬ Summable (fun n => paretoWeight n *
      ‖mellinMode (MellinFrequency.criticalPoint t) n‖ ^ 2) := by
  intro hs
  have hh : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ (hs.mul_left 4)
    intro n
    have h := mul_le_mul_of_nonneg_left (criticalMode_energy_lower t n)
      (show (0 : ℝ) ≤ 4 by norm_num)
    have he : (4 : ℝ) * (1 / (4 * ((n : ℝ) + 2))) = 1 / ((n : ℝ) + 2) := by
      field_simp [show (n : ℝ) + 2 ≠ 0 by positivity]
    rwa [he] at h
  have hh' : Summable (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ (1 : ℝ)) := by
    exact hh.congr (fun n => by rw [Real.rpow_one, abs_of_pos (by positivity)])
  have hfalse := (Real.summable_one_div_nat_add_rpow 2 1).1 hh'
  norm_num at hfalse


end RiemannResearch.RH.Pareto.SpectralObstruction
