import RiemannResearch.RH.ZetaTwoReciprocalObstruction
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A stronger permanent squarefree reciprocal obstruction

Source: independently developed continuation of the user-directed increasing-
conductor signed recovery problem, 9 October 2026. The literal radical dual
at 8 -> 2 is combined with the existing four-site dual. All conclusions use
the actual inverse-square Hilbert realization and cumulative stages. The
full signed cross term and complete positive screening remainder survive.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.ZetaTwoDualEightObstruction
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open ZetaTwoReciprocalObstruction SquarefreeRadicalDifference

def natEight (k : ℕ) : ℝ :=
  if k = 1 then 1 else if k = 2 then -4 else
  if k = 7 then -49 else if k = 8 then 64 else 0

private theorem natEight_large (k : ℕ) (hk : 9 ≤ k) : natEight k = 0 := by
  simp only [natEight, if_neg (show k ≠ 1 by omega),
    if_neg (show k ≠ 2 by omega), if_neg (show k ≠ 7 by omega),
    if_neg (show k ≠ 8 by omega)]

private theorem eight_square_summable :
    Summable (fun k => positiveQWeight k * (natEight k)^2) := by
  apply summable_of_ne_finset_zero (s := Finset.range 9)
  intro k hk
  have hlarge : 9 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [natEight_large k hlarge]
  simp

def eightWitness : QHilbert := encodeQ natEight eight_square_summable

theorem eightWitness_sequence : qSequence eightWitness = natEight :=
  qSequence_encodeQ _ _ (by norm_num [natEight])

/-- Complete infinite pairing, evaluated exactly using the finite dual support. -/
theorem inner_eightWitness (x : QHilbert) :
    inner ℝ eightWitness x =
      (qSequence x 8 - qSequence x 7 - qSequence x 2 + qSequence x 1) / zetaTwo := by
  rw [qInner_weighted, eightWitness_sequence]
  rw [tsum_eq_sum (s := Finset.range 9) (by
    intro k hk
    have hlarge : 9 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    rw [natEight_large k hlarge]
    simp)]
  norm_num [Finset.sum_range_succ, natEight, positiveQWeight]
  ring

theorem eightWitness_norm_sq : ‖eightWitness‖^2 = 118 / zetaTwo := by
  rw [← real_inner_self_eq_norm_sq, inner_eightWitness, eightWitness_sequence]
  norm_num [natEight]

theorem eightWitness_reciprocal_energy :
    inner ℝ eightWitness (reciprocalD eightWitness) = 18 / zetaTwo := by
  rw [inner_eightWitness]
  simp only [qSequence_reciprocalD, eightWitness_sequence]
  norm_num [natEight]

theorem eightWitness_inner_fourWitness :
    inner ℝ eightWitness fourWitness = 5 / zetaTwo := by
  rw [inner_eightWitness, fourWitness_sequence]
  norm_num [ZetaTwoConductorFour.natWitness]

theorem eightWitness_inner_DfourWitness :
    inner ℝ eightWitness (reciprocalD fourWitness) = 3 / zetaTwo := by
  rw [inner_eightWitness]
  simp only [qSequence_reciprocalD, fourWitness_sequence]
  norm_num [ZetaTwoConductorFour.natWitness]

theorem eightWitness_inner_qOne : inner ℝ eightWitness qOne = 0 := by
  rw [inner_eightWitness, qSequence_qOne]
  norm_num [qOneSequence]

theorem eightWitness_inner_qResidue (d : ℕ) (hd : 2 ≤ d) (hs : Squarefree d) :
    inner ℝ eightWitness (qResidue d) = 0 := by
  have hdiv : d ∣ 8 ↔ d ∣ 2 := by
    simpa only [show (2 : ℕ)^3 = 8 by norm_num] using
      (hs.dvd_pow_iff_dvd (y := (2 : ℕ)) (by decide : (3 : ℕ) ≠ 0))
  have he := residueFraction_difference_eq_of_dvd_iff d 8 2 hd
    (by norm_num) (by norm_num) hdiv
  rw [inner_eightWitness, qSequence_qResidue]
  have hz : RiemannResearch.RH.ArithmeticCumulative.residueFraction d 8 -
      RiemannResearch.RH.ArithmeticCumulative.residueFraction d 7 -
      RiemannResearch.RH.ArithmeticCumulative.residueFraction d 2 +
      RiemannResearch.RH.ArithmeticCumulative.residueFraction d 1 = 0 := by
    norm_num at he
    linarith
  rw [hz, zero_div]

theorem eightWitness_inner_squarefreeAtom (i : ℕ) :
    inner ℝ eightWitness (squarefreeAtom i) = 0 := by
  unfold squarefreeAtom
  split_ifs with hs
  · exact eightWitness_inner_qResidue (i + 2) (by omega) hs
  · simp

theorem eightWitness_mem_stage_orthogonal (n : ℕ) :
    eightWitness ∈ (stage n)ᗮ := by
  apply ((stage n).mem_orthogonal _).mpr
  intro x hx
  rw [real_inner_comm]
  change x ∈ Submodule.span ℝ
    (Set.range (fun i : Fin n => squarefreeAtom (id i))) at hx
  induction hx using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact eightWitness_inner_squarefreeAtom i
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_right, ihx, ihy]
  | smul c x hx ih => simp [inner_smul_right, ih]

/-- Screening retains the complete signed reciprocal row. -/
theorem eightWitness_inner_compressed (n : ℕ) (x : QHilbert) :
    inner ℝ eightWitness
      (reciprocalD x - (stage n).starProjection (reciprocalD x)) =
      inner ℝ eightWitness (reciprocalD x) := by
  have hp : inner ℝ eightWitness
      ((stage n).starProjection (reciprocalD x)) = 0 := by
    rw [real_inner_comm]
    exact ((stage n).mem_orthogonal _).mp (eightWitness_mem_stage_orthogonal n) _
      ((stage n).starProjection_apply_mem _)
  rw [inner_sub_right, hp, sub_zero]

theorem eightWitness_inner_residual (n : ℕ) :
    inner ℝ eightWitness (residual n) = 0 := by
  have hp : inner ℝ eightWitness (optimizer n) = 0 := by
    rw [real_inner_comm]
    exact ((stage n).mem_orthogonal _).mp (eightWitness_mem_stage_orthogonal n) _
      ((stage n).starProjection_apply_mem _)
  rw [ZetaTwoOptimizerStage.residual, inner_sub_right, eightWitness_inner_qOne, hp,
    sub_zero]

/-- The physical row is a full difference at 8 minus the radical-base
difference at 2; no optimizer coefficient or signed channel is dropped. -/
theorem eightWitness_reciprocal_row (x : QHilbert) :
    inner ℝ eightWitness (reciprocalD x) =
      (qDifference (reciprocalD x) 8 - qDifference (reciprocalD x) 2) / zetaTwo := by
  rw [inner_eightWitness]
  norm_num [qDifference]
  ring

def mixedWitness : QHilbert := (16 : ℝ) • fourWitness + eightWitness

/-- The permanent universal obstruction is perpendicular to the actual
target residual. It therefore supplies no positive lower bound on the
target's normalized screened second moment. -/
theorem mixedWitness_inner_residual (n : ℕ) :
    inner ℝ mixedWitness (residual n) = 0 := by
  simp only [mixedWitness, inner_add_left, real_inner_smul_left,
    fourWitness_inner_residual, eightWitness_inner_residual, mul_zero, add_zero]

theorem mixedWitness_norm_sq : ‖mixedWitness‖^2 = 7958 / zetaTwo := by
  have hcross : inner ℝ fourWitness eightWitness = 5 / zetaTwo := by
    calc
      inner ℝ fourWitness eightWitness = inner ℝ eightWitness fourWitness :=
        real_inner_comm eightWitness fourWitness
      _ = 5 / zetaTwo := eightWitness_inner_fourWitness
  rw [mixedWitness, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left]
  rw [fourWitness_norm_sq, eightWitness_norm_sq, hcross]
  ring

theorem mixedWitness_reciprocal_energy :
    inner ℝ mixedWitness (reciprocalD mixedWitness) = 2674 / zetaTwo := by
  have hcross : inner ℝ fourWitness (reciprocalD eightWitness) = 3 / zetaTwo := by
    calc
      inner ℝ fourWitness (reciprocalD eightWitness) =
          inner ℝ (reciprocalD fourWitness) eightWitness :=
        (reciprocalD_symmetric fourWitness eightWitness).symm
      _ = inner ℝ eightWitness (reciprocalD fourWitness) :=
        real_inner_comm eightWitness (reciprocalD fourWitness)
      _ = 3 / zetaTwo := eightWitness_inner_DfourWitness
  simp only [mixedWitness, map_add, map_smul,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [fourWitness_reciprocal_energy, eightWitness_reciprocal_energy,
    eightWitness_inner_DfourWitness, hcross]
  ring

theorem mixedWitness_mem_stage_orthogonal (n : ℕ) :
    mixedWitness ∈ (stage n)ᗮ :=
  (stage n)ᗮ.add_mem ((stage n)ᗮ.smul_mem 16 (fourWitness_mem_stage_orthogonal n))
    (eightWitness_mem_stage_orthogonal n)

theorem mixedWitness_inner_compressed (n : ℕ) (x : QHilbert) :
    inner ℝ mixedWitness
      (reciprocalD x - (stage n).starProjection (reciprocalD x)) =
      inner ℝ mixedWitness (reciprocalD x) := by
  have hp : inner ℝ mixedWitness
      ((stage n).starProjection (reciprocalD x)) = 0 := by
    rw [real_inner_comm]
    exact ((stage n).mem_orthogonal _).mp (mixedWitness_mem_stage_orthogonal n) _
      ((stage n).starProjection_apply_mem _)
  rw [inner_sub_right, hp, sub_zero]

theorem universal_firstMoment_cap_ge (n : ℕ) (τ : ℝ)
    (hcap : ∀ x : QHilbert, x ∈ (stage n)ᗮ →
      inner ℝ x (reciprocalD x) ≤ τ * ‖x‖^2) :
    (1337 / 3979 : ℝ) ≤ τ := by
  have h := hcap mixedWitness (mixedWitness_mem_stage_orthogonal n)
  rw [mixedWitness_reciprocal_energy, mixedWitness_norm_sq,
    ← mul_div_assoc] at h
  have hs := (div_le_div_iff_of_pos_right zetaTwo_pos).mp h
  linarith

theorem firstMoment_floor_strict : (1 / 3 : ℝ) < 1337 / 3979 := by norm_num

theorem compressed_mixedWitness_norm_sq_ge (n : ℕ) :
    (1337 / 3979 : ℝ)^2 * ‖mixedWitness‖^2 ≤
      ‖reciprocalD mixedWitness -
        (stage n).starProjection (reciprocalD mixedWitness)‖^2 := by
  let s := reciprocalD mixedWitness -
    (stage n).starProjection (reciprocalD mixedWitness)
  have hi : inner ℝ mixedWitness s = (1337 / 3979 : ℝ) * ‖mixedWitness‖^2 := by
    rw [mixedWitness_inner_compressed, mixedWitness_reciprocal_energy,
      mixedWitness_norm_sq]
    ring
  have hc := abs_real_inner_le_norm mixedWitness s
  have hsq := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg mixedWitness) (norm_nonneg s))).mpr hc
  rw [sq_abs, mul_pow, hi] at hsq
  have hp : 0 < ‖mixedWitness‖^2 := by
    rw [mixedWitness_norm_sq]
    exact div_pos (by norm_num) zetaTwo_pos
  have hm : ‖mixedWitness‖^2 *
      ((1337 / 3979 : ℝ)^2 * ‖mixedWitness‖^2) ≤
      ‖mixedWitness‖^2 * ‖s‖^2 := by nlinarith [hsq]
  by_contra hn
  have hlt : ‖s‖^2 < (1337 / 3979 : ℝ)^2 * ‖mixedWitness‖^2 := lt_of_not_ge hn
  have hproduct := mul_pos hp (sub_pos.mpr hlt)
  nlinarith [hproduct]

theorem universal_secondMoment_cap_ge (n : ℕ) (τ : ℝ)
    (hcap : ∀ x : QHilbert, x ∈ (stage n)ᗮ →
      ‖reciprocalD x - (stage n).starProjection (reciprocalD x)‖^2 ≤
        τ * ‖x‖^2) : (1337 / 3979 : ℝ)^2 ≤ τ := by
  have h := (compressed_mixedWitness_norm_sq_ge n).trans
    (hcap mixedWitness (mixedWitness_mem_stage_orthogonal n))
  have hp : 0 < ‖mixedWitness‖^2 := by
    rw [mixedWitness_norm_sq]
    exact div_pos (by norm_num) zetaTwo_pos
  by_contra hn
  have hlt : τ < (1337 / 3979 : ℝ)^2 := lt_of_not_ge hn
  have hproduct := mul_pos hp (sub_pos.mpr hlt)
  nlinarith [hproduct]

theorem no_vanishing_universal_secondMoment_caps (τ : ℕ → ℝ)
    (hcap : ∀ n x, x ∈ (stage n)ᗮ →
      ‖reciprocalD x - (stage n).starProjection (reciprocalD x)‖^2 ≤
        τ n * ‖x‖^2) : ¬ Tendsto τ atTop (𝓝 0) := by
  intro ht
  have hle : (1337 / 3979 : ℝ)^2 ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall
      (fun n => universal_secondMoment_cap_ge n (τ n) (hcap n)))
  norm_num at hle

theorem no_vanishing_universal_firstMoment_caps (τ : ℕ → ℝ)
    (hcap : ∀ n x, x ∈ (stage n)ᗮ →
      inner ℝ x (reciprocalD x) ≤ τ n * ‖x‖^2) :
    ¬ Tendsto τ atTop (𝓝 0) := by
  intro ht
  have hle : (1337 / 3979 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds ht (Eventually.of_forall
      (fun n => universal_firstMoment_cap_ge n (τ n) (hcap n)))
  norm_num at hle

/-- Exact two-dual screen decomposition, retaining the signed cross term
and the complete positive norm-square remainder. -/
theorem two_dual_screen_exact (n : ℕ) :
    let s := screenedResidual n
    let b₄ := zetaTwo * inner ℝ fourWitness s
    let b₈ := zetaTwo * inner ℝ eightWitness s
    let α := (118 * b₄ - 5 * b₈) / 3515
    let β := (30 * b₈ - 5 * b₄) / 3515
    ‖s‖^2 = (118 * b₄^2 - 10 * b₄ * b₈ + 30 * b₈^2) / (3515 * zetaTwo) +
      ‖s - (α • fourWitness + β • eightWitness)‖^2 := by
  have hcross : inner ℝ fourWitness eightWitness = 5 / zetaTwo := by
    calc
      inner ℝ fourWitness eightWitness = inner ℝ eightWitness fourWitness :=
        real_inner_comm eightWitness fourWitness
      _ = 5 / zetaTwo := eightWitness_inner_fourWitness
  have hfour : inner ℝ (screenedResidual n) fourWitness =
      inner ℝ fourWitness (screenedResidual n) :=
    real_inner_comm fourWitness (screenedResidual n)
  have height : inner ℝ (screenedResidual n) eightWitness =
      inner ℝ eightWitness (screenedResidual n) :=
    real_inner_comm eightWitness (screenedResidual n)
  dsimp only
  rw [norm_sub_sq_real, norm_add_sq_real]
  simp only [inner_add_right, real_inner_smul_left, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    fourWitness_norm_sq, eightWitness_norm_sq, hcross,
    eightWitness_inner_fourWitness, hfour, height]
  field_simp [ne_of_gt zetaTwo_pos]
  ring

/-- Both optimizer correction squares appear with their exact signs;
the full remainder and cross term survive the substitution. -/
theorem two_dual_correction_exact (n : ℕ) :
    let s := screenedResidual n
    let b₄ := zetaTwo * inner ℝ fourWitness s
    let b₈ := zetaTwo * inner ℝ eightWitness s
    let α := (118 * b₄ - 5 * b₈) / 3515
    let β := (30 * b₈ - 5 * b₄) / 3515
    quarticFloor n + weightedMismatch n - screening n =
      (118 * b₄^2 - 10 * b₄ * b₈ + 30 * b₈^2) / (3515 * zetaTwo) +
      ‖s - (α • fourWitness + β • eightWitness)‖^2 := by
  have he := two_dual_screen_exact n
  dsimp only at he ⊢
  rw [screenedResidual_energy_exact, signedCorrection] at he
  linarith [he]

end RiemannResearch.RH.ZetaTwoDualEightObstruction
