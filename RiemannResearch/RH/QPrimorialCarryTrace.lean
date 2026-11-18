import RiemannResearch.RH.QCRTCarrySourceBudget
import RiemannResearch.RH.PrimeTreeDisplacementPrimeDefect
import RiemannResearch.Analysis.VanishingTraceDeterminant
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Vanishing trace for the actual growing CRT blocks

A two-cutoff argument suffices for convergence: consecutive cutoffs at least
four contain at most one prime. This avoids an asymptotic prime number theorem.
Mertens's product theorem gives the sharper rate in the accompanying note.
-/

noncomputable section
open Filter
open scoped BigOperators Topology ComplexOrder
namespace RiemannResearch.RH.QPrimorialCarryTrace
open QCRTCarrySourceBudget QSquarefreePrimorialCofinality QSquarefreePrimePacket
open Pareto.SquarefreeStageExhaustion

def allDivisorMass (n : ℕ) : ℝ := ∑ d ∈ (primorialPeriod n).divisors, 1 / (d : ℝ)

private theorem mass_nonneg (n : ℕ) : 0 ≤ allDivisorMass n := by
  unfold allDivisorMass
  positivity

theorem mass_prime_step (n : ℕ) (hp : (n + 4).Prime) :
    allDivisorMass (n + 1) = (1 + 1 / ((n + 4 : ℕ) : ℝ)) * allDivisorMass n := by
  have hc := hp.coprime_iff_not_dvd.mpr (cutoff_prime_fresh n hp)
  unfold allDivisorMass
  rw [primorialPeriod_prime_step n hp, Pareto.sum_divisors_coprime hc,
    hp.divisors, Finset.sum_insert (by simp [hp.ne_one.symm]), Finset.sum_singleton]
  rw [add_mul]
  simp only [one_mul]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  simp only [Nat.cast_mul, one_div, mul_inv]

private theorem mass_no_step (n : ℕ) (hp : ¬ (n + 4).Prime) :
    allDivisorMass (n + 1) = allDivisorMass n := by
  simp only [allDivisorMass, primorialPeriod_composite_step n hp]

private theorem mass_step_le (n : ℕ) :
    allDivisorMass (n + 1) ≤ (1 + 1 / ((n + 4 : ℕ) : ℝ)) * allDivisorMass n := by
  by_cases hp : (n + 4).Prime
  · exact (mass_prime_step n hp).le
  · rw [mass_no_step n hp, add_mul, one_mul]
    linarith [mul_nonneg (by positivity : 0 ≤ 1 / ((n + 4 : ℕ) : ℝ)) (mass_nonneg n)]

private theorem two_step (n : ℕ) :
    allDivisorMass (n + 2) ≤ (1 + 1 / ((n + 4 : ℕ) : ℝ)) * allDivisorMass n := by
  by_cases hp : (n + 4).Prime
  · have ho := hp.odd_of_ne_two (by omega)
    have hn : ¬ (n + 1 + 4).Prime := by
      intro h
      have hodd := h.odd_of_ne_two (by omega)
      obtain ⟨a, ha⟩ := ho
      obtain ⟨b, hb⟩ := hodd
      omega
    rw [show n + 2 = n + 1 + 1 by omega, mass_no_step (n + 1) hn, mass_prime_step n hp]
  · have h := mass_step_le (n + 1)
    rw [mass_no_step n hp] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (mass_nonneg n)
    apply add_le_add_right
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (show n + 4 ≤ n + 1 + 4 by omega)

/-- An elementary square-root upper bound for the full divisor Euler product. -/
theorem mass_sq_bound (n : ℕ) :
    allDivisorMass n ^ 2 ≤ allDivisorMass 0 ^ 2 * ((n : ℝ) + 3) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with (_ | _ | n)
    · norm_num
      nlinarith [sq_nonneg (allDivisorMass 0)]
    · rw [mass_no_step 0 (by decide)]
      norm_num
      nlinarith [sq_nonneg (allDivisorMass 0)]
    · have hi := ih n (by omega)
      have hstep := two_step n
      let x : ℝ := (n : ℝ) + 4
      have hx : 1 < x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) n]
      have hfac : (1 + 1 / x)^2 * ((n : ℝ) + 3) ≤ (n : ℝ) + 5 := by
        have hx' : 0 < x := by linarith
        rw [show (n : ℝ) + 3 = x - 1 by dsimp [x]; ring,
          show (n : ℝ) + 5 = x + 1 by dsimp [x]; ring]
        field_simp
        nlinarith
      have hs : allDivisorMass (n + 2)^2 ≤ ((1 + 1 / x) * allDivisorMass n)^2 := by
        apply (sq_le_sq₀ (mass_nonneg _) (mul_nonneg (by dsimp [x]; positivity) (mass_nonneg n))).mpr
        simpa only [Nat.cast_add, Nat.cast_ofNat, x] using hstep
      rw [mul_pow] at hs
      have hb := mul_le_mul_of_nonneg_left hi (sq_nonneg (1 + 1 / x))
      have hc := mul_le_mul_of_nonneg_right hfac (sq_nonneg (allDivisorMass 0))
      push_cast
      nlinarith only [hs, hb, hc]

theorem mass_div_cutoff_tendsto_zero :
    Tendsto (fun n => allDivisorMass n / ((n + 4 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hinf : Tendsto (fun n : ℕ => ((n + 4 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 4)
  have hlim : Tendsto (fun n : ℕ => allDivisorMass 0 ^ 2 / ((n + 4 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hinf
  apply squeeze_zero (fun n => div_nonneg (mass_nonneg _) (by positivity))
    (fun n => Real.le_sqrt_of_sq_le ?_) (by simpa only [Real.sqrt_zero] using hlim.sqrt)
  rw [div_pow]
  have hp : (0 : ℝ) < ((n + 4 : ℕ) : ℝ) := by positivity
  apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).mpr
  have h := mass_sq_bound n
  have h' : allDivisorMass n ^ 2 ≤ allDivisorMass 0 ^ 2 * ((n + 4 : ℕ) : ℝ) := by
    push_cast
    nlinarith [sq_nonneg (allDivisorMass 0)]
  nlinarith only [mul_le_mul_of_nonneg_right h' hp.le]

theorem selected_mass_le (n : ℕ) (s : Finset (DivisorIndex n)) :
    divisorMass n s ≤ allDivisorMass n := by
  classical
  let e : DivisorIndex n ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : s.map e ⊆ (primorialPeriod n).divisors := by
    intro d hd
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hd
    exact j.property.1
  have he := Finset.sum_le_sum_of_subset_of_nonneg (f := fun d : ℕ => 1 / (d : ℝ))
    hsub (fun _ _ _ => by positivity)
  simpa only [divisorMass, allDivisorMass, Finset.sum_map, e, Function.Embedding.coeFn_mk] using he

theorem actual_trace_tendsto_zero (s : ∀ n, Finset (DivisorIndex n)) :
    Tendsto (fun n => blockTrace n (s n)) atTop (𝓝 0) := by
  let C := (Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / ZetaTwoProbability.zetaTwo
  have hp : 0 ≤ C := by
    dsimp [C]
    rw [← StepCorrectionNorm.residueEnergy_eq_log_two_pi_sub_gamma, StepCorrectionNorm.residueEnergy]
    have ht : 0 ≤ ∑' m, StepCorrectionNorm.rawResidueCellEnergy m :=
      tsum_nonneg StepCorrectionNorm.rawResidueCellEnergy_nonneg
    exact div_nonneg (by linarith)
      ZetaTwoProbability.zetaTwo_pos.le
  apply squeeze_zero (fun n => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) _
    (by simpa only [mul_zero] using mass_div_cutoff_tendsto_zero.const_mul C)
  intro n
  apply (blockTrace_upper n (s n)).trans
  calc
    _ = C * (divisorMass n (s n) / ((n + 4 : ℕ) : ℝ)) := by dsimp [C]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (selected_mass_le n (s n)) (by positivity)) hp

/-- The physical screened Gram, complexified entrywise for its spectral polynomial. -/
def omega (n : ℕ) : Matrix (DivisorIndex n) (DivisorIndex n) ℂ :=
  (Matrix.gram ℝ (innovation n)).map Complex.ofReal

theorem omega_trace (n : ℕ) : (omega n).trace.re = blockTrace n Finset.univ := by
  classical
  simp [omega, Matrix.trace, Matrix.diag, Matrix.gram_apply, blockTrace,
    ← Complex.ofReal_pow]

private theorem ofReal_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : (A.map Complex.ofReal).PosSemidef := by
  classical
  let U : Matrix ι ι ℝ := hA.isHermitian.eigenvectorUnitary
  let t := hA.isHermitian.eigenvalues
  have he : A = U * Matrix.diagonal t * U.conjTranspose := by
    simpa only [U, t, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_real_eq_id, Function.id_comp] using hA.isHermitian.spectral_theorem
  let V := U.map Complex.ofReal
  have ha : (Matrix.diagonal fun i => (t i : ℂ)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by
      change (0 : ℂ) ≤ (t i : ℂ)
      exact_mod_cast hA.eigenvalues_nonneg i)
  have hv := ha.mul_mul_conjTranspose_same V
  have hmap : A.map Complex.ofReal =
      V * (Matrix.diagonal fun i => (t i : ℂ)) * V.conjTranspose := by
    rw [he]
    ext i j
    simp [V, Matrix.mul_apply, Matrix.diagonal, Matrix.conjTranspose_apply,
      Complex.ofReal_sum, Complex.ofReal_mul]
  rwa [hmap]

theorem omega_posSemidef (n : ℕ) : (omega n).PosSemidef :=
  ofReal_posSemidef (Matrix.posSemidef_gram ℝ (innovation n))

theorem unscaled_det_tendsto_one (R : ℝ) :
    TendstoUniformlyOn (fun n (z : ℂ) => (1 - z^2 • omega n).det) (fun _ => (1 : ℂ))
      atTop {z : ℂ | ‖z‖ ≤ R} := by
  apply RiemannResearch.Analysis.VanishingTraceDeterminant.det_tendstoUniformlyOn_disk
    omega omega_posSemidef _ R
  simpa only [omega_trace] using (actual_trace_tendsto_zero (fun _ => Finset.univ))

/-- Even a varying bounded nonnegative scale leaves the physical spectral limit constant. -/
theorem bounded_rescaling_det_tendsto_one (a : ℕ → ℝ) {C : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hC : ∀ n, a n ≤ C) (R : ℝ) :
    TendstoUniformlyOn (fun n (z : ℂ) => (1 - z^2 • ((a n : ℂ) • omega n)).det)
      (fun _ => (1 : ℂ)) atTop {z : ℂ | ‖z‖ ≤ R} := by
  let A := fun n => (a n : ℂ) • omega n
  have hp (n : ℕ) : (A n).PosSemidef :=
    (omega_posSemidef n).smul (show (0:ℂ) ≤ (a n : ℂ) by exact_mod_cast ha n)
  have he (n : ℕ) : (A n).trace.re = a n * blockTrace n Finset.univ := by
    simp [A, Matrix.trace_smul, smul_eq_mul, Complex.mul_re, omega_trace]
  have h0 (n : ℕ) : 0 ≤ blockTrace n Finset.univ := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply RiemannResearch.Analysis.VanishingTraceDeterminant.det_tendstoUniformlyOn_disk A hp _ R
  simp only [he]
  apply squeeze_zero (fun n => mul_nonneg (ha n) (h0 n))
    (fun n => mul_le_mul_of_nonneg_right (hC n) (h0 n))
  simpa only [mul_zero] using (actual_trace_tendsto_zero (fun _ => Finset.univ)).const_mul C

end RiemannResearch.RH.QPrimorialCarryTrace
