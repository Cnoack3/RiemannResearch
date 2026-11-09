/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoResidueZeroNormal
import RiemannResearch.RH.ParetoResidueCriticalNormalLimit
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ParetoAtomMellinSignature
import RiemannResearch.RH.ParetoUnscaledDilation
import RiemannResearch.RH.MobiusHilbertCoordinates
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact zero tests for the legal Pareto atoms

The legal atom `g_d(n) = (n % d) / d` is the normalized periodic sequence
in Bagchi, *On Nyman, Beurling and Báez-Duarte's Hilbert space reformulation
of the Riemann hypothesis*, Theorem 1 and §4,
https://www.isibang.ac.in/~statmath/eprints/2005/isibc200535.pdf.
Its existing Mellin signature yields the exact grouped pairing on every
multiple period. The project Möbius charge at six separates the target
from dictionaries omitting that mixed conductor. The arithmetic
normalization uses Mathlib's `Chebyshev.psi_eq_log_lcmUpto`.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin
open RiemannResearch.RH.ParetoAtomMellinSignature
open RiemannResearch.Analysis.FiniteHilbertGram

theorem atom_mem_trial (L d : ℕ) (hL : 0 < L) (hd : 0 < d) (hdL : d ∣ L) :
    normalizedResidueHilbert d hd ∈ trialSpace L :=
  Submodule.subset_span ⟨⟨d, Nat.mem_divisors.mpr ⟨hdL, hL.ne'⟩⟩, rfl⟩

/-- On the nonzero classes the legal atom has exactly the conductor Mellin
signature, including the factor of the actual zeta function. -/
theorem class_pairing_atom_zeta (N d : ℕ) (hd : 0 < d) (hdL : d ∣ N + 1)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∑ r : Fin N, classMellin N s r.castSucc *
      (normalizedAtom d (r.val + 1) : ℂ)) =
      riemannZeta s * ((1 / (d : ℂ)) - (d : ℂ) ^ (-s)) := by
  let f := normalizedResidueHilbert d hd
  have hperiod (r : Fin (N + 1)) (k : ℕ) :
      hilbertSequence f (r.val + (N + 1) * k + 1) = hilbertSequence f (r.val + 1) := by
    have hk : d ∣ (N + 1) * k := hdL.trans (dvd_mul_right _ _)
    dsimp only [f]
    rw [normalizedResidueHilbert_sequence]
    change normalizedAtom d (r.val + (N + 1) * k + 1) = normalizedAtom d (r.val + 1)
    rw [show r.val + (N + 1) * k + 1 = r.val + 1 + (N + 1) * k by omega]
    simp [normalizedAtom, residue, Nat.add_mod, Nat.mod_eq_zero_of_dvd hk]
  have hb (n : ℕ) : |hilbertSequence f n| ≤ 1 := by
    dsimp only [f]
    rw [normalizedResidueHilbert_sequence]
    exact normalizedAtom_abs_le_one d n hd
  have hh := class_pairing_eq_mellin N f hperiod hb s hs
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hmul : s * (riemannZeta s / s * ((1 / (d : ℂ)) - (d : ℂ) ^ (-s))) =
      riemannZeta s * ((1 / (d : ℂ)) - (d : ℂ) ^ (-s)) := by
    field_simp [hs0]
  dsimp only [f] at hh
  rw [paretoMellin_normalizedResidue_zeta d hd s hs hs1, hmul,
    normalizedResidueHilbert_sequence, Fin.sum_univ_castSucc] at hh
  have hlast : ArithmeticCumulative.residueFraction d ((Fin.last N).val + 1) = 0 := by
    simp [ArithmeticCumulative.residueFraction, Nat.mod_eq_zero_of_dvd hdL]
  rw [hlast, Complex.ofReal_zero, mul_zero, add_zero] at hh
  simpa only [Fin.val_castSucc, ArithmeticCumulative.residueFraction, normalizedAtom, residue]
    using hh

/-- A legal atom in the weighted nonzero residue coordinates. -/
def atomVector (N d : ℕ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun r => Real.sqrt (classWeight N r.castSucc) * normalizedAtom d (r.val + 1))

theorem inner_row_atom_eq_zeta {ι : Type*} (N d : ℕ) (hd : 0 < d) (hdL : d ∣ N + 1)
    (z : ι → ℂ) (i : ι × Bool) (hs : 0 < (z i.1).re) (hs1 : z i.1 ≠ 1) :
    inner ℝ (rowVector N z i) (atomVector N d) =
      part i.2 (riemannZeta (z i.1) * ((1 / (d : ℂ)) - (d : ℂ) ^ (-z i.1))) := by
  have hdots : inner ℝ (rowVector N z i) (atomVector N d) =
      ∑ r : Fin N, rowEntry N z i r * normalizedAtom d (r.val + 1) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, star_trivial]
    apply Finset.sum_congr rfl
    intro r _
    change (Real.sqrt (classWeight N r.castSucc) * normalizedAtom d (r.val + 1)) *
      (rowEntry N z i r / Real.sqrt (classWeight N r.castSucc)) = _
    field_simp [(Real.sqrt_pos.mpr (classWeight_pos N r.castSucc)).ne']
  rw [hdots]
  have h := congrArg (part i.2) (class_pairing_atom_zeta N d hd hdL (z i.1) hs hs1)
  rcases i with ⟨j, b⟩
  cases b <;> simpa [rowEntry, part, Complex.mul_re, Complex.mul_im] using h

/-- Zero tests annihilate each legal conductor separately. -/
theorem zero_row_orthogonal_atom {ι : Type*} (N d : ℕ) (hd : 0 < d) (hdL : d ∣ N + 1)
    (z : ι → ℂ) (i : ι × Bool) (hs : 0 < (z i.1).re) (hs1 : z i.1 ≠ 1)
    (hz : riemannZeta (z i.1) = 0) :
    inner ℝ (rowVector N z i) (atomVector N d) = 0 := by
  rw [inner_row_atom_eq_zeta N d hd hdL z i hs hs1, hz, zero_mul]
  cases i.2 <;> rfl

/-- The running LCM is indexed by its count of nonzero residue classes. -/
def lcmResidueIndex (M : ℕ) : ℕ := Nat.lcmUpto M - 1

theorem lcmResidueIndex_succ (M : ℕ) : lcmResidueIndex M + 1 = Nat.lcmUpto M :=
  Nat.sub_add_cancel (Nat.lcmUpto_pos M)

theorem lcmResidueIndex_tendsto : Tendsto lcmResidueIndex atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b + 1)] with M hM
  have hdiv : M ∣ Nat.lcmUpto M :=
    Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hlarge := Nat.le_of_dvd (Nat.lcmUpto_pos M) hdiv
  have hL := lcmResidueIndex_succ M
  omega

/-- The normalization of the grouped Gram is exactly the summatory von Mangoldt scale. -/
theorem lcm_log_eq_psi (M : ℕ) :
    Real.log ((lcmResidueIndex M : ℝ) + 1) = Chebyshev.psi (M : ℝ) := by
  have hcast : (lcmResidueIndex M : ℝ) + 1 = (Nat.lcmUpto M : ℝ) := by
    exact_mod_cast lcmResidueIndex_succ M
  rw [hcast, Chebyshev.psi_eq_log_lcmUpto]

theorem lcm_log_eq_sum_vonMangoldt (M : ℕ) :
    Real.log ((lcmResidueIndex M : ℝ) + 1) =
      ∑ n ∈ Finset.Ioc 0 M, ArithmeticFunction.vonMangoldt n := by
  rw [lcm_log_eq_psi]
  simp [Chebyshev.psi]

/-- Every prime up to the LCM cutoff is annihilated in the actual class pairing. -/
theorem lcm_zero_row_orthogonal_prime {ι : Type*} (M p : ℕ) (hp : p.Prime) (hpM : p ≤ M)
    (z : ι → ℂ) (i : ι × Bool) (hs : 0 < (z i.1).re) (hs1 : z i.1 ≠ 1)
    (hz : riemannZeta (z i.1) = 0) :
    inner ℝ (rowVector (lcmResidueIndex M) z i) (atomVector (lcmResidueIndex M) p) = 0 := by
  have hd : p ∣ lcmResidueIndex M + 1 := by
    rw [lcmResidueIndex_succ]
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hp.pos, hpM⟩)
  exact zero_row_orthogonal_atom _ _ hp.pos hd z i hs hs1 hz

private theorem moebius_two : ArithmeticFunction.moebius 2 = -1 :=
  ArithmeticFunction.moebius_apply_prime Nat.prime_two

private theorem moebius_three : ArithmeticFunction.moebius 3 = -1 :=
  ArithmeticFunction.moebius_apply_prime Nat.prime_three

private theorem moebius_six : ArithmeticFunction.moebius 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 by decide,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by decide : Nat.Coprime 2 3),
    moebius_two, moebius_three]
  norm_num

private theorem mobius_six_norm_sq : ‖mobiusDifferenceCLM 6‖ ^ 2 = 92 := by
  rw [mobiusDifferenceCLM_norm_sq 6 (by decide)]
  have hset : Finset.Icc 1 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) := by decide
  have h₁ : dualCoeff 6 1 = 2 := by
    norm_num [dualCoeff, moebius_six, moebius_two, moebius_three]
  have h₂ : dualCoeff 6 2 = 0 := by
    norm_num [dualCoeff, moebius_six, moebius_two, moebius_three]
  have h₃ : dualCoeff 6 3 = -1 := by
    norm_num [dualCoeff, moebius_six, moebius_two, moebius_three]
  have h₄ : dualCoeff 6 4 = 0 := by
    norm_num [dualCoeff, moebius_six, moebius_two, moebius_three]
  have h₅ : dualCoeff 6 5 = -1 := by
    norm_num [dualCoeff, moebius_six, moebius_two, moebius_three]
  have h₆ : dualCoeff 6 6 = 1 := by
    norm_num [dualCoeff, moebius_six, moebius_two, moebius_three]
  rw [hset]
  norm_num [h₁, h₂, h₃, h₄, h₅, h₆, Finset.sum_insert]

/-- A missing mixed conductor forces a uniform squared-error floor. -/
theorem omitted_six_error_floor (f : ThresholdHilbert) (hf : mobiusDifferenceCLM 6 f = 0) :
    1 / 92 ≤ ‖hilbertOne - f‖ ^ 2 := by
  have he : mobiusDifferenceCLM 6 (hilbertOne - f) = 1 := by
    rw [map_sub, mobius_coordinate_one 6 (by decide), moebius_six, hf]
    norm_num
  have h := (mobiusDifferenceCLM 6).le_opNorm (hilbertOne - f)
  rw [he, norm_one] at h
  have hsq := pow_le_pow_left₀ zero_le_one h 2
  rw [one_pow, mul_pow, mobius_six_norm_sq] at hsq
  linarith

/-- All normalized atoms except the conductor six lie in the kernel of its
Möbius charge. This covers prime-only and prime-power-only dictionaries. -/
theorem omitted_six_span_error_floor (f : ThresholdHilbert)
    (hf : f ∈ Submodule.span ℝ (Set.range (fun d : {d : ℕ // 0 < d ∧ d ≠ 6} =>
      normalizedResidueHilbert d.val d.property.1))) :
    1 / 92 ≤ ‖hilbertOne - f‖ ^ 2 := by
  apply omitted_six_error_floor f
  have hker : Submodule.span ℝ (Set.range
      (fun d : {d : ℕ // 0 < d ∧ d ≠ 6} => normalizedResidueHilbert d.val d.property.1)) ≤
        LinearMap.ker (mobiusDifferenceCLM 6).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    change mobiusDifferenceCLM 6 (normalizedResidueHilbert d.val d.property.1) = 0
    rw [mobius_normalizedResidue 6 d.val (by decide) d.property.1, if_neg d.property.2.symm]
  exact hker hf

/-- The same Chebyshev scale is the total sparse Ramanujan mean source. -/
theorem lcm_sum_ramanujan_mean_eq_psi (M : ℕ) :
    (∑ q ∈ (Nat.lcmUpto M).divisors, paretoMean (ramanujanPacket q)) =
      Chebyshev.psi (M : ℝ) := by
  simp_rw [paretoMean_ramanujanPacket]
  rw [ArithmeticFunction.vonMangoldt_sum, Chebyshev.psi_eq_log_lcmUpto]

/-- The entire synthesized certificate has zero pairing with every legal atom.
Thus appending the zero tests to a legal Gram introduces zero mixed blocks. -/
theorem certificate_orthogonal_atom {ι : Type*} [Fintype ι] (N d : ℕ)
    (hd : 0 < d) (hdL : d ∣ N + 1) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0) :
    inner ℝ (certificateVector N z) (atomVector N d) = 0 := by
  obtain ⟨a, ha⟩ := exists_zero_normal N z hs hs1 hz
  rw [certificateVector,
    ← certificate_eq_projection ((trialSpace (N + 1)).zero_mem) z hs hs1 hz a ha,
    inner_synthesis_left]
  apply Finset.sum_eq_zero
  intro i _
  rw [zero_row_orthogonal_atom N d hd hdL z i (hs i.1) (hs1 i.1) (hz i.1), mul_zero]


/-- Subtracting the certified zero component leaves every legal normal
right-hand side identical in the weighted residue quotient. -/
theorem certificate_shift_preserves_atom_pairing {ι : Type*} [Fintype ι] (N d : ℕ)
    (hd : 0 < d) (hdL : d ∣ N + 1) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0)
    (x : EuclideanSpace ℝ (Fin N)) :
    inner ℝ (atomVector N d) (x - certificateVector N z) = inner ℝ (atomVector N d) x := by
  have h : inner ℝ (atomVector N d) (certificateVector N z) = 0 := by
    calc
      _ = inner ℝ (certificateVector N z) (atomVector N d) := real_inner_comm _ _
      _ = 0 := certificate_orthogonal_atom N d hd hdL z hs hs1 hz
  rw [inner_sub_right, h, sub_zero]

/-- The missing-conductor obstruction holds at each coordinate, with its
actual squared dual norm and without a squarefree premise. -/
theorem omitted_conductor_error (m : ℕ) (hm : 1 < m) (f : ThresholdHilbert)
    (hf : mobiusDifferenceCLM m f = 0) :
    (ArithmeticFunction.moebius m : ℝ) ^ 2 ≤
      ‖mobiusDifferenceCLM m‖ ^ 2 * ‖hilbertOne - f‖ ^ 2 := by
  have he : mobiusDifferenceCLM m (hilbertOne - f) = (ArithmeticFunction.moebius m : ℝ) := by
    rw [map_sub, mobius_coordinate_one m (by omega), hf, sub_zero]
  have h := (mobiusDifferenceCLM m).le_opNorm (hilbertOne - f)
  rw [he] at h
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using
    pow_le_pow_left₀ (norm_nonneg _) h 2

end RiemannResearch.RH.Pareto.ResidueMellin
