# Exact rational tail certificates: reproduction source

Save the Python block beside this note as `exact_head_moment_tail_certificates.py`.
Its optional `--certificates`, `--output-dir` and `--emit-lean` arguments override
the default paths. All bounds use exact fractions and outward rounding.
The separate Lean modules establish the kernel-checked results.

```python
#!/usr/bin/env python3
"""Recompute complete rational tail bounds and emit the cutoff-seven Lean witness.

The input coefficients propose corrections only. Every output budget is
recomputed from integer counts, exact Fractions and the proved elementary
Pareto progression upper bound. No floating-point value is a premise.
"""
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import argparse
import json


def moebius(n):
    sign, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def stage_record(st):
    x, P = st['cutoff'], st['period']
    W = sum(F(moebius(d)**2, d) for d in range(1, x+1))
    V = sum(F(moebius(d)**2, x) for d in range(1, x+1))
    U = sum(F(d*moebius(d)**2, x*x) for d in range(1, x+1))
    m = sum(F(moebius(d), d) for d in range(1, x+1))
    z = F(sum(moebius(d) for d in range(1, x+1)), x)
    det = W*U-V*V
    assert det > 0
    a0, a1 = (U*m-V*z)/det, (W*z-V*m)/det
    coeff = {d: round(F(c)*10**6) for d, c in
             zip(st['proper_upper_divisors'], st['upper_span_coefficients'])}
    assert all(d > x and d < P and P % d == 0 for d in coeff)
    jumps = [(d, moebius(d)**2*(a0+a1*F(d, x))) for d in range(1, x+1)]
    residual, psi, H, total = F(1, 2), F(0), F(0), 0
    scale = 10**10
    data, budget = {0: F(1, 2)}, {}
    for r in range(1, P):
        inc = sum(j for d, j in jumps if r % d == 0)
        psi += inc
        g = gcd(r, P)
        residual += inc-F(g == 1, 2)-F(coeff.get(g, 0), 10**6)
        data[r] = residual
        if r <= x:
            assert residual == psi
            H += psi**2/F(r*(r+1))
        else:
            t = r+P
            hi = F(1, r*(r+1))+F(1, t*(t+1))+F(1, P*(t+1))
            term = hi*residual**2*scale
            budget[r] = -(-term.numerator // term.denominator)
            assert F(budget[r], scale) >= hi*residual**2
            total += budget[r]
    upper = F(total, scale)
    assert upper <= F(1, 30)
    record = dict(cutoff=x, period=P, alpha='1/2', prefix_terms=1,
                  observer_a0=str(a0), observer_a1=str(a1),
                  correction_denominator=10**6,
                  correction_numerators={str(d): c for d, c in coeff.items()},
                  per_residue_upper_grid_denominator=scale,
                  tail_energy_upper=str(upper),
                  tail_energy_upper_decimal=float(upper),
                  unperiodized_head_energy=str(H),
                  candidate_M='1/30', passes_candidate=True,
                  status='external_exact_rational; see Lean modules for kernel replay')
    return record, coeff, data, budget


def emit_point_checks():
    return '''set_option maxHeartbeats 50000000 in
-- Exact integer cross-multiplication checks all 202 outward-rounded bounds.
set_option maxRecDepth 100000 in
private theorem integer_checks : ∀ r : Fin 210, 8 ≤ r.val →
    (10000000000 : ℤ) * numData r.val ^ 2 *
      (210 * ((r.val : ℤ) + 210) * ((r.val : ℤ) + 211) +
       210 * (r.val : ℤ) * ((r.val : ℤ) + 1) +
       (r.val : ℤ) * ((r.val : ℤ) + 1) * ((r.val : ℤ) + 210)) ≤
    (budget r.val : ℤ) * 354000000 ^ 2 * 210 *
      (r.val : ℤ) * ((r.val : ℤ) + 1) * ((r.val : ℤ) + 210) *
      ((r.val : ℤ) + 211) := by decide

private theorem point_checks : ∀ r : Fin 210, 8 ≤ r.val →
    (elementaryProgressionInterval 210 r.val 1).hi * data r.val ^ 2 ≤
      (budget r.val : ℚ) / 10000000000 := by
  intro r hr
  have hrp : (0 : ℚ) < r.val := by
    exact_mod_cast (show 0 < r.val by omega)
  have h0 : (r.val : ℚ) ≠ 0 := hrp.ne'
  have h1 : (r.val : ℚ) + 1 ≠ 0 := by positivity
  have h210 : (r.val : ℚ) + 210 ≠ 0 := by positivity
  have h211 : (r.val : ℚ) + 211 ≠ 0 := by positivity
  let D : ℚ := 354000000 ^ 2 * 210 * (r.val : ℚ) * ((r.val : ℚ) + 1) *
    ((r.val : ℚ) + 210) * ((r.val : ℚ) + 211)
  have hD : 0 < D := by dsimp [D]; positivity
  have hc := integer_checks r hr
  have hq : (10000000000 : ℚ) * (numData r.val : ℚ) ^ 2 *
      (210 * ((r.val : ℚ) + 210) * ((r.val : ℚ) + 211) +
       210 * (r.val : ℚ) * ((r.val : ℚ) + 1) +
       (r.val : ℚ) * ((r.val : ℚ) + 1) * ((r.val : ℚ) + 210)) ≤
    (budget r.val : ℚ) * 354000000 ^ 2 * 210 *
      (r.val : ℚ) * ((r.val : ℚ) + 1) * ((r.val : ℚ) + 210) *
      ((r.val : ℚ) + 211) := by exact_mod_cast hc
  have he : (elementaryProgressionInterval 210 r.val 1).hi * data r.val ^ 2 =
      ((numData r.val : ℚ) ^ 2 *
        (210 * ((r.val : ℚ) + 210) * ((r.val : ℚ) + 211) +
         210 * (r.val : ℚ) * ((r.val : ℚ) + 1) +
         (r.val : ℚ) * ((r.val : ℚ) + 1) * ((r.val : ℚ) + 210))) / D := by
    norm_num [elementaryProgressionInterval, data, D, Finset.sum_range_succ]
    field_simp [h0, h1, h210, h211]
    <;> ring
  rw [he]
  apply (div_le_div_iff₀ hD (by norm_num : (0 : ℚ) < 10000000000)).mpr
  simpa only [D, mul_assoc, mul_comm, mul_left_comm] using hq

'''


def emit_seven(coeff, data, budget):
    D = 354000000
    assert all((v*D).denominator == 1 for v in data.values())
    cases = lambda values: '\n'.join(f'  | {r} => {v}' for r, v in values.items())+'\n  | _ => 0'
    head = '''import RiemannResearch.RH.ExactHeadMomentTail
import RiemannResearch.RH.ParetoFiniteCertificates
import RiemannResearch.RH.ParetoRationalWeightIntervals
import Mathlib.Tactic

/-!
# A kernel certificate for the cutoff-seven centered tail

The nine correction coefficients are six-decimal rational roundings of the
retained external witness. All 202 tail residues and their complete infinite
Pareto progression weights are checked. The upper endpoints are rounded
outward on a 10^(-10) grid, independently at every residue.
Source: ResearchData/ExactHeadGreen20261116/moment_probe_certificates.json;
reproduction: ResearchData/ExactHeadGreen20261116/moment_tail_reproduction.md.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomStageSevenMoment
open RiemannResearch
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.RH.MobiusAffineProfile
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.NumberTheory.DivisorIncidence
open ExactHeadAtomOptimizer MobiusHeadGreen

theorem probe_formula (r : ℕ) : fittedMomentProbe 7 r =
    (125 * (r : ℝ) + 44 * (r / 2 : ℕ) - 37 * (r / 3 : ℕ) -
      199 * (r / 5 : ℕ) - 280 * (r / 6 : ℕ) - 361 * (r / 7 : ℕ)) / 354 := by
  have h4 : ArithmeticFunction.moebius 4 = 0 := by decide
  have h6 : ArithmeticFunction.moebius 6 = 1 := moebius_six
  norm_num [fittedMomentProbe, affineMomentDual, mass, energy, weight,
    sum_Icc_one, Finset.sum_range_succ, grid,
    ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three,
    ArithmeticFunction.moebius_apply_prime (show Nat.Prime 5 by norm_num),
    ArithmeticFunction.moebius_apply_prime (show Nat.Prime 7 by norm_num), h4, h6]
  ring

private def divisors : Finset ℕ := {10,14,15,21,30,35,42,70,105}
private def coeff : ℕ → ℤ
'''+cases(coeff)+'''

def probeCorrection (r : ℕ) : ℝ :=
  ∑ d ∈ divisors, ((coeff d : ℝ) / 1000000) * atom 210 d r

theorem probeCorrection_mem : probeCorrection ∈ upperSpan 210 7 (atom 210) := by
  have hd : divisors ⊆ upperDivisors 210 7 := by decide
  have he : probeCorrection = ∑ d ∈ divisors, ((coeff d : ℝ) / 1000000) • atom 210 d := by
    funext r
    simp [probeCorrection]
  rw [he]
  apply Submodule.sum_mem
  intro d hD
  exact (upperSpan 210 7 (atom 210)).smul_mem _
    (Submodule.subset_span ⟨d, hd hD, rfl⟩)

def centeredProbe (r : ℕ) : ℝ :=
  fittedMomentProbe 7 r - (1 / 2) * target 210 r - probeCorrection r

private def count (d r : ℕ) : ℕ :=
  ((Finset.Icc 1 r).filter (fun n => Nat.gcd n 210 = d)).card

private theorem atom_eq_count (d r : ℕ) : atom 210 d r = (count d r : ℝ) := by
  simp [atom, count]

private def numerator (r : ℕ) : ℤ :=
  1000000 * (125 * (r : ℤ) + 44 * (r / 2 : ℕ) - 37 * (r / 3 : ℕ) -
    199 * (r / 5 : ℕ) - 280 * (r / 6 : ℕ) - 361 * (r / 7 : ℕ)) -
  177000000 * ((count 1 r : ℤ) - 1) -
  354 * ∑ d ∈ divisors, coeff d * (count d r : ℤ)

private def numData : ℕ → ℤ
'''+cases({r: int(v*D) for r,v in data.items()})+'''

set_option maxHeartbeats 50000000 in
-- Kernel reduction checks all 210 finite gcd-count identities.
set_option maxRecDepth 100000 in
private theorem data_check : ∀ r : Fin 210, numerator r.val = numData r.val := by decide

private theorem residual_data (r : ℕ) (hr : r < 210) :
    centeredProbe r = (numData r : ℝ) / 354000000 := by
  have hn := data_check ⟨r, hr⟩
  change numerator r = numData r at hn
  rw [← hn]
  simp only [centeredProbe, probe_formula, probeCorrection, target, atom_eq_count, numerator]
  generalize r / 2 = r2
  generalize r / 3 = r3
  generalize r / 5 = r5
  generalize r / 6 = r6
  generalize r / 7 = r7
  push_cast
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  ring

private def data (r : ℕ) : ℚ := (numData r : ℚ) / 354000000

private theorem data_cast (r : ℕ) (hr : r < 210) : (data r : ℝ) = centeredProbe r := by
  rw [residual_data r hr]
  simp [data]

private def budget : ℕ → ℕ
'''+cases(budget)+'''

'''+emit_point_checks()+'''

set_option maxHeartbeats 50000000 in
-- This is a finite sum of the outward-rounded integer budgets.
set_option maxRecDepth 100000 in
private theorem budget_sum :
    (∑ r ∈ Finset.Icc 8 209, budget r) = 324629179 := by decide

/-- Every infinite progression tail is included in this finite rational certificate. -/
theorem centered_tail_seven_le :
    centeredMomentTailEnergy 7 (1 / 2) probeCorrection ≤ (1 / 30 : ℝ) := by
  have hP : greenPeriod 7 = 210 := by decide
  simp only [centeredMomentTailEnergy, primorial_tail_residues, hP]
  change energy (Finset.Icc 8 209) (progressionWeight 210) centeredProbe ≤ (1 / 30 : ℝ)
  calc
    _ ≤ ∑ r ∈ Finset.Icc 8 209, (budget r : ℝ) / 10000000000 := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨hr8, hr209⟩ := Finset.mem_Icc.mp hr
      have hr210 : r < 210 := by omega
      have hw := (elementaryProgressionInterval_contains 210 r 1 (by norm_num) (by omega)).2
      have hc := point_checks ⟨r, hr210⟩ hr8
      have hb : ((elementaryProgressionInterval 210 r 1).hi : ℝ) * (data r : ℝ) ^ 2 ≤
          (budget r : ℝ) / 10000000000 := by
        have hh := (Rat.cast_le (K := ℝ)).2 hc
        push_cast at hh
        exact hh
      rw [data_cast r hr210] at hb
      exact (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans hb
    _ ≤ _ := by
      have hb : (∑ r ∈ Finset.Icc 8 209, (budget r : ℝ)) = 324629179 := by
        exact_mod_cast budget_sum
      rw [← Finset.sum_div, hb]
      norm_num

theorem fitted_moment_seven_tail_deficit :
    atomFittedMoment (greenPeriod 7) 7 ≤
      (3 / 4) * atomEnergy (greenPeriod 7) 7 + 1 / 30 := by
  have hP : greenPeriod 7 = 210 := by decide
  have hv : probeCorrection ∈ upperSpan (greenPeriod 7) 7 (atom (greenPeriod 7)) := by
    simpa only [hP] using probeCorrection_mem
  have h := fitted_moment_deficit_of_tail_probe_bound 7 (1 / 2) (1 / 30) (1 / 4)
    (by norm_num) (by norm_num) probeCorrection hv centered_tail_seven_le
  norm_num at h ⊢
  exact h

end RiemannResearch.RH.Pareto.ExactHeadAtomStageSevenMoment
'''
    return head


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parents[3]
    parser.add_argument('--certificates', type=Path, default=root/'RiemannResearch/ResearchData/ExactHeadGreen20261116/moment_probe_certificates.json')
    parser.add_argument('--output-dir', type=Path, default=root/'RiemannResearch/ResearchData/ExactHeadGreen20261116')
    parser.add_argument('--emit-lean', type=Path)
    args = parser.parse_args()
    result = {'method': 'complete rational progression upper bounds, K=1, six-decimal rational correction, outward rounding of each energy summand', 'uniform_status': 'finite stages only; no cofinal bound', 'stages': []}
    for st in json.loads(args.certificates.read_text())['stages']:
        record, coeff, data, budget = stage_record(st)
        result['stages'].append(record)
        if st['cutoff'] == 7 and args.emit_lean:
            args.emit_lean.write_text(emit_seven(coeff, data, budget))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir/'moment_tail_certificates.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps([{k:r[k] for k in ('cutoff','tail_energy_upper','passes_candidate')} for r in result['stages']], indent=2))


if __name__ == '__main__':
    main()
```
