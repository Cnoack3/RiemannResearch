# Complete-Q arithmetic-screening diagnostics

25 October 2026. **Floating diagnostics only; no uniform estimate is proved.**

This companion to ArithmeticKernelScreening20261025.md preserves the reproduction
script and raw results. Copy the first code block into squarefree_kernel_screening.py.
The script uses NumPy and SciPy. All infinite physical sums use periodic
special-function formulas. Float64 cancellation and conditioning remain.

## Reproduction script

```python
#!/usr/bin/env python3
"""Floating diagnostics for complete-Q squarefree Schur energies.

Run e.g. OPENBLAS_NUM_THREADS=1 python schur_rigidity_diagnostic.py --stages 20 40 80 120
or add --output output.json to save results.  No Lean verification is performed.

All physical sums are complete infinite sums, reduced using each summand's
period.  They are evaluated in IEEE float64, NOT certified interval arithmetic.
In particular the Schur subtraction can lose significant digits.  A finite
set of tested stages/evaluation sites establishes no uniform bound.

For a=1,...,L and x=a+kL put
 S0(a,L) = psi1(a/L)/L^2
 S1(a,L) = S0(a,L) + (psi(a/L)-psi((a+1)/L))/L
 S2(a,L) = (psi1(a/L)+psi1((a+1)/L))/L^2
           + 2*(psi(a/L)-psi((a+1)/L))/L.
These sum respectively x^-2, [x^2(x+1)]^-1, [x^2(x+1)^2]^-1 over k>=0.
G,H,J are the complete matrices <g_d,g_e>, <g_d,Bg_e>, <Bg_d,Bg_e>.
For target moments c0=<1,g_d>, c1=<B1,g_d>,
 epsilon=1-c0^T G^-1 c0; rho=c1-H G^-1 c0;
 x_n=G^-1 (g_d(n)); b(n)=g(n)^T G^-1 rho;
 Lambda(n)=x_n^T (J-H G^-1 H) x_n.

The four-site vector z=e1-e2-e3+e4 has norm squared 30*zeta(2).
It annihilates every squarefree legal atom and the constant target.
Its exact removable energy is [k(1)/2-k(2)/3-k(3)/4+k(4)/5]^2/(30*zeta(2)).

For each nonsquarefree j<=cutoff, rows M_j encode the functional
 f(j)-f(j-1)-f(rad(j))+f(rad(j)-1).
These rows have independent leading coordinates j.  Their Riesz Gram matrix is
 C=zeta(2)*M*diag(1^2,...,cutoff^2)*M^T, and D=M*diag(1/(m+1))*K.
The exact removable finite-family energy is diag(D^T C^-1 D).
No finite physical truncation is used for G,H,J,epsilon,b,Lambda.  A finite
cutoff here selects a finite set of exact annihilator constraints only.
"""
import argparse
import json
import math
import time
import numpy as np
from scipy.special import digamma, polygamma

ZETA2 = math.pi**2 / 6

def squarefree(n):
    return all(n % (p*p) for p in range(2, math.isqrt(n)+1))

def radical(n):
    result = 1
    for p in range(2, n+1):
        if n % p == 0:
            result *= p
            while n % p == 0:
                n //= p
        if n == 1:
            break
    return result

def periodic_weights(period):
    a = np.arange(1, period+1, dtype=float)
    u, v = a/period, (a+1)/period
    s0 = polygamma(1, u)/period**2
    difference = (digamma(u)-digamma(v))/period
    return a, s0, s0+difference, s0+polygamma(1, v)/period**2+2*difference

def rigidity_rows(cutoff):
    rows = []
    for n in range(4, cutoff+1):
        r = radical(n)
        if r == n:
            continue
        row = np.zeros(cutoff)
        row[n-1] += 1
        row[n-2] -= 1
        row[r-1] -= 1
        row[r-2] += 1
        rows.append(row)
    return np.array(rows)

def stage_result(stage, extra_cutoffs=()):
    started = time.monotonic()
    ds = np.array([d for d in range(2, stage+2) if squarefree(d)])
    dim = len(ds)
    G, H, J = [np.empty((dim, dim)) for _ in range(3)]
    c0, c1 = np.empty(dim), np.empty(dim)
    for i, d in enumerate(ds):
        d = int(d)
        a, s0, s1, _ = periodic_weights(d)
        g = (a % d)/d
        c0[i], c1[i] = g @ s0/ZETA2, g @ s1/ZETA2
        for j, e in enumerate(ds[:i+1]):
            e = int(e)
            a, s0, s1, s2 = periodic_weights(math.lcm(d, e))
            g = ((a % d)/d)*((a % e)/e)
            for matrix, weight in [(G, s0), (H, s1), (J, s2)]:
                matrix[i,j] = matrix[j,i] = g @ weight/ZETA2
    coeff = np.linalg.solve(G, c0)
    epsilon = 1-c0 @ coeff
    rho = c1-H @ coeff
    values = (np.arange(1, stage+1)[:,None] % ds)/ds
    X = np.linalg.solve(G, values.T)
    b = values @ np.linalg.solve(G, rho)
    schur = J-H @ np.linalg.solve(G,H)
    energy = np.einsum('in,ij,jn->n', X, schur, X)
    product = epsilon*energy
    k4 = ((np.arange(1,5)[:,None] % ds)/ds) @ X
    defect4 = np.array([1/2,-1/3,-1/4,1/5]) @ k4
    removed4 = defect4**2/(30*ZETA2)
    four_product = epsilon*(energy-removed4)
    result = {
        'stage': stage, 'dimension': dim, 'epsilon': float(epsilon),
        'max_abs_b': float(np.max(np.abs(b))),
        'max_abs_b_site': int(np.argmax(np.abs(b))+1),
        'max_b_squared': float(np.max(b*b)),
        'max_error_times_kernel_energy': float(np.max(product)),
        'max_product_site': int(np.argmax(product)+1),
        'max_four_site_screened_product': float(np.max(four_product)),
        'four_site_screened_max_site': int(np.argmax(four_product)+1),
        'minimum_computed_schur_eigenvalue': float(np.linalg.eigvalsh(schur).min()),
        'gram_condition_number': float(np.linalg.cond(G)),
        'rigidity_cutoffs': []
    }
    for cutoff in sorted(set([stage, *extra_cutoffs])):
        M = rigidity_rows(cutoff)
        gram = ZETA2*(M*np.arange(1, cutoff+1)**2) @ M.T
        kernel = ((np.arange(1,cutoff+1)[:,None] % ds)/ds) @ X
        defects = (M/np.arange(2,cutoff+2)) @ kernel
        removed = np.einsum('in,in->n', defects, np.linalg.solve(gram, defects))
        sharp_product = epsilon*(energy-removed)
        j = int(np.argmax(sharp_product))
        result['rigidity_cutoffs'].append({
            'cutoff': cutoff, 'constraint_count': len(M),
            'max_screened_product': float(sharp_product[j]), 'max_site': j+1,
            'raw_product_at_max_site': float(product[j]),
            'removed_fraction_at_max_site': float(removed[j]/energy[j]),
            'minimum_screened_energy': float(np.min(energy-removed))
        })
    result['elapsed_seconds'] = time.monotonic()-started
    return result

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--stages', type=int, nargs='+', default=[20,40,80,120])
    parser.add_argument('--extra-cutoffs', type=int, nargs='*', default=[])
    parser.add_argument('--output')
    args = parser.parse_args()
    out = {'status':'floating diagnostic, not a certified theorem',
           'precision':'IEEE float64; exact infinite-period formulas evaluated numerically',
           'physical_tail_truncated':False,
           'wolfram_checks': {'four_site_squared_norm':'5 Pi^2 = 30 zeta(2)',
                              'partial_fraction_remainders':[0,0],
                              'four_site_on_B_g2':'1/8', 'mean_zero':0},
           'stages':[]}
    for stage in args.stages:
        out['stages'].append(stage_result(stage,args.extra_cutoffs))
        print(json.dumps(out['stages'][-1]),flush=True)
    if args.output:
        with open(args.output,'w') as stream:
            json.dump(out,stream,indent=2)

if __name__ == '__main__':
    main()
```

## Raw results

```json
{
  "status": "floating diagnostic, not a certified theorem",
  "precision": "IEEE float64; exact infinite-period formulas evaluated numerically",
  "physical_tail_truncated": false,
  "wolfram_checks": {
    "four_site_squared_norm": "5 Pi^2 = 30 zeta(2)",
    "partial_fraction_remainders": [
      0,
      0
    ],
    "four_site_on_B_g2": "1/8",
    "mean_zero": 0
  },
  "stages": [
    {
      "stage": 10,
      "dimension": 7,
      "epsilon": 0.014399791640788528,
      "max_abs_b": 0.00979857424691932,
      "max_abs_b_site": 5,
      "max_b_squared": 9.60120572723905e-05,
      "max_error_times_kernel_energy": 0.0011384984154078211,
      "max_product_site": 5,
      "max_four_site_screened_product": 0.0011370924417341453,
      "four_site_screened_max_site": 5,
      "minimum_computed_schur_eigenvalue": 6.117969078586903e-06,
      "gram_condition_number": 108.14827865472056,
      "rigidity_cutoffs": [
        {
          "cutoff": 10,
          "constraint_count": 3,
          "max_screened_product": 0.0011349185958563503,
          "max_site": 5,
          "raw_product_at_max_site": 0.0011384984154078211,
          "removed_fraction_at_max_site": 0.0031443342415092197,
          "minimum_screened_energy": 0.007959855447076917
        }
      ],
      "elapsed_seconds": 0.0024906649996410124
    },
    {
      "stage": 20,
      "dimension": 13,
      "epsilon": 0.010924074561315833,
      "max_abs_b": 0.009751819315512066,
      "max_abs_b_site": 5,
      "max_b_squared": 9.509797996239422e-05,
      "max_error_times_kernel_energy": 0.0011070063700996508,
      "max_product_site": 20,
      "max_four_site_screened_product": 0.0011068269078511458,
      "four_site_screened_max_site": 20,
      "minimum_computed_schur_eigenvalue": 8.044513464709851e-07,
      "gram_condition_number": 285.9843131628469,
      "rigidity_cutoffs": [
        {
          "cutoff": 20,
          "constraint_count": 7,
          "max_screened_product": 0.0009108670132816292,
          "max_site": 20,
          "raw_product_at_max_site": 0.0011070063700996508,
          "removed_fraction_at_max_site": 0.17717997124114604,
          "minimum_screened_energy": 0.006467686681747912
        }
      ],
      "elapsed_seconds": 0.00723543600179255
    },
    {
      "stage": 40,
      "dimension": 26,
      "epsilon": 0.008229809854195413,
      "max_abs_b": 0.018478846727966517,
      "max_abs_b_site": 39,
      "max_b_squared": 0.00034146777639567884,
      "max_error_times_kernel_energy": 0.0011948660488003222,
      "max_product_site": 39,
      "max_four_site_screened_product": 0.0011876822407846034,
      "four_site_screened_max_site": 39,
      "minimum_computed_schur_eigenvalue": 4.8919104507504445e-08,
      "gram_condition_number": 1974.175230803055,
      "rigidity_cutoffs": [
        {
          "cutoff": 40,
          "constraint_count": 14,
          "max_screened_product": 0.0009372085579937238,
          "max_site": 39,
          "raw_product_at_max_site": 0.0011948660488003222,
          "removed_fraction_at_max_site": 0.21563713444305613,
          "minimum_screened_energy": 0.005074845122551619
        }
      ],
      "elapsed_seconds": 0.072627116998774
    },
    {
      "stage": 80,
      "dimension": 49,
      "epsilon": 0.007295688535909561,
      "max_abs_b": 0.027030305428090994,
      "max_abs_b_site": 80,
      "max_b_squared": 0.0007306374115358855,
      "max_error_times_kernel_energy": 0.0023117167485315186,
      "max_product_site": 80,
      "max_four_site_screened_product": 0.0023113443789768294,
      "four_site_screened_max_site": 80,
      "minimum_computed_schur_eigenvalue": 3.297268992862255e-09,
      "gram_condition_number": 8996.368196600655,
      "rigidity_cutoffs": [
        {
          "cutoff": 80,
          "constraint_count": 30,
          "max_screened_product": 0.001867698366604532,
          "max_site": 80,
          "raw_product_at_max_site": 0.0023117167485315186,
          "removed_fraction_at_max_site": 0.19207300470918093,
          "minimum_screened_energy": 0.004451700686985766
        }
      ],
      "elapsed_seconds": 0.803361327998573
    },
    {
      "stage": 120,
      "dimension": 74,
      "epsilon": 0.006379360131061329,
      "max_abs_b": 0.03828736772343027,
      "max_abs_b_site": 95,
      "max_b_squared": 0.00146592252718917,
      "max_error_times_kernel_energy": 0.003063077710856543,
      "max_product_site": 95,
      "max_four_site_screened_product": 0.0030551569838730103,
      "four_site_screened_max_site": 95,
      "minimum_computed_schur_eigenvalue": 7.467373004755505e-10,
      "gram_condition_number": 20859.338662890503,
      "rigidity_cutoffs": [
        {
          "cutoff": 120,
          "constraint_count": 45,
          "max_screened_product": 0.002216748216554708,
          "max_site": 95,
          "raw_product_at_max_site": 0.003063077710856543,
          "removed_fraction_at_max_site": 0.2763003665568681,
          "minimum_screened_energy": 0.004052983293979156
        }
      ],
      "elapsed_seconds": 4.102420967996295
    },
    {
      "stage": 160,
      "dimension": 98,
      "epsilon": 0.006123771763566377,
      "max_abs_b": 0.03769123597477097,
      "max_abs_b_site": 95,
      "max_b_squared": 0.0014206292693058693,
      "max_error_times_kernel_energy": 0.0030038741223860437,
      "max_product_site": 95,
      "max_four_site_screened_product": 0.0029948238180863423,
      "four_site_screened_max_site": 95,
      "minimum_computed_schur_eigenvalue": 2.1178867224581157e-10,
      "gram_condition_number": 36444.85355824131,
      "rigidity_cutoffs": [
        {
          "cutoff": 160,
          "constraint_count": 62,
          "max_screened_product": 0.0021766893008431823,
          "max_site": 159,
          "raw_product_at_max_site": 0.002852552866797928,
          "removed_fraction_at_max_site": 0.2369328799551477,
          "minimum_screened_energy": 0.0038970387552107015
        }
      ],
      "elapsed_seconds": 12.154004253003222
    },
    {
      "stage": 240,
      "dimension": 149,
      "epsilon": 0.005353392610074614,
      "max_abs_b": 0.04890554123208909,
      "max_abs_b_site": 221,
      "max_b_squared": 0.0023917519632035656,
      "max_error_times_kernel_energy": 0.004530879463181003,
      "max_product_site": 221,
      "max_four_site_screened_product": 0.004505747923867651,
      "four_site_screened_max_site": 221,
      "minimum_computed_schur_eigenvalue": 4.272685055582809e-11,
      "gram_condition_number": 85420.15356141757,
      "rigidity_cutoffs": [
        {
          "cutoff": 240,
          "constraint_count": 91,
          "max_screened_product": 0.003491812657818958,
          "max_site": 221,
          "raw_product_at_max_site": 0.004530879463181003,
          "removed_fraction_at_max_site": 0.22933004812989344,
          "minimum_screened_energy": 0.0035498791589209412
        }
      ],
      "elapsed_seconds": 66.0632896130046
    }
  ],
  "cutoff_sweep": {
    "stage": 80,
    "dimension": 49,
    "epsilon": 0.007295688535909561,
    "max_abs_b": 0.027030305428090994,
    "max_abs_b_site": 80,
    "max_b_squared": 0.0007306374115358855,
    "max_error_times_kernel_energy": 0.0023117167485315186,
    "max_product_site": 80,
    "max_four_site_screened_product": 0.0023113443789768294,
    "four_site_screened_max_site": 80,
    "minimum_computed_schur_eigenvalue": 3.297268992862255e-09,
    "gram_condition_number": 8996.368196600655,
    "rigidity_cutoffs": [
      {
        "cutoff": 40,
        "constraint_count": 14,
        "max_screened_product": 0.0019764584713103683,
        "max_site": 80,
        "raw_product_at_max_site": 0.0023117167485315186,
        "removed_fraction_at_max_site": 0.14502567299134617,
        "minimum_screened_energy": 0.0045514582285668854
      },
      {
        "cutoff": 80,
        "constraint_count": 30,
        "max_screened_product": 0.001867698366604532,
        "max_site": 80,
        "raw_product_at_max_site": 0.0023117167485315186,
        "removed_fraction_at_max_site": 0.19207300470918093,
        "minimum_screened_energy": 0.004451700686985766
      },
      {
        "cutoff": 160,
        "constraint_count": 62,
        "max_screened_product": 0.0018290651107465852,
        "max_site": 80,
        "raw_product_at_max_site": 0.0023117167485315186,
        "removed_fraction_at_max_site": 0.2087849379001688,
        "minimum_screened_energy": 0.0044249098280897065
      },
      {
        "cutoff": 320,
        "constraint_count": 124,
        "max_screened_product": 0.001809832545966194,
        "max_site": 80,
        "raw_product_at_max_site": 0.0023117167485315186,
        "removed_fraction_at_max_site": 0.21710454054725284,
        "minimum_screened_energy": 0.004420384313523533
      },
      {
        "cutoff": 640,
        "constraint_count": 251,
        "max_screened_product": 0.0018010827688446336,
        "max_site": 80,
        "raw_product_at_max_site": 0.0023117167485315186,
        "removed_fraction_at_max_site": 0.2208895099329349,
        "minimum_screened_energy": 0.004416722163165926
      },
      {
        "cutoff": 1280,
        "constraint_count": 502,
        "max_screened_product": 0.001797710578895577,
        "max_site": 80,
        "raw_product_at_max_site": 0.0023117167485315186,
        "removed_fraction_at_max_site": 0.22234824831478855,
        "minimum_screened_energy": 0.004415791573967427
      }
    ],
    "elapsed_seconds": 0.8156565519966534
  }
}
```
