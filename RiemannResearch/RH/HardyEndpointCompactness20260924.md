# Hardy endpoint, damping, and compactness — 24 September 2026

## Outcome and verification boundary

The June 2026 paper proves convergence of its raw Möbius sums for half-plane boundary alpha > 1. The argument below includes alpha = 1, unconditionally. This extends that paper's stated range; no claim of historical novelty is made. Earlier work already treats closely related endpoint weights and weak compactness.

Two companion Lean modules establish narrower, precisely stated results:

- `CanonicalMobiusWeightedEndpoint.lean`: unconditional convergence of the project's boundary-corrected Möbius residual with weight 1/[n²(n+1)]. The proof uses the existing formal prime number theorem, exact finite heads, and sublinear full energy.
- `DampedDiagonalCompactness.lean`: a finite-coordinate diagonal criterion for membership in a closed legal subspace, with an explicit uniform bound in one fixed Hilbert norm.

Both snippets compiled and their main declarations report only `propext`, `Classical.choice`, and `Quot.sound`. The raw Hardy-space endpoint proof below, including Mellin–Plancherel and Ramaré's quantitative estimate, is an analytic proof, not a completed Lean formalization. There is no unconditional RH proof.

## Parameters and the raw endpoint theorem

Write C_alpha = {s : Re(s) > alpha},

\[
E(s)=1/s,\qquad G_k(s)=(k^{-s}-k^{-1})\zeta(s)/s,
\qquad S_N=\sum_{k=2}^N\mu(k)G_k.
\]

The Hardy norm uses (2 pi)^(-1) times the vertical-line integral. The paper's alpha is the half-plane boundary. Its RH endpoint is alpha = 1/2. Thus an offset tending to zero means epsilon = alpha - 1/2, not alpha itself tending to zero.

Set m_N = sum_{k<=N} mu(k)/k and M(n) = sum_{k<=n} mu(k). Define

\[
r_N(n)=1-\sum_{k=1}^N\mu(k)\lfloor n/k\rfloor+n m_N,
\qquad R_N(x)=r_N(\lfloor x\rfloor).
\]

The bounded step function h_k(x) = floor(x/k) - floor(x)/k has Mellin transform G_k. Compute the transform first for Re(s)>1, then continue analytically using boundedness. With x=exp(t), ordinary Laplace/Fourier Plancherel gives, for alpha>0,

\[
\|E-S_N\|_\alpha^2
=\int_1^\infty R_N(x)^2x^{-2\alpha-1}\,dx
=\frac1{2\alpha}\sum_{n\ge1}r_N(n)^2
\bigl(n^{-2\alpha}-(n+1)^{-2\alpha}\bigr).
\tag{1}
\]

These finite combinations belong to the indicated Hardy spaces because their inverse Mellin step functions are bounded. Taking the supremum over vertical lines gives exactly the boundary integral by monotone convergence.

For 1<=n<=N, Möbius divisor cancellation gives r_N(n)=n m_N. Therefore the contribution from 1<=x<N is at most m_N² log N when alpha=1. The unconditional bound

\[
|m_N|\le 2.4/\log N\qquad(N>1)
\tag{2}
\]

is the q=1 case of Ramaré's published estimate. The head tends to zero.

For the tail, two exact identities supply everything needed:

\[
|r_N(n)|\le N,
\qquad
r_N(n)=n m_N+
\sum_{j=1}^{\lfloor n/N\rfloor}
\left[M(\lfloor n/j\rfloor)-M(N)\right].
\tag{3}
\]

The bound follows from h_k(n)=-(n mod k)/k and h_1=0. The second identity follows by summing the omitted divisors k>N in the full Möbius floor identity. The upper limit can alternatively be floor(n/(N+1)); the extra terms in (3) vanish.

The exact Abel identity

\[
M(N)=N m_N-\sum_{k=1}^{N-1}m_k
\]

and m_N->0 imply M(N)/N->0 by Cesàro convergence. For fixed u>=1, put n=floor(Nu) in (3). Its number of summands is floor(u), independent of N; every normalized summand tends to zero. Hence R_N(Nu)/N->0. Now

\[
\int_N^\infty R_N(x)^2x^{-3}\,dx
=\int_1^\infty\left|R_N(Nu)/N\right|^2u^{-3}\,du\longrightarrow0.
\]

Dominated convergence applies with majorant u^(-3). Together with the head estimate this proves

\[
\boxed{S_N\longrightarrow E\text{ in }H^2(C_1).}
\tag{4}
\]

The argument also proves convergence for every alpha>=1 by norm monotonicity. It does not prove convergence at any fixed alpha<1.

## The modification verified in Lean

The project's canonical corrected family is

\[
\widetilde S_N=S_N-(N+1)m_NG_{N+1}.
\tag{5}
\]

Its step-function coordinates are

\[
F_N(n)=\sum_{k\le N}\mu(k)\lfloor n/k\rfloor
-(N+1)m_N\lfloor n/(N+1)\rfloor.
\]

In particular F_N(n)=1 for 1<=n<=N. In the project's critical Pareto norm, with weight 1/[n(n+1)], the existing PNT provider proves ||F_N||²/N->0. The new module derives ||1-F_N||²/N->0, then proves

\[
\boxed{\sum_{n\ge1}\frac{|1-F_N(n)|^2}{n^2(n+1)}\longrightarrow0.}
\tag{6}
\]

The general checked inequality is energy_with_extra_inverse_coordinate(x)<=||x||²/N whenever x(n)=0 for n<N and N>0. This is an unconditional theorem about the actual project family, not an assumed cancellation hypothesis.

The exact alpha=1 Mellin cell weight divided by the weight in (6) is

\[
\frac{\tfrac12(n^{-2}-(n+1)^{-2})}{1/[n^2(n+1)]}
=1-\frac1{2(n+1)}\in[3/4,1).
\]

Thus (6) analytically implies Hardy endpoint convergence for (5). This identification has not been formalized in the new module. One can also recover (4) from (5): splitting at x=k gives

\[
\|G_k\|_1^2\le\frac{\log k+1/2}{k^2},
\quad
\|(N+1)m_NG_{N+1}\|_1^2
\le m_N^2(\log(N+1)+1/2)\to0
\]

by (2).

## What compactness can accomplish

In a fixed Hilbert space H²(C_(1/2)), suppose legal finite sums f_j have uniformly bounded norms and converge to E on a uniqueness set in Re(s)>1. Reflexivity gives weakly convergent subsequences; bounded point evaluations and analytic uniqueness identify any weak limit with E. The closed legal subspace is weakly closed, so it contains E. Mazur's lemma supplies strongly convergent legal convex combinations.

The new Lean diagonal theorem packages this in the project's sequence Hilbert space. For each j, it asks for one legal f(alpha,N) with

\[
0<\alpha\le1/(j+1),\quad N\ge j,\quad\|f(\alpha,N)\|\le C,
\quad |f(\alpha,N)(k)-x(k)|\le1/(j+1)\quad(1\le k\le j).
\]

It then proves x belongs to the closed legal subspace. Here alpha is a damping parameter. **Open:** provide this uniformly bounded family for the actual RH target. The checked theorem retains that premise in its type.

There is also an analytic moving-domain criterion: if alpha_j->1/2 from above, f_j are legal finite sums, f_j->E on an open subset of Re(s)>1, and

\[
\sup_j\|f_j\|_{H^2(C_{\alpha_j})}<\infty,
\tag{7}
\]

then RH follows. Indeed |f_j(s)|<=C/sqrt(2(Re(s)-alpha_j)) gives local boundedness throughout Re(s)>1/2. Montel and the identity theorem identify the local limit with E. An off-line zeta zero would make every f_j vanish there, contradicting E(s)=1/s. This moving-domain argument is analytic, not part of the new Lean module.

Cantor diagonal selection does not create (7). Nor does a uniform bound on canonical orthogonal projections identify their limit with E: that limit is the projection of E onto the closed legal span, whose equality with E remains to be proved.

## Damping toward zero and the exact obstruction

A natural legal modification is

\[
F_{N,\varepsilon}(s)=\sum_{k=2}^N\mu(k)k^{-\varepsilon}G_k(s).
\]

For Re(s)>1 and epsilon>0 its limit is

\[
F_\varepsilon(s)=\frac{\zeta(s)}s
\left(\frac1{\zeta(s+\varepsilon)}-
\frac1{\zeta(1+\varepsilon)}\right).
\tag{8}
\]

This tends pointwise to E as epsilon decreases to zero. What is missing is uniform control in the critical Hardy norm while keeping legal approximants. Formula (8) does not automatically define a Hardy function on the entire critical half-plane: shifted zeros can introduce poles. Báez-Duarte already studied such damping and conditional schedules; its small-damping convergence cannot be imported as an unconditional theorem.

The raw endpoint proof displays the missing rate exactly:

\[
\int_N^\infty R_N(x)^2x^{-2\alpha-1}\,dx
=N^{2-2\alpha}\int_1^\infty
|R_N(Nu)/N|^2u^{-2\alpha-1}\,du.
\tag{9}
\]

For alpha=1, dominated convergence suffices. For fixed alpha<1, the growing prefactor requires additional arithmetic cancellation. Even alpha_N=1-c/log N works by the same argument (fixed c>0, prefactor exp(2c)); those boundaries tend to 1, not to 1/2.

For abstract exact-head residuals, the known energy estimate E_N=o(N) permits one extra inverse-coordinate weight. It does not imply convergence with arbitrary weights n^(-beta), beta>0, or along beta_N->0. A residual with energy N/log N concentrated at n=N+1 is an explicit counterexample: its beta_N-damped energy diverges for every beta_N->0. Removing damping also requires attention to the legal subspace; multiplying coordinates by a damping weight generally changes the generators.

## External computation

Wolfram verified the missing-divisor identity in 720 exact rational cases (1<=N<=12, 1<=n<=60), and symbolically evaluated the two finite-head energies:

\[
\sum_{n=1}^N n^2\,\frac{n^{-2}-(n+1)^{-2}}2
=H_{N+1}-\frac{1+H^{(2)}_{N+1}}2,
\]

\[
\sum_{n=1}^N n^2\left(n^{-1}-(n+1)^{-1}\right)
=N+1-H_{N+1}.
\]

Multiplying these by m_N² gives the raw head at alpha=1 and alpha=1/2 respectively. The second requires a much stronger rate. Finite exact checks support implementation reliability; they do not prove an infinite limit.

The reproducible Python code included below evaluates (1) by an integer divisor sieve, avoiding numerical integration of zeta. It reports floating-point partial energies and the separate analytic tail bound N²/(2M²), with M=100N. Floating-point output is not an interval certificate.

| N | Squared energy summed below M=100N | Analytic bound on omitted tail |
|---:|---:|---:|
| 32 | 0.0117202806759 | 0.00005 |
| 128 | 0.000151984000428 | 0.00005 |
| 512 | 0.000152134695545 | 0.00005 |
| 2048 | 0.000137993864675 | 0.00005 |
| 4096 | 0.000133990132343 | 0.00005 |

The finite data are not monotone and do not establish an asymptotic convergence rate. The script independently passed the same 720 exact-fraction identity checks.

## Primary references and provenance

1. Manzur, Noor, Quintero, *A Hardy space approximation supporting zero-free half-planes for the zeta-function*, June 2026, [arXiv:2606.16097](https://arxiv.org/html/2606.16097v1), Theorem 3.1 and Proposition 3.1: baseline range and legal-span zero-free implication.
2. Gallardo-Gutiérrez and Seco, *Zero-free regions of the Riemann zeta function and approximation in weighted Dirichlet spaces*, [arXiv:2206.02654](https://arxiv.org/pdf/2206.02654), Section 2.1 and Proposition 3.4: prior weak-compactness/Mazur strategy and truncated-divisor identity.
3. Olivier Ramaré, *Explicit estimates on the summatory functions of the Möbius function with coprimality restrictions*, Acta Arithmetica 165 (2014), 1–10, [DOI:10.4064/aa165-1-1](https://doi.org/10.4064/aa165-1-1): quantitative estimate (2).
4. Luis Báez-Duarte, *A strengthening of the Nyman–Beurling criterion for the Riemann Hypothesis, 2*, [arXiv:math/0205003](https://arxiv.org/html/math/0205003v1), Corollary 3.1 and Proposition 3.1: damping, its RH-dependent convergence, and a conditional parameter schedule.

The endpoint assembly and Lean adaptations were developed during this research continuation. The exact-head corrected family comes from the existing manuscript-backed project modules. No claim that these elementary consequences are previously unknown is intended.

## Reproduce the finite experiment

Save the following as `hardy_endpoint_experiment.py` and run it with Python 3. It uses only the standard library and writes JSON and CSV beside the script.

```python
#!/usr/bin/env python3
"""Exploratory raw Mobius residual norms at alpha=1.

The normalization is ||F||^2 = (1/(2*pi))*integral_{R}|F(1+it)|^2 dt.
For the supplied Mellin/step residual model this equals
    sum_{n>=1} r_N(n)^2 * (n^(-2) - (n+1)^(-2))/2,
where r_N(n)=1-sum_{k<=N}mu(k)*floor(n/k)+n*m_N,
and m_N=sum_{k<=N}mu(k)/k.

The divisor sieve and cumulative floor sums use exact Python integers.
m_N, residual evaluation, weights, and energies use floating-point arithmetic;
math.fsum improves summation but does not certify rounding. Consequently the
reported truncated energies and their sums with the tail bound are exploratory,
not interval enclosures. The mathematical omitted-tail bound is exact:
|r_N(n)|<=N and sum_{n>=M}weight(n)=1/(2*M^2), so tail<=N^2/(2*M^2).
No zeta evaluations or quadrature are used. Standard library only.
"""

from array import array
import csv
from fractions import Fraction
import json
import math
from pathlib import Path
import time


def mobius_sieve(limit):
    """Linear sieve for exact integer mu(0),...,mu(limit)."""
    mu = [0] * (limit + 1)
    mu[1] = 1
    composite = bytearray(limit + 1)
    primes = []
    for n in range(2, limit + 1):
        if not composite[n]:
            primes.append(n)
            mu[n] = -1
        for p in primes:
            v = n * p
            if v > limit:
                break
            composite[v] = 1
            if n % p == 0:
                mu[v] = 0
                break
            mu[v] = -mu[n]
    return mu


def verify_small_exact_identities():
    """Check supplied missing-divisor identity with exact fractions."""
    mu = mobius_sieve(60)
    mertens = [0] * 61
    for n in range(1, 61):
        mertens[n] = mertens[n - 1] + mu[n]
    checks = 0
    for n_cutoff in range(1, 13):
        m_exact = sum((Fraction(mu[k], k) for k in range(1, n_cutoff + 1)), Fraction(0))
        for n in range(1, 61):
            floor_sum = sum(mu[k] * (n // k) for k in range(1, n_cutoff + 1))
            raw = Fraction(1 - floor_sum) + n * m_exact
            missing = sum(mertens[n // j] - mertens[n_cutoff]
                          for j in range(1, n // (n_cutoff + 1) + 1))
            assert raw == n * m_exact + missing, (n_cutoff, n, raw, missing)
            modulo = 1 + sum((Fraction(mu[k] * (n % k), k)
                              for k in range(1, n_cutoff + 1)), Fraction(0))
            assert raw == modulo
            assert abs(raw) <= n_cutoff
            checks += 1
    return {"N_range": [1, 12], "n_range": [1, 60],
            "cases": checks, "missing_divisor_identity": "passed exact Fraction equality",
            "modulo_identity_and_bound": "passed exact Fraction equality and inequality"}


def compute_row(n_cutoff, mu, tail_factor=100):
    cutoff = tail_factor * n_cutoff
    # d[n]=sum_{k<=N,k|n}mu(k), so prefix d is sum mu(k)*floor(n/k).
    divisor_sums = array('q', [0]) * cutoff
    for k in range(1, n_cutoff + 1):
        muk = mu[k]
        if muk:
            for n in range(k, cutoff, k):
                divisor_sums[n] += muk
    m_n = math.fsum(mu[k] / k for k in range(1, n_cutoff + 1))
    max_abs_residual = 0.0
    floor_sum = 0
    terms = []
    for n in range(1, cutoff):
        floor_sum += divisor_sums[n]
        residual = (1 - floor_sum) + n * m_n
        max_abs_residual = max(max_abs_residual, abs(residual))
        # Algebraically identical to (1/n^2-1/(n+1)^2)/2,
        # without subtracting nearby floating-point reciprocals.
        weight = (2 * n + 1) / (2 * n * n * (n + 1) * (n + 1))
        terms.append(residual * residual * weight)
    energy = math.fsum(terms)
    tail_bound = Fraction(n_cutoff * n_cutoff, 2 * cutoff * cutoff)
    return {"N": n_cutoff, "M": cutoff, "alpha": 1,
            "last_included_n": cutoff - 1,
            "m_N_exploratory": m_n,
            "truncated_squared_energy_exploratory": energy,
            "analytic_tail_bound_exact": str(tail_bound),
            "analytic_tail_bound_decimal": float(tail_bound),
            "energy_plus_tail_bound_exploratory_not_certificate": energy + float(tail_bound),
            "max_abs_residual_exploratory": max_abs_residual}


def main():
    started = time.perf_counter()
    ns = [32, 128, 512, 2048, 4096]
    checks = verify_small_exact_identities()
    mu = mobius_sieve(max(ns))
    rows = [compute_row(n, mu) for n in ns]
    payload = {
        "experiment": "Raw Mobius residual norm at alpha=1",
        "normalization": "H^2 squared norm uses (1/(2*pi))*integral over vertical line",
        "arithmetic": "Mobius sieve and divisor/floor sums exact integers; all norm values exploratory float",
        "truncation": "n=1,...,M-1 with M=100*N; omitted-tail bound N^2/(2*M^2)=1/20000 exactly",
        "rounding": "No floating-point interval certificate; math.fsum does not certify rounding",
        "exact_checks": checks,
        "rows": rows,
        "elapsed_seconds": time.perf_counter() - started,
    }
    outdir = Path(__file__).resolve().parent
    json_path = outdir / "hardy_endpoint_experiment.json"
    csv_path = outdir / "hardy_endpoint_experiment.csv"
    json_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print("Exploratory squared energies; exact analytic tail bound 1/20000; no rounding certificate.")
    print(f"{'N':>6} {'M':>8} {'m_N':>16} {'truncated energy':>19} {'tail bound':>12}")
    for row in rows:
        print(f"{row['N']:6d} {row['M']:8d} {row['m_N_exploratory']:16.10g} "
              f"{row['truncated_squared_energy_exploratory']:19.12g} "
              f"{row['analytic_tail_bound_decimal']:12.6g}")
    print(f"Exact Fraction identity checks: {checks['cases']} passed.")
    print(f"Elapsed: {payload['elapsed_seconds']:.3f}s")
    print(json_path)
    print(csv_path)


if __name__ == '__main__':
    main()
```
