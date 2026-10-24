# Certified finite squarefree exact-head candidates

Date: 24 October 2026.

These experiments follow the constructive approximants handoff, sections 5, 8,
and 10. They provide exact rational candidate certificates in the complete
Pareto norm. They do **not** certify global optimality, a uniform-in-head bound,
capacity saturation, or RH.

Use

\[
P(n)=\frac1{n(n+1)},\quad g_d(n)=\frac{n\bmod d}{d},\quad
D=\{2,3,5,6,7,10,11,13,14\}.
\]

All conductors in this dictionary are squarefree. For every head length
\(M=1,\ldots,6\), two candidates \(F_M=\sum_{d\in D}c_{M,d}g_d\)
were produced: one numerically proposed to minimize the complete norm and one
numerically proposed to minimize the complete residual norm. Their coefficients
were rounded to rationals in the free coordinates, and the pivot coordinates
were then solved **exactly** so that \(F_M(n)=1\) for \(1\le n\le M\).
Every head identity was checked using Python's exact rational arithmetic.

## The already-verified squarefree rank defect

The physical head matrices have exact ranks \(1,2,3,3,4,5\) for these six
head lengths. Already at \(M=4\),

\[
g_d(4)+g_d(1)=g_d(2)+g_d(3)
\qquad(d\ge2,\ d\ne4).
\]

For \(d\ge5\), this is the integer identity \(4+1=2+3\) divided by \(d\);
the cases \(d=2,3\) are direct. Thus it holds for every squarefree conductor.
The relation is compatible with a constant head. Rank deficiency is therefore
not infeasibility, but it prohibits using an ordinary inverse of the full
four-row head Gram matrix. The computations select independent physical rows
and verify all omitted constraints exactly afterward.

## Complete-norm certificates

For the candidates proposed by minimum-norm optimization, the following closed
intervals contain the **actual infinite** squared Pareto norms. Decimal endpoints
were rounded outward from exact rational endpoints.

| Head M | Exact head rank | Certified complete norm squared |
|---:|---:|---:|
| 1 | 1 | [0.55752526, 0.55753289] |
| 2 | 2 | [0.71420252, 0.71420994] |
| 3 | 3 | [0.84829710, 0.84830845] |
| 4 | 3 | [0.84829710, 0.84830845] |
| 5 | 4 | [0.87805050, 0.87806378] |
| 6 | 5 | [0.92310540, 0.92312738] |

These are intervals for the exhibited candidates. In particular, their upper
endpoints are certified upper bounds for the constrained minimum, but their
lower endpoints are **not** lower bounds for that minimum. A separate universal
lower bound for any exact-head candidate is
\(\|F_M\|_P^2\ge\sum_{n\le M}P(n)=M/(M+1)\).

For the candidates proposed by minimum-residual optimization:

| Head M | Certified complete residual norm squared |
|---:|---:|
| 1 | [0.02021497, 0.02022173] |
| 2 | [0.02040433, 0.02041104] |
| 3 | [0.02041182, 0.02041853] |
| 4 | [0.02041182, 0.02041853] |
| 5 | [0.02228236, 0.02229039] |
| 6 | [0.02524742, 0.02525776] |

The dictionary is fixed, so adding head constraints can increase the minimum
residual. This table makes no asymptotic claim.

## What the certificate checks

The period is \(L=30030\). Rational coefficients give integers \(A_r,B\)
with \(F(n)=A_{n\bmod L}/B\). The exact period maxima

\[
U=\max_{0\le r<L}|A_r|/B,\qquad
V=\max_{0\le r<L}|A_r-B|/B
\]

bound the norm and residual tails. Every finite summand through \(N=250000\)
is evaluated by exact integer division and rounded down at scale \(2^{80}\).
If the resulting norm sum is \(S_N\), then

\[
S_N\le\|F\|_P^2
\le S_N+N2^{-80}+\frac{U^2}{N+1}.
\]

The identical statement with \(F-1\) and \(V\) certifies the residual.
The tail identity is exact:
\(\sum_{n>N}P(n)=1/(N+1)\). All signed coefficients are combined before
squaring, so no mixed terms are dropped from the finite sum.

The numerical proposal stage uses the periodic Gram formula

\[
H_{de}=\sum_{r=1}^{\operatorname{lcm}(d,e)}
g_d(r)g_e(r)\,
\frac{\psi((r+1)/L_{de})-\psi(r/L_{de})}{L_{de}},
\qquad \ell_d=\frac{\log d}{d}.
\]

SciPy's floating-point digamma and linear algebra are used only to propose
coefficients. Their outputs, the reported condition number, and reported
optimal values are explicitly marked unverified in the JSON. None is used
by the final certificate verifier.

## Reproduction and verification status

[Download the reproducible bundle](https://chatgpt.com/library?file_id=libfile_680712bd867c8191b84e3feca12757a0&account_id=personal). Unpack it to obtain:

- `certify_squarefree_exact_heads.py`: numerical proposal and exact certificate code.
- `squarefree_exact_head_certificates.json`: exact rational coefficients,
  exact interval endpoints, decimal outward enclosures, and separately labelled
  numerical diagnostics for all twelve candidates.

Reproduce proposals with Python, NumPy, and SciPy:

```sh
python certify_squarefree_exact_heads.py --output squarefree_exact_head_certificates.json
```

Recheck all certificates with Python's standard library only:

```sh
python certify_squarefree_exact_heads.py --verify --output squarefree_exact_head_certificates.json
```

The independent verifier was run successfully. These are exact Python arithmetic
certificates, **not Lean kernel certificates**. The full period and all 250000
finite terms are recomputed during verification.

The next arithmetic task remains an infinite family of legal exact-head
candidates with a head-independent complete-norm bound. Six finite cases do
not supply that missing theorem.
