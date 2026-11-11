# Signed cancellation beyond the FMZ microscopic budget
Date: 11 November 2026. Starting repository revision:
`8cf57d207372734701fb22296908744d003242fe`.

## Findings and mathematical status

There is a real improvement in the available complex-zero estimate and a
noncircular conditional route for moving ordinate tests. There is **no proof
here of cancellation for the actual horizontal prefixes**, and no proof of
Montgomery's conjecture.

* New Lean result: the repository's unconditional rational Landau provider
  gives normalized error \(O(1/\log T)\) uniformly for
  \(1\le m<n\le T^\theta\), for every fixed \(0\le\theta<2/5\).
  The previous \(1/8\) corollary left room in its existing error envelope.
* New Lean results: exact Fejer summation by parts; sharp mode, prefix,
  prefix mean-square, and bounded-difference estimates; explicit two-mode
  and three-mode probes; a signed-weight failure; an alternating example
  separating linear cancellation from pair-square control.
* New conditional research reduction in Lean: a signed horizontal-prefix
  hypothesis implies a vanishing complete moving Fourier remainder, with
  no RH or Selberg assumption. The prefix hypothesis is **Open**.
* External published input: FMZ Lemma 1 gives the stronger prime-power
  complex-zero band \(p^d\le T^\theta\), \(\theta<2\). The sharper Landau
  provider has not been transferred into these Lean declarations.
* The growing-grid formulas and their sinc limit below are elementary
  paper derivations. The numerical table is an external computation.
  Neither is mislabeled as a newly checked Lean declaration.

## 1. Exact identity and the losses in the absolute bound

Put
\[
H(t)=\sum_j b_j e^{iq_jt},\qquad \sum_jb_j=1,\qquad
V=\tfrac12\sum_{j,k}b_jb_k(q_j-q_k)^2.
\]
The exact identities
\[
V=\sum_j b_jq_j^2-\left(\sum_jb_jq_j\right)^2,\qquad
1-|H(t)|^2=\sum_{j,k}b_jb_k\{1-\cos((q_j-q_k)t)\}
\]
hold for real signed weights of total mass one. Positivity enters when
deducing \(V\ge0\), nonnegative repulsion, and multiplying
\(1-\cos x\le x^2/2\) by \(b_jb_k\).

For \(q_j=\log(n_j/m_j)\), the repository weight is
\[
W(n,m)=1+|\log n+\log m|,
\quad
M=\sum_{j,k}b_jb_k W(n_jm_k,m_jn_k)^2.
\]
It is **logarithmic height squared**, not \(n^2\), \(m^2\), or an exponential
height budget. The frequency inequality \(q^2\le W^2\) is scalar; summing it
with nonnegative pair weights gives \(2V\le M\). The old condition
\(M/\log T\to0\) therefore forces microscopic degeneracy.

The exact Fourier remainder instead has the form
\[
R_T=\sum_\lambda c_\lambda E_T(\lambda).
\]
One should aggregate equal rational frequencies and center the constant
mode first. The estimate
\[
|R_T|\le\sum_\lambda |c_\lambda|\,|E_T(\lambda)|
       \le {C\over\log T}\sum_\lambda |c_\lambda|W_\lambda^2
\]
discards (i) cancellation in aggregated coefficients, (ii) cancellation
between frequency remainders, and (iii) cancellation inside each zero sum.
For positive spectral weights the aggregated autocorrelation coefficients
are nonnegative, so (i) does not help; (ii) and (iii) still can.

The absolute mode envelope alone cannot force cancellation: aligned errors
attain its triangle bound. Changing the signs of the spectral weights is
also not a free DPP construction. For weights \((2,-1)\) and frequencies
\((0,a)\), the new Lean calculations give
\[
V=-2a^2,\qquad 1-|H(t)|^2=-4(1-\cos(at)).
\]
The positive feature-Gram interpretation has been lost.

The older actual-ordinate rate in `ActualRationalFMZRate` explicitly takes
`UniformSelbergDensity (1/4)`. Its missing provider is a formalization gap;
the elementary variance obstruction does not need that premise.

## 2. Explicit probes and their complete remainders

For a positive frequency \(q\), write \(E_T(q)\) for the normalized ordinate
Fourier coefficient minus its signed arithmetic main term; set \(E_T(0)=0\)
after exact centering, and \(E_T(-q)=\overline{E_T(q)}\).

### Two modes

Take \(b=(1/2,1/2)\), \(q=(0,a)\), \(a=\log n>0\). Then
\[
V=a^2/4,\quad 1-|H(t)|^2=(1-\cos(at))/2,\quad
R_T=\tfrac12\Re E_T(a).
\]
If \(a=\theta\log T\), the microscopic profile is exactly
\((1-\cos(\theta u))/2\). There is only one positive nonconstant mode;
no inter-frequency cancellation can be claimed for this family.
The displayed repository pair representation has exactly
\[
M_{\rm raw}=1+2a+\tfrac32a^2.
\]
Centering and reducing the two off-diagonal ratios improves it to
\(M_{\rm off}=\tfrac12(1+a)^2\), which still has order \((\log T)^2\).

### Three binomial modes

For \(b=(1/4,1/2,1/4)\) and \(q=(0,a,2a)\),
\[
V=a^2/2,\quad
|H(t)|^2={3+4\cos(at)+\cos(2at)\over8}
         =\cos^4(at/2),
\]
\[
R_T=\tfrac12\Re E_T(a)+\tfrac18\Re E_T(2a),\qquad
M_{\rm off}=\tfrac12(1+a)^2+\tfrac18(1+2a)^2.
\]
Here cancellation requires an actual relation between the two errors.
It is not a consequence of the coefficients being positive or the kernel
being positive definite. The variance and cosine formulas are in Lean.

### Growing equal-weight prime-power grid

Fix a prime \(p\), let \(L=\log p\), and take
\[
q_j=jL,\quad b_j={1\over N+1},\quad 0\le j\le N.
\]
Elementary finite summation gives
\[
V_N={L^2N(N+2)\over12},
\quad
|H_N(t)|^2={1\over(N+1)^2}
 \left(N+1+2\sum_{d=1}^N(N+1-d)\cos(dLt)\right).
\]
For \(T_N=p^{N/\theta}\), \(\theta>0\),
\[
{V_N\over(\log T_N)^2}\to{\theta^2\over12},\quad
H_N(u/\log T_N)\to e^{i\theta u/2}
 {\sin(\theta u/2)\over\theta u/2},
\]
with the quotient interpreted as one at zero. This follows directly from
the Riemann sum on \([0,1]\); no assertion about zero statistics is involved.

The complete raw budget and the reduced budget including the constant
mode are respectively
\[
M_{\rm raw}=1+2NL+{7N^2+2N\over6}L^2,
\]
\[
M_{\rm reduced}
 =1+{2LN(N+2)\over3(N+1)}+{L^2N(N+2)\over6}.
\]
The nonconstant budget is \(M_{\rm reduced}-1/(N+1)\). Thus reduction,
grouping, and exact centering improve constants, but
\(M_{\rm off}/\log T_N\sim(\theta^2/6)\log T_N\) still diverges.

Let \(Z(T)\) count all positive-height zeros through \(T\), with multiplicity,
and define
\[
A_d(T)={1\over T}\sum_{0<\gamma\le T}e^{idL\gamma},
\quad a_d={L\over2\pi p^{d/2}},\quad E_d=A_d+a_d.
\]
The complete **signed** remainder, including the exact diagonal and
arithmetic correction, is
\[
\begin{aligned}
R_N(T)
&={1\over T}\sum_{0<\gamma\le T}|H_N(\gamma)|^2
 -{Z(T)\over T(N+1)}
 +{L\over\pi(N+1)^2}\sum_{d=1}^N(N+1-d)p^{-d/2}\\
&={2\over(N+1)^2}\sum_{d=1}^N(N+1-d)\Re E_d(T).
\end{aligned}
\]
This is a one-point sampling identity; it is not a formula for the
Montgomery form factor.

## 3. Signed-prefix replacement for the absolute budget

For arbitrary complex \(e_1,\ldots,e_N\), set
\[
S_k=\sum_{d=1}^k e_d,\qquad
\mathcal R_N(e)={2\over(N+1)^2}\sum_{d=1}^N(N+1-d)e_d.
\]
The new Lean module proves
\[
\boxed{\mathcal R_N(e)={2\over(N+1)^2}\sum_{k=1}^N S_k.}
\]
Consequently,
\[
|\mathcal R_N(e)|
 \le {2\over(N+1)^2}\sum_{k=1}^N|S_k|,
\qquad
|\mathcal R_N(e)|^2
 \le {4N\over(N+1)^4}\sum_{k=1}^N|S_k|^2.
\]
A uniform prefix bound \(|S_k|\le B_N\) gives
\(2NB_N/(N+1)^2\); \(B_N=o(N)\) is sufficient. A bounded coboundary
\(e_d=f_d-f_{d-1}\) also gives an \(O(1/N)\) estimate through telescoping.

These hypotheses allow genuine cancellation. For the model errors
\(e_d=(-1)^{d-1}\), all prefixes have modulus at most one and the signed
remainder is \(O(1/N)\), whereas the complete weighted absolute error is
\(N/(N+1)\to1\). The new Lean declarations verify the prefix bound and
the exact square remainder
\[
\mathcal R_N((|e_d|^2)_d)={N\over N+1}.
\]
For constant aligned errors \(e_d=z\), Lean proves the sharp identity
\(\mathcal R_N(e)=Nz/(N+1)\). No universal cancellation factor follows
from individual mode bounds.

## 4. Stronger Landau bands and the actual moving-test theorem

Let
\[
\mathcal L_T(q)=\sum_{0<\gamma\le T}e^{q(\rho-1/2)},\qquad
\Delta_T(q)={\sum e^{iq\gamma}-\mathcal L_T(q)\over T}.
\]
Horizontal reflection gives the exact, multiplicity-preserving expression
\[
\Delta_T(q)=-{1\over T}\sum_{0<\gamma\le T}
 e^{iq\gamma}\{\cosh(q(\beta-\tfrac12))-1\}.
\]
All cancellation remains present here. The factor inside braces is
nonnegative, but the complete summand has an oscillatory phase.

The existing unconditional rational contour provider has envelope
\[
{C\over T}\left(X^{5/2}+X^{3/2}\log^2(T+3)+X\log(T+3)\right).
\]
For \(X=T^\theta\), every fixed \(0\le\theta<2/5\) makes this
\(o(1/\log T)\). `RationalLandauMovingBand` formalizes the resulting
uniform \(C/\log T\) bound. The threshold \(2/5\) belongs to this provider;
it is not claimed to be an optimal mathematical barrier.

For positive rational modes \(q_d=\log(n_d/m_d)\), \(d=1,\ldots,N\),
with \(1\le m_d<n_d\le T^\theta\), put
\[
E_d(T)={\operatorname{ordinateSum}_T(q_d)\over T}
           +\operatorname{rationalLandauMain}(n_d,m_d),
\quad
S_k^\Delta(T)=\sum_{d=1}^k\Delta_T(q_d).
\]
The new actual-zero theorem gives, uniformly over the moving support,
\[
\boxed{
|\mathcal R_N(E_T)|
\le {2\over(N+1)^2}\sum_{k=1}^N|S_k^\Delta(T)|
 +{N\over N+1}{C\over\log T}.}
\]
It first proves the exact split
\(\mathcal R_N(E)=\mathcal R_N(\Delta)+\mathcal R_N(\text{Landau error})\).
The main arithmetic sign is retained.

Thus
\[
{1\over(N_T+1)^2}\sum_{k=1}^{N_T}|S_k^\Delta(T)|\to0
\quad\Longrightarrow\quad
\mathcal R_{N_T}(E_T)\to0.
\]
This is a **conditional research reduction**, not a proof of the displayed
prefix smallness. It assumes neither Selberg nor RH nor pair correlation.
Taking \(n_d=p^d,m_d=1\), with \(N_T\log p\le\theta\log T\), is compatible
with nonzero limiting probe variance. For the symmetric real test it is
enough on paper to control the real parts of the prefixes; the Lean theorem
above controls the stronger complex remainder.

A finite collection of fixed off-line zeros would contribute at most
\(O(T^{-1+\theta/2})\) per normalized horizontal mode, uniformly in this
band. Hence this route does not demand that each horizontal displacement
vanish; its hypothesis is not secretly an assertion that every zero lies
on the critical line.

### What the published papers additionally support

[FMZ, Lemma 1](https://arxiv.org/html/1511.06814v2#Thmlem1), specialized
to the exact prime power \(x=p^d\), yields
\[
\left|{\mathcal L_T(\log x)\over T}
 +{\Lambda(x)\over2\pi\sqrt{x}}\right|
\ll {\sqrt{x}\log^2(2xT)\over T}
 +{\log(2T)\over T\sqrt{x}\log x}.
\]
For fixed \(p\), this tends to zero uniformly through \(p^d\le T^\theta\)
for every fixed \(\theta<2\). Combining that external theorem with the
same elementary prefix argument widens the paper reduction accordingly.
This sharper analytic provider is not a new Lean theorem in this change.

[FMZ, Lemma 2](https://arxiv.org/html/1511.06814v2#Thmlem2) instead
compares raw ordinates with complex-zero weights only for
\(\log x\le\log T/(50\log\log T)\), with normalized error
\(O((\log x)^2/\log T+(\log T)^{-10})\). Its stated estimate does not
give vanishing error at \(\log x\asymp\log T\). Fixed smooth-test FMZ
limits cannot be applied uniformly to these moving probes without more work.

[FSZ, Theorems 1.2--1.4](https://arxiv.org/html/0805.2745v3)
connect wider exponential-sum cancellation to short-interval prime and
pair-correlation hypotheses, with RH explicit in those implications.
The relevant stronger uniform estimates are conjectural inputs there,
not unconditional providers that can be imported to close this problem.

## 5. Parseval, dual Gram, and the pair-square obstruction

The existing `PrimeProbeDualGram` equalities identify the two finite
Gram traces, square traces, and determinant generating functions. The
actual-zero rational autocorrelation expansion groups equal ratios before
norms. These are exact identities; neither supplies uniform spectral
conditioning, random independence, or an actual-zero DPP law.

The existing `ActualSignedResidualPairing` and
`SpectralDerivativePairing` retain the gamma integral, both endpoints,
and the finite spectral correction. If \(P\) approximates the actual
integrated counting discrepancy \(S_1\), the remaining pairing obeys
\[
|\mathrm{Err}(F)|^2
 \le R(T)\left(TJ_4(F)+26\sum_\lambda
       {|c_\lambda|^2\lambda^4\over\delta_\lambda}\right),
\quad R(T)=\int_0^T|S_1(t)-P(t)|^2dt.
\]
The exact signed residual identity allows cancellation among energy,
polynomial-Gram, and mixed-correlation defects. Replacing it by three
absolute bounds is optional and can be costly.

For the symmetric Fejer polynomial here, \(\delta_\lambda=L\) and
\[
J_4={2L^4\over(N+1)^4}
       \sum_{d=1}^N d^4(N+1-d)^2
    \sim {2L^4\over105}N^3.
\]
Consequently this global Cauchy--Schwarz route needs
\(R(T)/T=o(N^{-3})\) to force the **T-normalized**, fully corrected
remainder to zero. At \(N\asymp\log T\), a proposed bound of only
\(O((\log T)^{-2})\) would leave an \(O(\log T)\) squared-error upper
bound. This calculation identifies a loss; it does not prove that the
actual error diverges. Keep the deterministic corrections when comparing
this remainder with FMZ.

Even successful one-point cancellation would leave another obligation.
For \(A_d=-a_d+E_d\),
\[
|A_d|^2-a_d^2=-2a_d\Re E_d+|E_d|^2.
\]
The finite unweighted two-zero sampling identity is
\[
{1\over T^2}\sum_{\gamma,\gamma'}|H_N(\gamma-\gamma')|^2
 ={(Z(T)/T)^2\over N+1}
  +{2\over(N+1)^2}\sum_{d=1}^N(N+1-d)|A_d|^2.
\]
Both multiplicities and the diagonal remain. The alternating example
above proves that a small signed linear remainder does not by itself
control this positive square term. The Montgomery statistic also has its
Cauchy weight and natural normalization; use
`MontgomeryPrimeProbe.shifted_probe` and
`MontgomeryFourierPairing.normalized_fourier_pairing` for that exact
bridge, rather than substituting this unweighted identity.

A viable next input must control the complete quadratic remainder (cross
term plus square), or suitable weighted mean-square errors, and the
remaining signed additive prime correlations above Fourier support one.
An assumed sine-kernel/DPP law for the actual zeros would insert the
desired statistics as a premise.

## 6. External finite numerical check

Computed with mpmath 1.3.0 at 30 decimal digits, \(p=2,T=200\), using
the first 79 numerically computed critical-line zeros.
`mp.nzeros(200)` also returned 79. This is an exploratory calculation,
**not** a certified zero enumeration or a Lean computation.

| N | variance | M_off / log T | signed R_N | empirical weighted sum of abs(E_d) | uniform-prefix bound |
|---:|---:|---:|---:|---:|---:|
| 2 | 0.320302009279 | 0.479309215334 | 0.002645785970 | 0.003936307795 | 0.004691240033 |
| 4 | 0.960906027836 | 0.932349402973 | 0.003973079905 | 0.004978037671 | 0.008455505567 |
| 8 | 3.203020092790 | 2.152092283900 | 0.007052165386 | 0.008608296850 | 0.016441323075 |
| 16 | 11.530872334000 | 6.007833193160 | 0.007801125360 | 0.017187996090 | 0.014914152336 |

The prefix column uses the **complete** errors E_d, so it illustrates the
finite summation-by-parts bound, not a numerical proof of the horizontal
prefix hypothesis. At these checked numerical zeros beta=1/2, so their
computed horizontal defect is zero. The budget column has no unknown
FMZ constant attached and is not presented as an empirical error bound.
The data exhibit finite cancellation and do not establish a limiting rate.

Reproduction: compute
`E[d] = sum(exp(1j*d*log(2)*gamma))/200 + log(2)/(2*pi*2**(d/2))`,
multiply by `2*(N+1-d)/(N+1)**2`, and retain the complete signed sum.
The following executable script performs exactly this calculation.

```python
#!/usr/bin/env python3
"""Exploratory FMZ/Fejer calculation; not a certified zero enumeration."""
import mpmath as mp

mp.mp.dps = 30
T = mp.mpf(200)
p = 2
L = mp.log(p)
gammas = [mp.im(mp.zetazero(k)) for k in range(1, 80)]
print("mpmath", mp.__version__, "numerical N(200):", mp.nzeros(T))
for N in [2, 4, 8, 16]:
    errors = [
        sum(mp.exp(1j * d * L * g) for g in gammas) / T
        + L / (2 * mp.pi * p ** (mp.mpf(d) / 2))
        for d in range(1, N + 1)
    ]
    weights = [2 * mp.mpf(N + 1 - d) / (N + 1) ** 2 for d in range(1, N + 1)]
    signed = sum(w * mp.re(e) for w, e in zip(weights, errors))
    empirical_absolute = sum(w * abs(e) for w, e in zip(weights, errors))
    prefix_bound = 2 * N * max(abs(sum(errors[:k])) for k in range(1, N + 1)) / (N + 1) ** 2
    budget = sum(w * (1 + d * L) ** 2 for d, w in enumerate(weights, 1))
    variance = L ** 2 * N * (N + 2) / 12
    print(N, *(mp.nstr(x, 12) for x in
        (variance, budget / mp.log(T), signed, empirical_absolute, prefix_bound)))
```

## 7. New declarations and verification boundary

| Module | Principal declarations | Status of the mathematics |
|---|---|---|
| `Analysis/RationalLandauMovingBand` | `eventually_rational_landau_error_power_band` | Unconditional; every fixed theta < 2/5 |
| `Analysis/FejerSignedRemainder` | `triangular_eq_prefix`, `norm_remainder_sq_le_prefix_energy`, `norm_remainder_le_modes`, `tendsto_remainder_of_prefix` | Finite algebra, inequalities, and an abstract conditional limit |
| same | `remainder_const`, `norm_remainder_difference`, `norm_remainder_alternating_le`, `alternating_square_remainder` | Explicit cancellation and pair-square countermodel |
| `Analysis/PrimeProbeExplicitFamilies` | `two_mode_microscopic`, `two_mode_rationalPairBudget`, `three_mode_variance`, `three_mode_repulsion`, signed-weight identities | Explicit finite probe calculations |
| `Analysis/ActualFejerMovingFMZ` | `fejer_remainder_exact`, `eventually_fejer_ordinate_remainder_le` | Exact actual-zero split and unconditional estimate retaining signed prefixes |
| same | `tendsto_fejer_ordinate_of_horizontal_prefix` | **Conditional research reduction**; actual horizontal-prefix smallness **Open** |

Development candidate job `job_X0k6eVW9sJvHo6JUs6iSAJ90LzutY5Lx`
passed Bazel/BuildBuddy with exit 0 in 55.369 server seconds; source SHA256
`6297f0c9a6f0fb0ebde0267c7047b33a91aa1586a3f07d780009c3c87f5269bf`.
That was a combined snippet, not an exact published-SHA project certificate.
The four saved modules also passed the scoped import build
`job_XVUyaljeYRBDPW_AdJ9dvhteV4nDyREM` (exit 0, 124.611 seconds;
[BuildBuddy](https://app.buildbuddy.io/invocation/4b35e7c5-f3a4-4c16-aa06-5ea3aaf89c82)).
A guarded axiom audit of the principal Landau, actual-prefix, prefix-energy,
alternating-square, three-mode, and rational-budget declarations passed as
`job_mEegwqQiLAdX0H40RPaV6SGklJ_c7wIC` (exit 0, 57.825 seconds;
[BuildBuddy](https://app.buildbuddy.io/invocation/586c13cf-2560-4453-849c-e3e07d461ecf)).
Each audited declaration uses only `propext`, `Classical.choice`, and
`Quot.sound`. The audit snippet SHA256 is
`cbc7622a3720ab33fa3ae1b5af21720f245e51ff332d5b33477d7c0d77808032`.
These scoped checks do not substitute for the full publication checkpoint.

Final publication must pass the repository's full
`bazel build --config=buildbuddy //:RiemannResearch` checkpoint,
including any integrated main changes. The terminal checkpoint record
and published SHA accompanying delivery establish the final scope.

No declaration supplies the missing actual signed-prefix, pair-square,
or high-support prime-correlation estimate. No priority claim is made for
the elementary mathematics or for sharpening a nonoptimal repository
corollary of a classical Landau estimate.
