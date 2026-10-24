# Certified complete-P target repair costs through head length 32

Date: 24 October 2026.

This continues the constructive approximants agenda with certified **lower and upper bounds for the actual constrained minimum and target repair cost**, rather than merely upper bounds for exhibited candidate norms. It does not prove a head-independent bound, capacity saturation, or RH.

Use P(n)=1/(n(n+1)), g_d(n)=(n mod d)/d, and squarefree conductor dictionaries D={d:2≤d≤B, d squarefree} for B=24,40,60. Their largest conductors are 23,39,59 and their sizes are 15,25,36. Physical heads of lengths 8 through 32 are handled on independent rows; all omitted head equations are verified exactly afterward.

## Certified quantities

Let H be the **complete** P-Gram matrix, ell_d=log(d)/d, and C the compressed physical head matrix. Define

\[
\delta=\min_a\|1-\Phi a\|_P^2=1-\ell^TH^{-1}\ell,
\qquad E_M=\min_{Ca=\mathbf1}\|1-\Phi a\|_P^2.
\]

The actual target repair energy is

\[
R_M=E_M-\delta.
\]

When the compressed head rows are independent, it also equals
r^T(CH^{-1}C^T)^{-1}r, r=1−CH^{-1}ell. The certificates do not require a floating-point inverse to be trusted, and they do not invert the singular full physical-head matrix.

All table intervals are rounded outward from exact rational endpoints. In contrast to the earlier six-head table, **these lower endpoints are lower bounds for the minima themselves**.

| Largest conductor | Dictionary size | Head M | Exact rank | Projection defect delta | Constrained minimum E_M | Target repair energy R_M |
|---:|---:|---:|---:|---|---|---|
| 23 | 15 | 8 | 6 | [0.016218637, 0.016224706] | [0.020898878, 0.020905290] | [0.004674172, 0.004686652] |
| 23 | 15 | 12 | 8 | [0.016218637, 0.016224706] | [0.023465391, 0.023472271] | [0.007240685, 0.007253633] |
| 23 | 15 | 16 | 11 | [0.016218637, 0.016224706] | [0.033417603, 0.033425806] | [0.017192897, 0.017207168] |
| 39 | 25 | 8 | 6 | [0.013529599, 0.013536266] | [0.016576442, 0.016583762] | [0.003040176, 0.003054162] |
| 39 | 25 | 16 | 11 | [0.013529599, 0.013536266] | [0.021408234, 0.021417027] | [0.007871968, 0.007887427] |
| 39 | 25 | 24 | 16 | [0.013529599, 0.013536266] | [0.027504639, 0.027515116] | [0.013968373, 0.013985516] |
| 59 | 36 | 8 | 6 | [0.011906259, 0.011915316] | [0.014163185, 0.014173483] | [0.002247869, 0.002267223] |
| 59 | 36 | 16 | 11 | [0.011906259, 0.011915316] | [0.017832586, 0.017844969] | [0.005917270, 0.005938710] |
| 59 | 36 | 24 | 16 | [0.011906259, 0.011915316] | [0.020055134, 0.020069799] | [0.008139819, 0.008163539] |
| 59 | 36 | 32 | 20 | [0.011906259, 0.011915316] | [0.025320985, 0.025338267] | [0.013405670, 0.013432008] |

For example, with 36 squarefree conductors and head length 32,

\[
0.013405670\le R_{32}\le0.013432008.
\]

This is an interval for the complete unsampled repair energy. No zero-sampling error is present or absorbed into it. For each fixed dictionary the intervals separate the increasing cost of the larger tested heads. Enlarging dictionaries improves the tested overlapping cases. Neither observation gives an asymptotic theorem.

## Minimum complete norms and the absolute tail majorant

For the same constraints, the computation also certifies

\[
J_M=\min_{Ca=\mathbf1}\|\Phi a\|_P^2.
\]

A separate rational feasible vector and separate dual multipliers are used. Setting the Hilbert target to zero gives the dual lower bound

\[
J_M\ge2\lambda^T\mathbf1-(C^T\lambda)^TL^{-1}(C^T\lambda).
\]

The exact-head lower bound M/(M+1) is also included. Complete primal norm tails use the same signed periodic-pair computation, with target zero. These are minimum **norm** bounds, distinct from the minimum residual and repair-cost columns above.

The last column compares the crude absolute-coefficient supremum tail bound U²/(N+1) with the signed periodic-mean-plus-Abel-remainder tail upper certificate for the minimum-residual candidate. It measures loss from that absolute majorant; it does not isolate cancellation from all other sources of improvement.

| Largest conductor | Head M | Certified minimum complete norm squared J_M | Supremum-tail / signed-Abel-tail bound |
|---:|---:|---|---|
| 23 | 8 | [0.937249505, 0.937252238] | [259.175812097, 259.175812098] |
| 23 | 12 | [0.984282919, 0.984287600] | [253.471739952, 253.471739953] |
| 23 | 16 | [1.026568824, 1.026576576] | [234.579027190, 234.579027191] |
| 39 | 8 | [0.919142347, 0.919145247] | [351.743072490, 351.743072491] |
| 39 | 16 | [0.975934150, 0.975940547] | [344.627950524, 344.627950525] |
| 39 | 24 | [1.010671591, 1.010680566] | [313.961079361, 313.961079362] |
| 59 | 8 | [0.915586803, 0.915592449] | [299.066756575, 299.066756576] |
| 59 | 16 | [0.965199818, 0.965209261] | [305.485701910, 305.485701911] |
| 59 | 24 | [0.987365383, 0.987376549] | [290.374097273, 290.374097274] |
| 59 | 32 | [0.999688976, 0.999703127] | [264.891872608, 264.891872609] |

In particular, the specified 15-atom dictionary at M=16 and 25-atom dictionary at M=24 cannot provide an exact-head vector of complete norm at most 1. Larger dictionaries improve the tested cases; this finite obstruction says nothing against a uniform bound greater than 1 or a suitable growing dictionary family.

Numerical condition estimates for the complete proposal Gram are provided for diagnostics only. They are **not certified** and are not used by any interval proof:

| Largest conductor | Dictionary size | Unverified numerical Gram condition number |
|---:|---:|---:|
| 23 | 15 | 502.302366 |
| 39 | 25 | 1538.731066 |
| 59 | 36 | 3912.745718 |

All certificates instead use exact positive LDL pivots. Precision is fixed at N=200000, Gram summand rounding 2^{-50}, finite norm summand rounding 2^{-80}, 64 rational atanh terms per reduced logarithm, and final rational interval rounding 2^{-80}. Every arithmetic bound includes the appropriate rounding remainder.

## 1. A rigorously positive lower Gram matrix

Set N=200000 and s=2^50. Each finite entry is accumulated by exact integer division:

\[
A_{ij}=\sum_{n=1}^N\left\lfloor s\,g_i(n)g_j(n)P(n)\right\rfloor,
\qquad L=\frac{A-JN I}{s},\quad J=|D|.
\]

Writing H_N for the exact truncated Gram, every entry of H_N−A/s lies in [0,N/s]. Therefore, for every real coefficient vector a,

\[
\left|a^T(H_N-A/s)a\right|
\le \frac Ns\left(\sum_i|a_i|\right)^2
\le\frac{JN}{s}\|a\|_2^2.
\]

Hence L≤H_N≤H in the Loewner order. All diagonal entries in an exact rational LDL decomposition of L are checked strictly positive. Thus L is positive definite and H^{-1}≤L^{-1}.

The verifier checks dictionary and coefficient dimensions, matrix row lengths, multiplier/observation length equality, head-row ranges, and exact ranks of both the compressed and full physical head matrices before evaluation. The proposal run uses NumPy integer operations with checked no-overflow bounds; the independent verifier recomputes every finite Gram entry using only standard Python integers. Floating-point Gram matrices are used only to propose coefficients and dual directions.

## 2. Certified logarithmic sources

For x in [1,2], put t=(x−1)/(x+1)≤1/3. The exact rational series enclosure is

\[
2\sum_{k=0}^{63}\frac{t^{2k+1}}{2k+1}
\le\log x
\le2\sum_{k=0}^{63}\frac{t^{2k+1}}{2k+1}
+\frac{2t^{129}}{129(1-t^2)}.
\]

Range reduction d=2^k x and a separate identical enclosure for log 2 give rational intervals for every ell_d. Write ell=ell_0+e with |e_i|≤epsilon_i.

For B=L^{-1}, w_0=ell_0+C^Tlambda and z=Bw_0, the signed expansion gives the rigorous upper certificate

\[
(\ell+C^T\lambda)^TB(\ell+C^T\lambda)
\le w_0^Tz+2\sum_i|z_i|\epsilon_i
+\sum_{i,j}|B_{ij}|\epsilon_i\epsilon_j.
\]

All quantities on the right are exact rationals. A normal dual direction lambda is proposed numerically and rounded to rational entries; it need not be optimal for the certificate to hold.

## 3. Primal and dual minimum certificates

For any rational lambda and any feasible real a, completing the square yields

\[
\|1-\Phi a\|_P^2
\ge1+2\lambda^T\mathbf1
-(\ell+C^T\lambda)^TH^{-1}(\ell+C^T\lambda)
\ge1+2\lambda^T\mathbf1
-(\ell+C^T\lambda)^TL^{-1}(\ell+C^T\lambda).
\]

The logarithmic-source enclosure above makes this a rational lower bound for E_M. Lambda=0 gives the corresponding lower certificate for delta.

For upper bounds, free coefficient coordinates are rounded to rationals and pivot coordinates are solved exactly. Every head equality at every site 1≤n≤M is checked. The complete residual norm of this feasible vector bounds E_M from above. A separate rational unconstrained candidate bounds delta from above.

If delta belongs to [d_lo,d_hi] and E_M belongs to [E_lo,E_hi], then

\[
R_M\in[\max(0,E_{lo}-d_{hi}),\ E_{hi}-d_{lo}].
\]

The displayed intervals are subsequently rounded outward to the dyadic grid 2^{-80}; the decimal table is rounded outward again.

## 4. Complete tails without an enormous whole-dictionary period

The complete dictionary LCM is never enumerated. For a nonnegative periodic f of period L with 0≤f≤b and period mean mu, every centered partial sum has absolute value at most Lb. Abel summation with decreasing Pareto weights gives

\[
\left|\sum_{n>N}f(n)P(n)-\frac\mu{N+1}\right|
\le\frac{Lb}{(N+1)(N+2)}.
\]

The exact signed Abel identity retains its endpoint term; the estimate follows by telescoping the positive weight differences. Absolute summability follows from boundedness of f and the finite Pareto mass.

Expand the residual square first:

\[
(1-\sum_i c_i g_i)^2
=1-2\sum_i c_i g_i+\sum_{i,j}c_ic_jg_ig_j.
\]

Each g_d has period d; each product g_d g_e has period lcm(d,e)≤d e. Every period mean is computed by exact integer/rational summation. The implementation retains the signed combined mean and bounds only the final Abel remainder using the absolute coefficient weights. Thus every infinite-tail mixed term is included. The finite squared residual is summed through N by exact integer division at scale 2^80, with rounding error at most N 2^{-80}.

A prior coarse version using the universal residual supremum bound U²/(N+1) also passed independent verification. The periodic-pair Abel refinement is what makes the present intervals narrow.

## Files and reproduction

- `certify_repair_cost.py`: proposal, certificates, and independent verifier.
- `expanded_repair_certificates.json`: exact rational feasible vectors and dual directions for both norm and residual minimization, floor-rounded finite Gram entries, exact interval endpoints, tail-majorant comparisons, and separately labelled unverified numerical condition/optimization proposals.

Generate proposals and certificates with NumPy/SciPy:

```sh
python certify_repair_cost.py --output expanded_repair_certificates.json
```

Recompute all certificates using the standard library only:

```sh
python certify_repair_cost.py --verify --output expanded_repair_certificates.json
```

Verification status: the independent exact-arithmetic verifier was run separately from proposal generation and passed for all three dictionaries and all ten head constraints. Its final output was: `All complete-P primal/dual/repair intervals independently recomputed with standard library only.` These individual numerical instances are **not Lean kernel certificates**. The structural finite-dimensional inequalities and the computational arithmetic must be distinguished. The main infinite-family repair bound remains open.

## Formal structural counterparts

The new Lean modules `Analysis/ConstrainedGramCertificates.lean`, `Analysis/ParetoPeriodicAbelTail.lean`, and the extension of `Analysis/FiniteSignedQuadratic.lean` prove the complete square-completion, tail, and source-error inequalities used by this certificate design. They passed module compilation and a principal-theorem axiom audit. Their project publication is gated by the final repository checkpoint. The concrete JSON instances and the logarithmic enclosures remain independently checked arithmetic, not reflected Lean certificates.

[Download the reproducible certificate bundle](https://chatgpt.com/library?file_id=libfile_e2fc10feac2881918120b1c4f6b4625d&account_id=personal).
