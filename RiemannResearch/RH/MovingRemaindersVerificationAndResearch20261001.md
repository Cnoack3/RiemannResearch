# Moving remainders: verification and arithmetic continuation

Date: October 1, 2026. Repository baseline: 653e0105593468c966c9436a6b24c0f88e3ef942.

## Scope and result

The user requested two previously suggested GitHub prompts, verification first, with Mathematica/Wolfram and trusted web research. The verbatim prompt texts were not available in the recovered conversation. This execution therefore audited the latest RH/Route B work first, then continued its moving-remainder and signed arithmetic analysis. It does not claim to have recovered the exact prompts.

The reusable moving Bessel–Minkowski estimate and its conditional application to the actual signed CRT contrast have passed Lean checks. The earlier agenda understates the block consequence: the stated complete row representation plus finite total variation controls the full uncentered error and therefore the full centered error.

The arithmetic continuation also gives a written, conditional inverse-pivot bound and an explicit Hilbert countermodel explaining why source growth alone cannot force screened growth. The Wolfram Language script evaluates the complete physical tails of the finite Gram matrix and retains the signed screening corrections. RH remains open. None of the reviewed preprints supplies the missing arithmetic provider. The ordinary deductions below are not claimed to be new in the literature.

## 1. Verification before continuation

The baseline audit checked the exact source chain rather than treating conditional reductions as unconditional results. Its relevant declarations include:

- the unconditional Li criterion and the strict negative-Li witness under negated RH;
- canonical tail-capacity geometry and the bounded-capacity/interpolant equivalence;
- exact coprime-certificate energies, nested-modulus pairings and screened cross-Gram rows;
- the complete split-tree capacity budget, fixed-vector Bessel perturbations and moving CRT contrast reduction;
- weighted model-error square completion and divergence transfer.

The coherent baseline audit completed successfully, exit code 0, in 8.594 seconds. Its job receipt is job_0rE3Kfzy3mofH7JkumkC8aIT-xCB0aiI. The theorem hypotheses were read separately from the axiom audits: standard foundations do not discharge a local arithmetic premise. The GitHub combined-status response contained no status entries, and the workflow query only covered PR-triggered runs; these responses are not a claim that every GitHub Actions workflow passed.

Two new exported modules are added:

| Module | Established statement | Remaining mathematical inputs |
|---|---|---|
| Analysis/MovingOrthogonalEnergy.lean | Finite masked Bessel–Minkowski bound, prefix diagonal-energy bound, and summability under absolute total variation | The generic theorem explicitly assumes orthonormal tests and summable variation |
| RH/ParetoMovingRemainderTransfer.lean | The normalized signed CRT amplitude squares to the actual certificate; a divergent model with a represented finite-variation error implies RH | Open: arithmetic model divergence, exact complete representation, orthonormal tests, and the variation estimate |

The combined final-source candidate passed in 4.014 seconds, exit code 0, receipt job_1QFaDtHAM9v9-d2KI7MSVb6dYl11o_LA. All six new theorem audits report only propext, Classical.choice and Quot.sound. The generic module also passed a full-file check in 3.102 seconds. Final acceptance and publication additionally use the repository checkpoint's affected-module validation.

The formal application uses
$$
c_j=\frac{\operatorname{primeBlockMovingCRTContrastPairing}(2^j,2^j,f_j)}
 {\sqrt{\operatorname{primeBlockContrastEnergy}(2^j,2^j,f_j)}}.
$$
Its square is exactly the existing signed moving CRT certificate, including Lean's zero-denominator convention. Its hypotheses require
$$
c_j-m_j=\langle v_j,R_j\rangle,\qquad
(v_j)\ \text{orthonormal},\qquad
\sum_j\|R_{j+1}-R_j\|<\infty,\qquad \sum_jm_j^2=\infty.
$$
The generic theorem makes the error square-summable; the existing complete model transfer makes the actual certificates nonsummable, contradicting the established consequence of negated RH. Constructing those hypotheses is the open research task.

## 2. The block strengthening and the agenda correction

Use physical conductors throughout:
$$
H=\ell^2\!\left(\mathbb N_{\ge1},\frac1{k(k+1)}\right),\quad
g_d(k)=\frac{k\bmod d}{d},\quad
t_d=g_d-\frac1d\,\mathbf1_{\{1\}}.
$$
For an odd prime p, let h_p be the innovation of t_p after projecting onto t_2,...,t_{p-1}. Set
$$
\sigma_p=\|h_p\|^2,\quad \eta_p=\langle h_p,z_{\rm source}\rangle,\quad
a_p=\operatorname{factorialPrimeDelta}(p-3),\quad b_p=\eta_p-a_p,
\quad w_p=\frac{a_p^2}{\sigma_p},\quad y_p=\frac{b_p}{a_p}.
$$
The source pairing notation means the compatible observations 1/d; a global z_source exists under bounded capacity. Repository indexing is h_p = tailInnovation(p-2) and sigma_p = schurSigma(p-2). The primitive Lean function primeSchurWeight(p-3) is 1/sigma_p; the slope weight w_p includes the additional a_p squared.

Let the disjoint parent windows B_j have nonempty left and right prime children. For a model m_p, put epsilon_p = y_p-m_p. Preserve both exact identities:
$$
D_j=\sum_{p\in B_j}w_p\epsilon_p^2
 =U_{B_j}\bar\epsilon_{B_j}^{\,2}+E_j,
$$
$$
E_j=\sum_{L_j}w_p(\epsilon_p-\bar\epsilon_{L_j})^2+
 \sum_{R_j}w_p(\epsilon_p-\bar\epsilon_{R_j})^2+
 \kappa_j(G_j-\widetilde G_j)^2.
$$

Suppose the complete row discrepancy satisfies
$$
a_p\epsilon_p=\langle R_j,h_p\rangle\quad(p\in B_j).
$$
Let Pi_j project onto the span of these innovations. Their ranges are pairwise orthogonal, and D_j = ||Pi_j R_j|| squared. Writing d_i = R_(i+1)-R_i gives the exact finite direct-sum decomposition
$$
(\Pi_jR_j)_{j=0}^{J}
 =(\Pi_jR_0)_{j=0}^{J}
   +\sum_{i=0}^{J-1}(\mathbf1_{\{j>i\}}\Pi_jd_i)_{j=0}^{J}.
$$
Minkowski and Bessel therefore give
$$
\left(\sum_{j=0}^{J}D_j\right)^{1/2}
 \le \|R_0\|+\sum_{i=0}^{J-1}\|d_i\|.
$$
Monotone passage to the limit proves
$$
\sum_jD_j\le\left(\|R_0\|+\sum_i\|d_i\|\right)^2<\infty.
$$
Consequently both sum E_j and the complete contrast-error energy are finite. The agenda's claim that this rowwise finite-variation hypothesis need not control the full centered error was too weak and has been corrected. The block projection statement here is an ordinary proof; the committed generic Lean module proves the scalar/masked finite theorem and the infinite orthonormal scalar consequence.

The representation must include the entire inverse-Gram correction and every model error. It is not supplied by boundedness of R_j or by a formal choice of a symbol R_j. In a complete Hilbert space, a square-summable array of row coefficients against orthonormal innovations can itself be assembled into one fixed vector by an orthogonal series. This shows why merely asserting the existence of some bounded-variation representative can restate the desired energy estimate. A useful provider needs an independently controlled arithmetic construction.

The actual factorial packets are unsuitable as finite-variation representatives without a further modification: their squared norms grow at least linearly and each nested refinement retains its exact orthogonal norm-square cost. Visible projections may stay bounded under failure while the orthogonal residual escapes.

## 3. A conditional inverse-pivot bound for the actual arithmetic

This section is an ordinary proof using the checked canonical-interpolant implication and the existing prime coefficient-dual identities. It is not a new specialized Lean declaration.

Assume negated RH. Bounded capacity supplies z in H, with z(1)=0, such that
$$
\langle t_d,z\rangle=1/d\quad(d\ge2),\qquad C=\|z\|^2<\infty.
$$
For an odd prime p define the finite-support vector u_p by
$$
u_p(1)=2,\quad u_p(p-1)=(p-1)p,\quad
u_p(p)=-p(p+1),
$$
and zero elsewhere. It is the negative of the existing primeDualRepresenter. Its full norm is exactly
$$
\|u_p\|^2=2+(p-1)p+p(p+1)=2p^2+2.
$$
For every d>=2,
$$
\langle g_d,u_p\rangle=g_d(1)+g_d(p-1)-g_d(p)=\mathbf1_{\{d=p\}}.
$$
Indeed g_d(p)-g_d(p-1) = 1/d minus the indicator that d divides p, and primality leaves only d=p. Since the first-site pairing with u_p is 1,
$$
\langle t_d,u_p\rangle=\mathbf1_{\{d=p\}}-1/d,\qquad
\langle t_d,u_p+z\rangle=\mathbf1_{\{d=p\}}.
$$
Thus <h_p,u_p+z> = 1, including the full old projection. Cauchy gives
$$
\frac1{\sigma_p}\le\|u_p+z\|^2
 =2p^2+2+2\langle u_p,z\rangle+C
 \le4p^2+4+2C.
$$
The displayed equality retains the signed mixed term before estimating it. No lower spectral bound was silently assumed. The same finite argument works with the compatible finite minimum through conductor p, replacing C by its actual finite capacity.

Now put Q = pi squared / (pi squared - 8) and q_p = Q/p squared. Under the same failure hypothesis,
$$
\sum_{p\ {\rm odd\ prime}}\frac{q_p^2}{\sigma_p}
 \le Q^2\sum_{p\ {\rm odd\ prime}}
 \left(\frac4{p^2}+\frac{4+2C}{p^4}\right)<\infty.
$$
No prime number theorem is needed for this deduction.

Let b_0 be the fixed factorial-2 certificate and B_p=<h_p,b_0>. Bessel gives
$$
\sum_pB_p^2/\sigma_p\le\|b_0\|^2.
$$
The natural raw-row comparison, while retaining the actual screened base, is
$$
m_p^{\rm raw}=-1+\frac{q_p+B_p}{a_p}.
$$
Consequently, under failure,
$$
\sum_pw_p(m_p^{\rm raw}+1)^2
 =\sum_p\frac{(q_p+B_p)^2}{\sigma_p}
 \le2\sum_p\frac{q_p^2}{\sigma_p}+2\|b_0\|^2<\infty.
$$
Every disjoint weighted split-gap energy of this model is bounded by that full deviation energy. Its gap energy is therefore finite under failure, with the ACTUAL weights, rather than only a simpler adjacent proxy.

This is a necessary failure restriction, not an unconditional proof that this model's energy is finite and not a refutation of RH. An unconditional divergence proof for that model would itself contradict failure; the familiar raw profile and growing positive sources do not establish such divergence.

For exact screening, define q_d=0 at even conductors and Q/d squared at odd conductors. The factorial-2 observation is 1/d-q_d. With
$$
\gamma_p=\Gamma_{<p}^{-1}\Gamma_{<p,p},\qquad
T_p=q_p-\gamma_p^Tq_{<p},
$$
one has the full signed identities
$$
B_p=\eta_p-T_p,\quad
y_p=-1+\eta_p/a_p,\quad
y_p-m_p^{\rm raw}=(T_p-q_p)/a_p.
$$
The term gamma_p transposed q_<p is the moving inverse-Gram screening correction. It has not been replaced by the raw charge q_p.

## 4. Source growth with finite screened energy: an exact countermodel

This is an abstract Hilbert construction, not a replacement for the arithmetic residue dictionary.

Let H=l squared(N>=1), with standard basis e_k, and S_n=n(n+1)/2. Define, for n>=2,
$$
h_n=\sqrt{S_{n-1}/S_n}\,e_n
 -\sqrt{\frac n{S_{n-1}S_n}}\sum_{k<n}\sqrt{k}\,e_k,\quad
D_n=\sqrt n\,e_n,\quad Z_n=\sum_{k=2}^nD_k,\quad z=-e_1.
$$
The h_n are orthonormal: their norm squares are S_(n-1)/S_n + n/S_n = 1, and for m<n the old weighted partial vector is orthogonal to h_m. The D_n are also mutually orthogonal, future D_m pair to zero with h_n, and nested certificates satisfy
$$
\langle Z_m,Z_n\rangle=\|Z_m\|^2\quad(m\le n),\qquad
\|Z_n\|^2=S_n-1\longrightarrow\infty.
$$
Yet the fresh positive source and the complete screened survivor are
$$
a_n=\langle D_n,h_n\rangle=\sqrt{\frac{nS_{n-1}}{S_n}},
\qquad
\eta_n=\langle Z_n,h_n\rangle=\langle z,h_n\rangle
 =\frac2{\sqrt{(n-1)n(n+1)}}.
$$
Thus a_n squared = n(n-1)/(n+1) grows linearly, while
$$
\sum_{n=2}^{N}\eta_n^2=1-\frac2{N(N+1)},\qquad
\sum_{n=2}^{\infty}\eta_n^2=1.
$$
The complete old correction is eta_n-a_n; its sign cancels the large fresh source. The slope is -1+2/[n(n-1)]. Therefore orthogonal refinements, triangular support, nested-certificate energy identities, and even linear source growth do not by themselves force screened-energy divergence. Residue/Mobius arithmetic must do additional work.

Wolfram verified the 8-by-8 h-Gram matrix exactly as the identity, all eight displayed survivor identities exactly as zero residuals, the exact slope ratio and the telescoping infinite sum. The formulas above provide the proof for every n.

## 5. Reproducible Wolfram/Mathematica computation of the full tails

The adjacent listing [MovingRemaindersDiagnostics20261001.md](MovingRemaindersDiagnostics20261001.md) contains the reproducible script evaluated in the Wolfram Language kernel. Its full-tail Gram formula is, with L=lcm(d,e),
$$
\Gamma(d,e)=\sum_{r=1}^{L}\frac{r\bmod d}{d}\frac{r\bmod e}{e}
 \frac{\psi((r+1)/L)-\psi(r/L)}{L}-\frac1{2de}.
$$
This follows by summing every physical site r+jL with weight 1/[k(k+1)], then deleting the exact first-site contribution. It is not a physical truncation. The sanity identity Gamma(2,2)=(log 2-1/2)/4 returned zero residual.

The kernel used 35-digit arithmetic before the displayed rounding. These are numerical diagnostics, not certified interval bounds or asymptotic proofs. Conductors 2..17 give rank 16. The exact prime source used
$$
a_p=\frac{M_{p-1}}{(M_{p-1}-1)p^2},\qquad
M_{p-1}=\zeta(2)\prod_{\ell<p,\ \ell\ {\rm prime}}(1-\ell^{-2}).
$$

| p | sigma_p | eta_p | w_p | actual y_p | raw comparison |
|---:|---:|---:|---:|---:|---:|
| 3 | 0.110470620433 | 0.095425750083 | 3.114355859 | -0.837311046 | -0.837311046 |
| 5 | 0.050589692829 | -0.117018638076 | 4.073933849 | -1.257760895 | -0.850864357 |
| 7 | 0.031112548892 | 0.008412419508 | 5.330350726 | -0.979342620 | -0.931188082 |
| 11 | 0.014911234583 | 0.090086839702 | 4.981099508 | -0.669446362 | -0.936621869 |
| 13 | 0.011469834518 | -0.061828544715 | 6.169420772 | -1.232427897 | -0.953643791 |
| 17 | 0.007456559997 | 0.040592416017 | 5.952613081 | -0.807326576 | -0.957720674 |

At j=3, repository row indices 8..15 mean physical conductors 11..18. The prime children are {11,13} and {17}. The calculation gives:

| Quantity | Value |
|---|---:|
| Actual split weight kappa | 3.880852208702 |
| Actual signed gap G | 0.173609284893 |
| Raw-model signed gap | -0.011680822665 |
| Actual kappa G squared | 0.116969598875 |
| Complete contrast-error energy | 0.133239063351 |
| Raw-model gap energy | 0.000529509755 |

This is a finite demonstration of the size and sign of screening, not evidence of an infinite divergent series. The script also checks coefficient-dual pairings exactly for primes 3,5,7,11,13,17 and conductors 2..20, and the exact abstract countermodel above.

## 6. Trusted primary research and its precise applicability

1. **Werner Ehm**, On certain Gram matrices and their associated series, arXiv:2405.06349v2, May 13, 2024:
   https://arxiv.org/html/2405.06349v2.
   Section 8.1 keeps the full inversion error E^(q)(N) in the quadratic decompositions and explicitly leaves its estimation unresolved. The modified-coefficient cancellation proposals offer a candidate construction strategy, not a bound for our complete screened discrepancy. An application needs a proved identification of the Hilbert forms and the actual inverse-dependent error.

2. **Masatoshi Suzuki**, Weil's quadratic form via the screw function, arXiv:2606.09096v3, September 23, 2026:
   https://arxiv.org/html/2606.09096v3.
   Its unconditional finite-window operator framework and real-zero generators are promising for exact finite certificates. Corollary 1.6 requires a locally uniform analytic limit to deduce RH; the discussion explicitly does not provide that limit. Finite self-adjoint spectra do not identify the arithmetic infinite limit or supply Pareto remainder variation.

3. **Larry Guth and James Maynard**, New large value estimates for Dirichlet polynomials, arXiv:2405.20552v2, April 7, 2026:
   https://arxiv.org/html/2405.20552v2.
   Their bounded-coefficient, separated-sampling estimates improve zero density and short-interval prime results. Applying them here requires converting the actual inverse-Gram-dependent coefficients into a quantitatively normalized Dirichlet polynomial and controlling the resulting transfer. Such an upper estimate does not directly provide a signed lower gap estimate.

4. **Vladimir A. Mikhailets and Aleksandr A. Murach**, General forms of the Menshov–Rademacher, Orlicz, and Tandori theorems on orthogonal series, Methods Funct. Anal. Topology 17 (2011), 330–340, arXiv:1110.4253v2:
   https://arxiv.org/pdf/1110.4253.
   Their Hilbert-valued orthogonal-series framework and logarithmic maximal estimates are a trusted source for dyadic proof strategies when actual remainder increments are orthogonal. They do not prove that the arithmetic remainder increments possess that structure.

These are applicability assessments, not claims that any of these authors established the present conditional reduction. None is imported as an assumption asserting RH.

## 7. The next concrete arithmetic target

A model must retain actual weights and the complete signed inverse-Gram correction. Finite variation is one sufficient route, but a strict relative error saving can be less demanding.

Write c_j for the actual normalized contrast and m_j for a candidate model, using the same cutoffs. Let
$$
A_J=\sum_{j\le J}c_j^2,\quad M_J=\sum_{j\le J}m_j^2,\quad
T_J=\sum_{j\le J}(c_j-m_j)^2.
$$
The complete identity is
$$
T_J=M_J+A_J-2\sum_{j\le J}c_jm_j.
$$
Consequently
$$
(\sqrt{M_J}-\sqrt{A_J})^2\le T_J
 \le(\sqrt{M_J}+\sqrt{A_J})^2.
$$
Under failure A_J is bounded. If M_J tends to infinity, T_J/M_J therefore tends to 1. Proving
$$
T_J\le\theta M_J+K,\qquad \theta<1,
$$
on the same cofinal cutoffs, together with genuine model divergence, would contradict failure. Both requirements remain Open. The raw-model test and countermodel prevent replacing this signed estimate by a positive source floor, prime counting, or a fixed-column Bessel estimate.

The deliverable is an audited analytic transfer, corrected accounting, explicit arithmetic failure restrictions, and reproducible computation. It is not an RH proof.
