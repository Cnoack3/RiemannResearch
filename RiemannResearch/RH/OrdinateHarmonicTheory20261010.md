# Harmonic analysis of zeta-zero ordinates: theory and Lean verification
## Research continuation — 10 October 2026

This continues the current version of `Zero_Ordinates_Primes_Proved_Refinements_20261009(2).md` (version 1, including Sections 14–21). In particular, its fixed-width Gaussian Hankel criterion was already paper-proved in Section 20. The present work verifies a concrete finite harmonic-analysis layer in Lean and refines the analytic theory. It does not claim that the previously established criterion is a new discovery.

All sums retain the nontrivial-zero multiset and analytic multiplicities unless a distinct-ordinate set is explicitly used. No RH assumption is hidden in a sum over known critical zeros. “Paper proof” below means a complete analytical argument, independently audited; it does not mean a kernel-verified zeta theorem. Literature priority is unconfirmed.

## 1. What the new continuation establishes

| Result | Status and precise scope |
|---|---|
| Exact weighted finite spectral Gram positivity, zero-energy detection, modulation, and collision-energy limits | Lean formalization; frequencies arbitrary real numbers; no RH |
| Coefficient-uniform Parseval and eventual strict detection on a fixed finite distinct frequency family | Lean formalization with explicit FourierCancellation; no actual-zeta analytic provider asserted |
| Sharp off-diagonal Gram error with factor r−1 | Lean formalization; diagonal is exact, including empty/singleton supports |
| Singular 2×2 PSD equivalence, explicit negative witnesses, atomic Hankel identities, limit closure, moment log-convexity | Lean formalization; the hypotheses in each declaration remain visible |
| Gaussian spectral kernels and moments of Mathlib's actual zeta-zero positive-height cutoffs | Lean formalization, with analytic multiplicities; neither RH nor simplicity assumed |
| Infinite Gaussian ordinate RKHS, strict positive definiteness, heat embeddings and compact-interval universality | Complete paper proofs using stated published inputs |
| Gaussian small-width prime recovery and normalized prime-resonance matrix | Complete paper deductions from Ford–Zaharescu |
| Every-neighborhood full-zero Toeplitz witnesses and explicit finite-difference error budget | Complete paper refinement of the existing fixed-width Hankel criterion |
| Complete monotonicity of the origin heat trace iff RH | Complete paper proof; uses Bernstein's theorem and genuine full-zero poles |
| Improved horizontal blindness error O(√a/log(1/a)) and heat-trace constant 7/4 | Complete paper proofs using the published Selberg density input |
| Automatic positivity of every fixed finite full-zero Hankel matrix at small widths | Complete paper proof; no RH; shows the first failing degree diverges if RH is false |
| Universal positivity of the full-zero arithmetic matrices | Open; would prove RH |
| Full analytic Lean verification of Gaussian growth, explicit formula and RH equivalences | Open; finite algebra is not a substitute for these providers |

The complete formal acceptance record is in Section 5. A queued request or an isolated successful snippet is not final project verification.

## 2. The core spectral objects

Write ρ=1/2+δ+iγ. For a>0 define
\[
 Z_a(u)=\sum_ρ e^{-aγ^2}e^{iuγ},\qquad
 S_a(u)=\sum_ρ e^{a(δ+iγ)^2+u(δ+iγ)}.
\]
The ordinate measure groups horizontal partners into the same real spectral atom. Thus Z_a is positive definite unconditionally. S_a retains δ and is the object entering RH criteria.

For distinct signed ordinates Γ, let
\[
 m_γ=\sum_{\Imρ=γ}\operatorname{ord}_ρζ,\qquad
 w_a(γ)=m_γe^{-aγ^2}.
\]
The exact identity is
\[
 \sum_{j,k}c_j\overline{c_k}Z_a(t_j-t_k)
 =\sum_{γ\in Γ}w_a(γ)\left|\sum_jc_je^{it_jγ}\right|^2.
\]
It retains every cross term before taking any estimate. Fixed-frequency equidistribution implies strict positivity for distinct t_j. Published positive-proportion simplicity plus exponential-type Fourier uniqueness implies universality on every compact real interval. These facts constrain sampling but do not locate the original horizontal zero coordinates.

## 3. Useful refinements of the earlier work

### 3.1 Coefficients may depend on the observations

For one fixed finite distinct frequency family u_1,…,u_r, put
\[
 D_c(t)=\sum_jc_je^{iu_jt}.
\]
Fixed-frequency cancellation implies
\[
 \forall ε>0\quad\exists N\quad\forall n\ge N\quad\forall c:
 \left|\frac1{n+1}\sum_{k=0}^n|D_c(γ_k)|^2-\|c\|_2^2\right|
 \le ε\|c\|_2^2.
\]
The threshold works for every c, including coefficients selected after observing the samples. This improves a merely coefficient-by-coefficient limit. The frequency support remains fixed. Lean verifies this implication under the explicit cancellation property; it does not supply the analytic cancellation theorem for the actual enumeration.

If a normalized Gram matrix has exact diagonal one and off-diagonal norm at most e, then
\[
 (1-(r-1)e)\|c\|_2^2\le c^*Gc
 \le (1+(r-1)e)\|c\|_2^2.
\]
The coefficient r−1 improves the earlier r estimate, and follows by subtracting the exact diagonal energy before Cauchy–Schwarz. Consequently one finite sufficiently large cutoff detects every nonzero vector on the fixed support.

### 3.2 Primes are the first Gaussian correction

For fixed u≠0,
\[
 \lim_{a\downarrow0}2\sqrt{πa}\,Z_a(u)
 =-\frac{Λ(e^{|u|})}{e^{|u|/2}}.
\]
For a fixed distinct time list, let G_a(j,k)=Z_a(t_j-t_k)/Z_a(0). Then
\[
 G_a=I+\frac{R}{\log(1/a)}+o\!\left(\frac1{\log(1/a)}\right),
\qquad
 R_{jj}=0,\quad
 R_{jk}=-\frac{2Λ(e^{|t_j-t_k|})}{e^{|t_j-t_k|/2}}.
\]
Only prime-power differences resonate. The leading identity matrix and the signed correction coexist. These are Gaussian consequences of the known fixed-frequency theorem, not a new theorem replacing it.

### 3.3 Full-zero positivity can be tested arbitrarily locally

For a single fixed a>0, define m_n(a)=i^{-n}S_a^{(n)}(0) and
H_N(a)=[m_{j+k}(a)]_{j,k=0}^N. The current source report already proved
\[
 \mathrm{RH}\iff H_N(a)\succeq0\quad\text{for every }N.
\]
This continuation supplies explicit finite-difference congruences. If any H_N has a negative direction, a negative Toeplitz matrix [S_a((j-k)h)] exists in every neighborhood of the origin for sufficiently small h. The error budget retains powers of h^{-1}; these witnesses become ill-conditioned.

The heat equation identifies the two even/odd derivative blocks of R(a)=S_a(0). An additional criterion is
\[
 \mathrm{RH}\iff t\mapsto R(a_0+t)\text{ is completely monotone}
\]
for any fixed a_0>0. Its converse uses the impossibility of nonreal poles of a positive Stieltjes transform. Proving the necessary arithmetic positivity remains the unresolved step.

### 3.4 Why finitely many narrow-width tests cannot settle RH

For each fixed N, unconditionally,
\[
 \frac{\sqrt a}{\log(1/a)}
 J_aH_N(a)J_a\longrightarrow C_N,
\qquad
 J_a=\operatorname{diag}(1,a^{1/2},…,a^{N/2}),
\]
where
\[
 C_N(j,k)=\frac1{4π}\int_\mathbb R x^{j+k}e^{-x^2}\,dx.
\]
C_N is strictly positive definite. Hence each fixed H_N(a) is strictly positive for all sufficiently small a. If RH fails, the least failing matrix order must tend to infinity as a↓0. This preserves the distinction between “every fixed N eventually” and “one width works for every N.”

### 3.5 A stronger error bound, with the density input stated

Selberg's published bound, quoted in Ford–Zaharescu Lemma 2, gives
\[
 \sum_{0<γ\le T}δ^2\ll T/\log T.
\]
Layer-cake integration and Gaussian weighting improve the paired mismatch to
\[
 S_a(u)-Z_a(u)=O_C\!\left(\frac{\sqrt a}{\log(1/a)}\right)
 \quad(|u|\le C\sqrt a).
\]
The earlier bound was O_C(√a log(1/a)). The improvement expresses reduced sensitivity in a shrinking observation window; it is not proof that δ vanishes.

Retaining the gamma contribution, the pole term and every prime power gives
\[
 Z_a(0)=
 \frac{\log(1/a)-γ_E-2\log(4π)}{4\sqrt{πa}}
 +\frac74+O(\sqrt a).
\]
Both signed ordinates are included. The corresponding one-sided formula is half of this.

## 4. Exact arithmetic obligations

The Gaussian full-zero identity remains
\[
 S_a(u)=2e^{a/4}\cosh(u/2)+A_a(u)
 -\sum_{n\ge2}\frac{Λ(n)}{\sqrt n}
 \{k_a(u-\log n)+k_a(u+\log n)\},
\]
where k_a(v)=(4πa)^{-1/2}e^{-v²/(4a)} and A_a is the exact digamma integral specified in Appendix II. Raw undamped Fourier series are not used as ordinary convergent functions.

The current source's scalar ordinate-resolvent comparison remains an equally concrete target:
\[
 3\sum_{γ>0}\frac1{γ^2+9/4}
 \le \frac32-\frac{\logπ+γ_E}{2}
 -\sum_{n\ge2}\frac{Λ(n)}{n^2}.
\]
The opposite direction has already been paper-proved; the displayed direction is RH-strength and remains Open. No coordinate-only positivity theorem discharges it.

The earlier Pareto compressed evaluation/Gram obstructions and high-ordinate asymptotic remain paper results in the source report. This continuation does not claim to have kernel-verified them.

## 5. Verification record and source ledger

Final verification metadata will be appended after the introducing checkpoint reaches its terminal result. Four new analysis modules contain 43 public theorem declarations. This count includes supporting finite algebra, not 43 independent zeta-distribution discoveries.

The concrete actual-zero module defines its cutoff using the repository's `cutoff T`, built from Mathlib's actual `riemannZeta` nontrivial zeros. Its weights are `zeroMult ρ * exp(-a * ρ.im^2)`. Thus the checked positivity statements concern all actual positive-height zeros in that cutoff with multiplicity, rather than an externally supplied list of critical zeros. Finite cutoffs are valid even for a≤0; a>0 is indispensable for the infinite Gaussian theory.

The key assumptions exposed by formal declarations are:
- `FourierCancellation times` for sampled limits and character rigidity.
- Nonnegative weights/nodes for generic atomic moment theorems.
- Convergence of finite moments for the infinite-limit log-convexity transfer.
- Shifted Hankel positivity for derivative inequalities; the theorem does not prove that full-zero derivatives satisfy it.

The full-zero analytic bridge remains unformalized in this continuation. No `sorry`, `admit`, local axiom or unsafe declaration is introduced.

## 6. Provenance and novelty assessment

- Ford–Zaharescu, *On the distribution of imaginary parts of zeros of the Riemann zeta function*: fixed-frequency cancellation/resonance and Selberg density input. <https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf>
- Ford–Meng–Zaharescu: multidimensional prime-phase structure and uniform horizontal mismatch. <https://www.ford126.web.illinois.edu/wwwpapers/FMZ.pdf>
- Aronszajn, *Theory of Reproducing Kernels*: the general RKHS construction. <https://web.mit.edu/9.520/www/spring06/Papers/aron.pdf>
- Bondarenko–Radchenko–Seip, *Fourier Interpolation with Zeros of Zeta and L-Functions*, equation (1.1): the unconditional full-zero Guinand–Weil formula. <https://link.springer.com/article/10.1007/s00365-022-09599-w>
- Suzuki, *Aspects of the screw function corresponding to the Riemann zeta function*, especially Theorems 1.2 and 1.8: established positivity and Hankel-moment RH criteria. <https://arxiv.org/html/2206.03682v4>
- Suzuki, *Weil's quadratic form via the screw function*, September 2026 revision: adjacent operator/de Branges context, not an input used to assert our novel results. <https://arxiv.org/html/2606.09096v3>
- Bui–Conrey–Young: published positive-proportion simple critical zeros, sufficient for compact-interval universality. <https://aimath.org/~kaur/publications/69.pdf>
- NIST DLMF 5.11: log-gamma and digamma asymptotics used in the heat-trace constant. <https://dlmf.nist.gov/5.11>

The Gaussian formulations, local certificates, sharp finite error factor and automatic fixed-order positivity are useful refinements to the present research program. A literature search has not established publication priority. Ordinary positive spectral kernels, RKHS constructions and moment inequalities are classical. The fixed-width Hankel criterion is already in the user's current continuation, and is explicitly credited above.

Wolfram was used only for small checks: the prime-two correction −2log2/√2≈−0.980258143469 and a polynomial expansion. An attempted Gaussian integral evaluation timed out and contributes no evidence. The proofs do not depend on those computations.

# Appendix I. Complete ordinate harmonic theory


# A harmonic analysis of the ordinate measure

Derived on 2026-10-11. All the statements below concern the actual nontrivial zeta zeros, without RH unless explicitly indicated. These are paper proofs, not Lean verifications. The construction is classical harmonic analysis specialized to this spectrum; the refined Gaussian prime-resonance matrix is a consequence of the known Ford–Zaharescu theorem. No literature-priority claim is made.

## 1. Keep the spectral measure and multiplicities precise

Let Γ be the **distinct signed ordinate set**. Set

\[
 m_\gamma=\sum_{\rho:\Im\rho=\gamma}m_\rho,
 \qquad \mu=\sum_{\gamma\in\Gamma}m_\gamma\delta_\gamma.
\]

Thus a hypothetical reflected off-line pair is merged into the same spectral atom and contributes twice to its ordinate multiplicity. Complex conjugation makes μ symmetric. Put

\[
 Z_a(t)=\sum_{\gamma\in\Gamma}m_\gamma e^{-a\gamma^2}e^{it\gamma},
 \quad H(a)=Z_a(0),\quad K_a(t,s)=Z_a(t-s),\quad a>0.
\]

The counting estimate N(T)=O(T log(T+2)) proves that μ is tempered and that all Gaussian moments are finite. Each Z_a is entire in t: on a compact set |Im t|≤R,

\[
 |\gamma|^k e^{-a\gamma^2+R|\gamma|}
 \le C_{a,R,k}e^{-a\gamma^2/2},
\]

which is summable. This also justifies termwise differentiation, uniformly on compact subsets of a>0 and complex t. In particular

\[
 \partial_a Z_a=\partial_t^2 Z_a,
 \quad Z_a(t)=Z_a(-t)\in\mathbb R\quad(t\in\mathbb R).
\]

No information about β is asserted by this construction. Its spectral measure has discarded the individual horizontal coordinates.

## 2. Positive definiteness is unconditional, and is strict

For arbitrary finite times t_j and complex coefficients c_j,

\[
 \sum_{j,k}c_j\overline{c_k}K_a(t_j,t_k)
 =\sum_{\gamma\in\Gamma}m_\gamma e^{-a\gamma^2}
     \left|\sum_jc_je^{it_j\gamma}\right|^2\ge0. \tag{2.1}
\]

Absolute summability justifies interchanging the finite and infinite sums.

**Theorem 2.1.** If the t_j are pairwise distinct and c is nonzero, (2.1) is strictly positive, for every a>0.

**Proof.** If (2.1) were zero, each nonnegative summand would vanish, so P(γ)=0 at every ordinate, where P(v)=Σ_j c_j exp(it_jv). The unconditional fixed-frequency equidistribution theorem gives

\[
 \frac1{N(T)}\sum_{0<\gamma\le T}|P(\gamma)|^2
 \longrightarrow\sum_j|c_j|^2.
\]

Indeed, expand the square. The diagonal averages equal one; for j≠k the averages of exp(i(t_j−t_k)γ) tend to zero. The left side is identically zero, a contradiction. This proof uses neither rational independence nor simplicity. □

A quantitative finite certificate follows. For a given finite distinct time list, let

\[
 D_T=\max_{j\ne k}\left|\frac1{N(T)}
  \sum_{0<\gamma\le T}e^{i(t_j-t_k)\gamma}\right|.
\]

Then

\[
 \sum_{j,k}c_j\overline{c_k}K_a(t_j,t_k)
 \ge e^{-aT^2}N(T)[1-(r-1)D_T]\|c\|_2^2. \tag{2.2}
\]

Here r is the number of times, and the bound is useful when its bracket is positive. It comes from retaining only the positive ordinates ≤T and bounding all off-diagonal entries of their empirical Gram matrix. No claim of a uniform lower bound for r growing with T is made.

## 3. An unconditional heat version of prime-power recovery

Use the literature theorem, with multiplicities included,

\[
 A_u(T):=\sum_{0<\gamma\le T}e^{iu\gamma}
 =c(u)T+o_u(T),\qquad
 c(u)=-\frac{\Lambda(e^{|u|})}{2\pi e^{|u|/2}},\quad u\ne0. \tag{3.1}
\]

Λ(x) is zero unless x is an integer prime power. Ford–Zaharescu's Theorem 1/Corollary 2 applied to one smooth torus character supplies (3.1) unconditionally.

**Theorem 3.1.** For every fixed u≠0,

\[
 \boxed{\lim_{a\downarrow0}2\sqrt{\pi a}\,Z_a(u)
 =-\frac{\Lambda(e^{|u|})}{e^{|u|/2}}.} \tag{3.2}
\]

**Proof.** Stieltjes integration by parts, with A_u(0)=0 and Gaussian decay at infinity, yields

\[
 \sum_{\gamma>0}e^{-a\gamma^2}e^{iu\gamma}
 =2a\int_0^\infty t e^{-at^2}A_u(t)\,dt
 =\frac{c(u)\sqrt\pi}{2\sqrt a}+o_u(a^{-1/2}).
\]

For the error, write A_u(t)−c(u)t=o(t). Given ε>0, bound its part t≥T_ε by ε times the same Gaussian integral. On [0,T_ε] its contribution is O_ε(a), hence o(a^{-1/2}). The negative ordinates give the conjugate of the positive-ordinate sum, and c(u) is real. Doubling its real part proves (3.2). □

This recovers primes from ordinates alone through an **asymptotic** small-width measurement. It differs from the exact fixed-width full-zero prime formula, which retains β and has an archimedean correction. No fixed finite data are claimed to determine the limit.

## 4. Gaussian normalization and the resonance matrix

The ordinary counting formula gives

\[
 \boxed{H(a)=\frac{\log(1/a)-\gamma_E-2\log(4\pi)}{4\sqrt{\pi a}}
        +O(\log(1/a)),\qquad a\downarrow0.} \tag{4.1}
\]

**Proof.** The two signs give

\[
 H(a)=4a\int_0^\infty t e^{-at^2}N(t)\,dt.
\]

Insert N(t)=t( log(t/(2π))−1)/(2π)+O(log(t+2)) (the bounded initial interval changes only O(a)). The error is O(log(1/a)). The main integral uses

\[
 \int_0^\infty t^2e^{-at^2}dt=\frac{\sqrt\pi}{4a^{3/2}},
 \quad
 \int_0^\infty t^2e^{-at^2}\log t\,dt
 =\frac{\sqrt\pi}{8a^{3/2}}[\psi(3/2)-\log a],
\]

and ψ(3/2)=2−γ_E−2 log2. Substitution gives (4.1). □

For fixed pairwise distinct times t_1,…,t_r define the normalized Gram matrix

\[
 (G_a)_{jk}=Z_a(t_j-t_k)/H(a).
\]

**Theorem 4.1.** In any finite-dimensional matrix norm,

\[
 \boxed{G_a=I+\frac{R}{\log(1/a)}+o(1/\log(1/a)),} \tag{4.2}
\]

where

\[
 R_{jj}=0,\qquad
 R_{jk}=-\frac{2\Lambda(e^{|t_j-t_k|})}{e^{|t_j-t_k|/2}}\quad(j\ne k).
\]

**Proof.** The diagonal entries are exactly one. Divide (3.2) by (4.1) for each fixed nonzero difference. There are finitely many entries, so the entrywise little-o is a matrix-norm little-o. □

Consequently

\[
 \lambda_{\min}(G_a)
 =1+\frac{\lambda_{\min}(R)}{\log(1/a)}+o(1/\log(1/a)),
\]

and similarly for the maximum eigenvalue. These statements follow from Weyl's finite-dimensional perturbation inequality. In particular, normalized interpolation Gram matrices become well-conditioned as the width tends to zero, while H(a) diverges.

For t_j=k_j log p the correction is

\[
 R_{jk}=-2(\log p)p^{-|k_j-k_k|/2}\quad(j\ne k).
\]

More generally, prime-power coordinate differences resonate only when their ratio is itself a prime power. Mixed prime factors produce zero correction. Formula (4.2) is the Gaussian counterpart of the previously proved fixed-support covariance law, not a new independent prime-distribution theorem.

## 5. The exact ordinate RKHS and its unitary representation

Set w_a(γ)=m_γ exp(−aγ²). Define

\[
 \mathcal H_a=\left\{f(t)=\sum_{\gamma\in\Gamma}b_\gamma e^{it\gamma}:
 \sum_\gamma\frac{|b_\gamma|^2}{w_a(\gamma)}<\infty\right\},
 \qquad \|f\|_a^2=\sum_\gamma\frac{|b_\gamma|^2}{w_a(\gamma)}.
\]

The Fourier sum is absolutely and uniformly convergent on real t by Cauchy–Schwarz. It is normally convergent on complex compact sets by the same estimate with Gaussian moments. The coefficient representation is unique: averaging f(t)exp(−iλt) over [−Y,Y] and passing through the absolutely summable series gives b_λ. Thus this norm is well-defined and the coefficient map identifies H_a isometrically with a weighted ℓ² space.

Using the inner-product convention linear in the first argument, the coefficient of exp(itγ) in K_a(t,s) is w_a(γ)exp(−isγ), and

\[
 \langle f,K_a(\cdot,s)\rangle_a=f(s).
\]

Hence H_a is exactly the RKHS of K_a. The normalized basis

\[
 e_\gamma^{(a)}(t)=\sqrt{w_a(\gamma)}e^{it\gamma}
\]

is orthonormal. Translation U_hf(t)=f(t+h) multiplies the γ-th coefficient by exp(ihγ); consequently U_h is a strongly continuous unitary group. Strong continuity follows by dominated convergence in the coefficient norm. Its self-adjoint generator is multiplication by γ, with domain Σ γ²|b_γ|²/w_a(γ)<∞.

This is an ordinate-only self-adjoint realization constructed from known real ordinates. Its existence does not force the original zeta zeros to have β=1/2.

## 6. Exact regularization and quantitative compactness

For b>a, the natural embedding J_ba:H_b→H_a is compact. In the orthonormal bases above it is diagonal with entries

\[
 \boxed{\sigma_\gamma(J_{ba})=e^{-(b-a)\gamma^2/2}.} \tag{6.1}
\]

This follows by applying J to e_γ^(b) and rewriting in the a-basis. Thus all Schatten powers are finite; the inverse on the range is unbounded. **Distinct** ordinates index these singular values; merged ordinate multiplicity affects the weights but cancels in the ratio.

For h>0, define the heat multiplier T_h by b_γ↦exp(−hγ²)b_γ. On fixed H_a it is a compact positive contraction, and

\[
 \boxed{T_h:\mathcal H_a\longrightarrow\mathcal H_{a+2h}
          \text{ is a unitary isomorphism}.} \tag{6.2}
\]

Indeed, each term of the new squared norm is exp((a+2h)γ²)exp(−2hγ²)|b_γ|²/m_γ, which equals the old term. Conversely, exp(hγ²) applied to any coefficient sequence in H_(a+2h) gives an H_a sequence of equal norm. This separates heat smoothing from changing the functional norm.

## 7. Long-window orthogonality and multiplicity-sensitive autocorrelation

Every f∈H_a has unique Fourier coefficients recovered by

\[
 b_\lambda=\lim_{Y\to\infty}\frac1{2Y}
       \int_{-Y}^{Y}f(t)e^{-i\lambda t}\,dt.
\]

For f(t)=Σ b_γ exp(itγ) and g(t)=Σ d_γ exp(itγ),

\[
 \lim_{Y\to\infty}\frac1{2Y}\int_{-Y}^Yf(t)\overline{g(t)}dt
 =\sum_\gamma b_\gamma\overline{d_\gamma}, \tag{7.1}
\]

because the exact finite-window expression is

\[
 \sum_{\gamma,\lambda}b_\gamma\overline{d_\lambda}
 \operatorname{sinc}(Y(\gamma-\lambda)),
 \quad\operatorname{sinc}(0)=1.
\]

The double coefficient sum is absolutely summable; bounded dominated convergence retains precisely γ=λ. Replacing f(t) by f(t+h) gives

\[
 C_f(h)=\sum_\gamma|b_\gamma|^2e^{ih\gamma}.
\]

For the ordinate trace itself this is

\[
 \boxed{C_{Z_a}(h)=\sum_{\gamma\in\Gamma}m_\gamma^2e^{-2a\gamma^2}e^{ih\gamma}.} \tag{7.2}
\]

The square of the **total** ordinate multiplicity is essential. Treating a repeated ordinate as two orthogonal frequencies gives an incorrect autocorrelation. Close but unequal ordinates contribute to finite windows through their sinc factors and vanish only in the limit.

## 8. Provenance and formalization boundaries

Primary inputs:

- Ford–Zaharescu, *On the distribution of imaginary parts of zeros of the Riemann zeta function*, Theorem 1/Corollary 2: https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf. Inspected in this run, ref `turn36view0`.
- Ford–Meng–Zaharescu, *Simultaneous distribution of the fractional parts of Riemann zeta zeros*: https://www.ford126.web.illinois.edu/wwwpapers/FMZ.pdf. Inspected in this run, ref `turn36view1`.
- Aronszajn, *Theory of reproducing kernels*, Trans. AMS 68 (1950), 337–404: https://www.ams.org/tran/1950-068-03/S0002-9947-1950-0051437-7/S0002-9947-1950-0051437-7.pdf. Official source discovered, direct open failed; alternate original-paper scan is https://web.mit.edu/9.520/www/spring06/Papers/aron.pdf. Construction above is proved directly and does not rely on an uninspected claim.
- Voros, *Zeta functions for the Riemann zeros*, Ann. Inst. Fourier 53 (2003), 665–699: https://numdam.org/item/AIF_2003__53_3_665_0/. This establishes the substantial existing literature on spectral transforms of zeta zeros; it is not used as a proof input here.

These conclusions do not improve the known RH zero-free region. They organize unconditional ordinate information, improve the earlier purely semidefinite conclusion to strict finite interpolation positivity, and identify the exact Gaussian prime-resonance correction. Priority remains unverified.

Lean-friendly elementary cores include the finite Gram-energy identity (2.1), nonnegativity, the bound (2.2), finite sinc orthogonality, the diagonal norm identity (6.2), and the general strictness implication under an explicit vanishing-exponential-average hypothesis. Full zeta specialization additionally requires formalizing/importing the unconditional counting/equidistribution theorems, Gaussian Stieltjes asymptotics, and infinite-sum/RKHS arguments. Kernel verification of a generic finite lemma must not be presented as verification of all those analytic inputs.

## Appendix A. The full unconditional heat-trace constant

The counting-only remainder in (4.1) can be sharpened, using the previously audited full-zero Gaussian explicit formula, to

\[
 \boxed{H(a)=\frac{\log(1/a)-\gamma_E-2\log(4\pi)}{4\sqrt{\pi a}}
       +\frac74+O(\sqrt a\log(1/a)).} \tag{A.1}
\]

The proof below does not use a density-one critical-line assumption or any zero-density improvement.

Write σ=1/4 and r(t)=Re ψ(σ+it/2)−log|t/2|. The digamma Stirling expansion shows r(t)=O(t^−2) for |t|≥1. Near zero, ψ is bounded and log|t| is integrable. Consequently r∈L¹(R), and

\[
 \int_\mathbb R(e^{-at^2}-1)r(t)\,dt=O(\sqrt a). \tag{A.2}
\]

For (A.2), use |1−exp(−at²)|≤min(at²,1), estimate the bounded interval by O(a), split the rest at |t|=a^−1/2, and use the O(t^−2) bound on both pieces.

The integral of r is exact. Let LogΓ be the analytic logarithm of Γ on Re z>0 chosen real at positive real z. Along the vertical line,

\[
 \int_0^Y\Re\psi(\sigma+iy)\,dy=\Im\operatorname{Log}\Gamma(\sigma+iY).
\]

Stirling's formula gives

\[
 \Im\operatorname{Log}\Gamma(\sigma+iY)
 =Y\log Y-Y+(\sigma-\tfrac12)\frac\pi2+O(Y^{-1}).
\]

Subtract ∫_0^Y log y dy=Y logY−Y, double by conjugate symmetry, and take Y→∞. This proves

\[
 \int_\mathbb R[\Re\psi(\sigma+iy)-\log|y|]dy
 =\pi(\sigma-\tfrac12).
\]

The substitution t=2y therefore gives ∫r(t)dt=−π/2. The logarithmic Gaussian integral is elementary, and the archimedean term in the full-zero formula satisfies

\[
 A_a(0)=\frac{\log(1/a)-\gamma_E-2\log(4\pi)}{4\sqrt{\pi a}}
             -\frac14+O(\sqrt a). \tag{A.3}
\]

The pole term is 2exp(a/4)=2+O(a). The prime term is exponentially small: for 0<a≤a₀,

\[
 P_a(0)\le C_{a_0}a^{-1/2}
             e^{-(\log2)^2/(8a)},
\]

because one splits exp(−(logn)²/(4a)) into two equal Gaussian factors, uses logn≥log2 in one factor, and bounds the other by its value at a₀. The constant involves the convergent series Σ_(n≥2) Λ(n)n^−1/2 exp(−(logn)²/(8a₀)). Thus the exact full-zero formula yields

\[
 S_a(0)=\frac{\log(1/a)-\gamma_E-2\log(4\pi)}{4\sqrt{\pi a}}
             +\frac74+O(\sqrt a). \tag{A.4}
\]

Finally, the previously proved horizontal-sensitivity bound at u=0 is

\[
 |S_a(0)-Z_a(0)|
 \le e^{a/4}\left[\frac a4H(a)+\frac{a^2}2H_2(a)\right]
 =O(\sqrt a\log(1/a)),
\]

where H₂(a)=Σ_ρ γ²exp(−aγ²)=O(a^−3/2 log(1/a)) follows directly from counting. Combining with (A.4) proves (A.1). The number 7/4 is therefore proved for the actual ordinate-only heat trace, unconditionally, with the stated remainder.

## Appendix B. Local universality of the ordinate Fourier space

**Theorem B.1.** For each a>0 and each compact interval I⊂R, the restrictions of H_a are uniformly dense in C(I). Moreover, for every nonzero finite complex Borel measure ν supported in I,

\[
 \boxed{\int_I\int_I K_a(t,s)\,d\nu(t)d\overline\nu(s)>0.} \tag{B.1}
\]

This strengthens finite strict positivity to integral strict positivity on every compact interval. It uses a classical published positive-proportion simplicity theorem, not any conjectured rational independence or RH.

**Input.** Bui–Conrey–Young, *More than 41% of the zeros of the zeta function are on the critical line*, Acta Arithmetica 150 (2011), Theorem 1.1, proves κ*≥0.4058, where κ* is the liminf proportion of simple critical zeros. The original author-paper PDF at https://aimath.org/~kaur/publications/69.pdf was inspected in this run (web ref `turn50view0`, page 1). In particular the number D(T) of distinct positive ordinates is ≳T logT.

**Proof.** If the left side of (B.1) were zero, the absolutely convergent Gaussian feature expansion implies

\[
 F(\gamma)=0\quad(\gamma\in\Gamma),\qquad
 F(z)=\int_Ie^{izt}\,d\nu(t).
\]

Let R₀=max_(t∈I)|t|. Then F is entire and |F(z)|≤|ν|(I)exp(R₀|Im z|). A nonzero entire function with this bound has only O(T) zeros in |z|≤T, counted with multiplicity: choose z₀ with F(z₀)≠0 and apply Jensen's formula in |z−z₀|≤2T to bound the number in the inner disk by a constant times T. The zeros at the distinct ordinates would instead number ≳T logT. Consequently F≡0.

All derivatives of F at zero vanish, so ∫_I t^n dν(t)=0 for every n≥0. Polynomial density on I and continuity of integration imply ν=0. This contradicts the premise and proves (B.1).

If the span of the functions exp(iγt), γ∈Γ, were not dense in C(I), Hahn–Banach and the Riesz representation theorem would supply a nonzero finite complex measure ν annihilating this span. The same argument forces ν=0. Every one of these exponentials belongs to H_a, so H_a|_I is dense as claimed. □

The proof supplies existence of local approximation, and the compact heat embeddings of Section 6 specify its norm costs. It does not give a uniform bound on the RKHS norm of approximants as their accuracy tends to zero. This local completeness phenomenon is a standard exponential-type uniqueness argument specialized to the known superlinear density of distinct zeta ordinates; no claim of novel literature priority is made.


# Appendix II. Gaussian refinements and finite-test limitations

# Full-zero Gaussian harmonic analysis: audited refinements

Prepared independently for the coordinating agent. These are paper proofs;
no Lean job was submitted by this agent and no literature-priority claim is made.

## 1. Definitions and indispensable distinction

Zeros are counted with multiplicity. Write
\[
\rho=\tfrac12+\delta_\rho+i\gamma_\rho,
\qquad w_\rho=\delta_\rho+i\gamma_\rho.
\]
The classical facts used here are: \(|\delta_\rho|<1/2\),
\(\gamma_\rho\ne0\), invariance of the multiset under conjugation and
\(w\mapsto-w\), local discreteness, and \(N(T)=O(T\log(T+2))\).
For \(a>0\), define the **full-zero** trace
\[
S_a(u)=\sum_\rho e^{a w_\rho^2+u w_\rho},\qquad R(a)=S_a(0).
\]
The **ordinate-only** trace
\[
Z_a(u)=\sum_\rho e^{-a\gamma_\rho^2}e^{iu\gamma_\rho}
\]
is positive definite without RH. Likewise \(a\mapsto Z_a(0)\) is completely
monotone without RH. Neither unconditional positivity statement tests horizontal
zero displacement. Every RH criterion below uses \(S_a\) or \(R\), not \(Z_a\).

On compact sets with \(\operatorname{Re} a>0\), the Gaussian decay dominates
all polynomial factors and every fixed complex \(u\). Normal convergence proves
joint analyticity, real-evenness in real \(u\), and
\[
\partial_a S_a(u)=\partial_u^2 S_a(u).
\tag{1}
\]
In particular the differentiated series below are legitimate, including mixed
derivatives and derivatives of the prime formula on compact \(a\)-intervals.

## 2. Audit of the preceding growth theorem and explicit formula

The preceding report's growth proof is sound. Set
\(d=\sup_\rho\delta_\rho\). Symmetry gives \(0\le d\le1/2\). For fixed
\(a>0\), the upper bound \(|S_a(u)|\le C_a e^{du}\), \(u\ge0\), is immediate.
If a smaller exponential rate were valid, the Laplace transform
\[
L_a(z)=\int_0^\infty e^{-zu}S_a(u)\,du
\]
would be holomorphic to the right of a smaller vertical line. Initially for
\(\operatorname{Re}z>d\), absolute convergence gives
\[
L_a(z)=\sum_{\rho\ \mathrm{distinct}}
\frac{m_\rho e^{a w_\rho^2}}{z-w_\rho}.
\]
The right side is normally meromorphic on the whole plane and has a genuine
pole at each distinct \(w_\rho\), with nonzero residue. Thus
\[
\limsup_{u\to\infty}\frac{\log^+|S_a(u)|}{u}=d.
\tag{2}
\]
No attained rightmost zero, absence of cancellation, RH, simplicity, or linear
independence of ordinates is required.

For the Fourier convention \(\widehat f(v)=\int f(t)e^{-ivt}\,dt\), set
\[
k_a(v)=(4\pi a)^{-1/2}e^{-v^2/(4a)},
\]
\[
A_a(u)=\frac1{2\pi}\int_{\mathbb R}e^{-at^2}\cos(ut)
\left[\operatorname{Re}\psi(\tfrac14+\tfrac{it}{2})-\log\pi\right]dt,
\]
\[
P_a(u)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
\{k_a(u-\log n)+k_a(u+\log n)\}.
\]
The formula
\[
S_a(u)=2e^{a/4}\cosh(u/2)+A_a(u)-P_a(u)
\tag{3}
\]
is correct unconditionally. Applying the Guinand–Weil formula to
\(f(t)=e^{-at^2}\cos(ut)\) gives the Gaussian zero sum, including all
horizontal locations. The evenness of the zero multiset identifies this sum
with \(S_a\). The Fourier normalization and pole terms give exactly the
coefficient and sign in (3).

Primary source checked: Bondarenko, Radchenko, Seip, *Fourier Interpolation
with Zeros of Zeta and L-Functions*, Constructive Approximation 57 (2023),
405–461, equation (1.1):
<https://link.springer.com/article/10.1007/s00365-022-09599-w>.
Their normalization is \(e^{-2\pi i x\xi}\), with samples at
\(\pm\log n/(2\pi)\); this converts to (3). Their formula counts full zeros
with multiplicity and does not assume RH.

The preceding archimedean formula
\[
A_a(u)=-(\gamma_E+\log\pi)k_a(u)+
\int_0^\infty\frac{e^{-x}k_a(u)-\tfrac12e^{-x/4}
\{k_a(u-x/2)+k_a(u+x/2)\}}{1-e^{-x}}\,dx
\tag{4}
\]
also has the right constants. Near zero its numerator is \(O(x)\). It must
remain combined; splitting the terms into divergent integrals is invalid.

## 3. Entire positive kernels and derivative Hankel matrices

This section supplies an elementary general theorem that avoids invoking the
Hamburger moment-existence theorem or Carleman's criterion.

Let \(S\) be an even entire function which is real on the real axis. Define
\[
m_n=i^{-n}S^{(n)}(0).
\]
Odd moments vanish, and all moments are real. Then the following are equivalent:

1. The translation kernel \(K(u,v)=S(u-v)\), \(u,v\in\mathbb R\), is positive
   semidefinite for every finite list of points.
2. Every finite real symmetric Hankel matrix
   \(H_N=[m_{j+k}]_{j,k=0}^N\) is positive semidefinite.
3. The kernel is positive semidefinite when points are restricted to any one
   nonempty open interval, however short.

### Proof that all Hankel matrices imply the full kernel

Define the polynomial functional \(\mathcal L(x^n)=m_n\). Hankel positivity
says \(\mathcal L(p\overline p)\ge0\) for every complex polynomial \(p\).
For fixed real \(u_1,\ldots,u_q\) and complex coefficients \(c_1,\ldots,c_q\),
use
\[
p_M(x)=\sum_{\ell=1}^q c_\ell
\sum_{j=0}^M\frac{(iu_\ell x)^j}{j!}.
\]
The resulting nonnegative quadratic form converges as \(M\to\infty\) to
\[
\sum_{\ell,r=1}^q c_\ell\overline{c_r}S(u_\ell-u_r).
\]
To justify the double-series limit, for each \(u,v\) note that
\[
\sum_{j,k\ge0}\frac{|m_{j+k}|\,|u|^j|v|^k}{j!k!}
=\sum_{n\ge0}\frac{|S^{(n)}(0)|(|u|+|v|)^n}{n!}<\infty.
\]
This is simply absolute Taylor convergence of an entire function. Hence no
hidden moment-growth assumption is present.

### Proof that local kernel positivity implies all Hankel matrices

Choose a point in the open interval and a small \(h>0\) so that all points
\(0,h,\ldots,Nh\), translated to that point, remain in the interval. For
\(0\le j,k\le N\), put
\[
B_h(j,k)=(ih)^{-j}(-ih)^{-k}
\sum_{r=0}^j\sum_{s=0}^k
(-1)^{j-r+k-s}\binom jr\binom ks S((r-s)h).
\tag{5}
\]
This is a congruence of the positive translation matrix, so \(B_h\succeq0\).
Successive finite differences and analyticity give
\(B_h(j,k)\to i^{-(j+k)}S^{(j+k)}(0)=m_{j+k}\).
Taking the limit in each finite quadratic form proves \(H_N\succeq0\).
Global positivity trivially gives local positivity. This proves the theorem.

## 4. Application: an origin-based all-orders RH criterion

Apply section 3 to \(S=S_a\) for any **one fixed** \(a>0\). The existing
growth theorem (2) proves that positive definiteness of \(S_a\) is equivalent
to RH. Therefore
\[
\boxed{\mathrm{RH}\iff H_N(a)\succeq0\quad\text{for every }N\ge0,}
\tag{6}
\]
where
\[
m_n(a)=i^{-n}S_a^{(n)}(0)
=\sum_\rho e^{a w_\rho^2}(-iw_\rho)^n.
\tag{7}
\]
Under RH, this becomes the genuine positive moment sequence
\(\sum_\gamma m_\gamma e^{-a\gamma^2}\gamma^n\).

All \(H_N(a)\) are then **strictly** positive definite: a nonzero polynomial
has finitely many real roots, while the zero-ordinate support is infinite.
Thus (6) may equally be stated with strict positive definiteness of all finite
Hankel matrices. The converse uses only semidefiniteness.

If RH fails, for every fixed \(a>0\) there are a finite \(N\) and a finite
coefficient vector \(c\) with
\[
c^*H_N(a)c<0.
\tag{8}
\]
This is a finite-order derivative obstruction at the origin. It is stronger
as a localization statement than merely knowing a distant two-point bound
eventually fails. It is not an effective upper bound on the first failing
degree, and it does not prove the matrices positive arithmetically.

## 5. Arbitrarily small Toeplitz witnesses and an error budget

Using (5), every obstruction (8) produces a negative translation matrix
\([S_a((r-s)h)]_{r,s=0}^N\) for every sufficiently small \(h>0\). Consequently,
if RH fails, the full-zero kernel has finite negative witnesses in **every**
neighborhood of the origin.

A precise finite-difference error estimate follows from repeated integral
representations of differences:
\[
B_h(j,k)=i^{-(j+k)}\int_{[0,1]^{j+k}}
S^{(j+k)}\!\left(h\Big[\sum_{r=1}^j t_r-
\sum_{s=1}^k v_s\Big]\right)dt\,dv.
\]
The empty integral for \(j=k=0\) is interpreted in the usual way. Since
\(|\sum t_r-\sum v_s|\le\max(j,k)\le N\),
\[
|B_h(j,k)-H_N(j,k)|
\le Nh\sup_{|t|\le Nh}|S^{(j+k+1)}(t)|.
\tag{9}
\]
Let \(c^*H_Nc=-\eta<0\), fix \(r>0\), and set
\[
M_r=\max_{1\le n\le2N+1}\sup_{|t|\le r}|S^{(n)}(t)|.
\]
For \(N\ge1\), it suffices to choose
\[
0<h<\min\left\{\frac rN,
\frac{\eta}{2N\max(1,M_r)\|c\|_1^2}\right\}.
\tag{10}
\]
Then \(c^*B_hc<-\eta/2\). If \(N=0\), \(S(0)<0\) itself is already a
one-point negative witness. Since \(B_h\) is a congruence of the Toeplitz
translation matrix, (10) implies that matrix has a negative quadratic form.

For an explicitly computed translation matrix and a coefficient vector \(b\),
uniform entry error \(\varepsilon\) changes its quadratic form by at most
\(\varepsilon\|b\|_1^2\). Thus a computed value below
\(-\varepsilon\|b\|_1^2\) rigorously certifies negativity once the error includes
all zero tails, all prime tails, and the archimedean evaluation error. The
finite-difference coefficients grow like powers of \(1/h\); this creates
ill-conditioning and must not be concealed.

## 6. Two derivative Hankel families using only the heat parameter

Equation (1) implies
\[
m_{2k}(a)=(-1)^k R^{(k)}(a),\qquad m_{2k+1}(a)=0.
\]
The even and odd index blocks of \(H_N\) are therefore the two families
\[
D_N(a)=\big[(-1)^{r+s}R^{(r+s)}(a)\big]_{r,s=0}^N,
\]
\[
E_N(a)=\big[(-1)^{r+s+1}R^{(r+s+1)}(a)\big]_{r,s=0}^N.
\tag{11}
\]
The blocks connecting even and odd indices vanish. Hence for **any one fixed**
\(a>0\),
\[
\boxed{\mathrm{RH}\iff
D_N(a)\succeq0\ \text{and}\ E_N(a)\succeq0
\quad\text{for every }N\ge0.}
\tag{12}
\]
Under RH both families are strictly positive definite: they are Gram matrices
of polynomials in \(\gamma^2\), with positive weights respectively
\(e^{-a\gamma^2}\) and \(\gamma^2 e^{-a\gamma^2}\); the support is infinite and
contains no zero ordinate.

Low-order necessary conditions include
\[
R(a)\ge0,\quad -R'(a)\ge0,\quad R''(a)\ge0,
\]
\[
R(a)R''(a)-R'(a)^2\ge0,
\qquad R'(a)R'''(a)-R''(a)^2\ge0.
\tag{13}
\]
These conditions are strictly positive where they are determinants under RH,
but checking finitely many conditions does not establish the all-orders
statement (12).

Substitution of (3) at \(u=0\) gives the exact arithmetic function
\[
R(a)=2e^{a/4}+A_a(0)
-2\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}k_a(\log n).
\tag{14}
\]
Formula (12) is thus a prime-only derivative-matrix criterion, with all prime
powers and the archimedean term retained. Differentiation is legitimate on
compact \(a\)-intervals inside \((0,\infty)\). Establishing its positive
semidefiniteness from arithmetic without using RH remains the open step.

## 7. A completely monotone origin-trace criterion

Fix any \(a_0>0\). Then
\[
\boxed{\mathrm{RH}\iff
t\longmapsto R(a_0+t)\ \text{is completely monotone on }[0,\infty).}
\tag{15}
\]
Equivalently, \((-1)^kR^{(k)}(a)\ge0\) for every \(k\ge0\) and all
\(a>a_0\), with continuity at \(a_0\).

Under RH,
\[
R(a_0+t)=\sum_\gamma m_\gamma e^{-a_0\gamma^2}e^{-t\gamma^2},
\]
so the assertion follows by termwise differentiation.

Conversely, Bernstein's theorem supplies a finite positive measure \(\nu\)
on \([0,\infty)\) such that
\(R(a_0+t)=\int e^{-t\lambda}d\nu(\lambda)\). It is finite because the
trace is continuous and finite at \(t=0\). Its Laplace transform is the
Stieltjes transform
\[
F(z)=\int_{[0,\infty)}\frac{d\nu(\lambda)}{z+\lambda},
\]
holomorphic on \(\mathbb C\setminus(-\infty,0]\). Initially for
\(\operatorname{Re}z>1/4\), absolute convergence of the full-zero series gives
\[
F(z)=\sum_\rho\frac{e^{a_0 w_\rho^2}}{z-w_\rho^2}.
\tag{16}
\]
The right side continues normally meromorphically to the whole plane. At a
given square \(w_\rho^2\), the only possible collisions are \(w\) and \(-w\),
and their residues add to a positive integer multiple of
\(e^{a_0w_\rho^2}\); they cannot cancel. If \(\delta_\rho\ne0\), then
\(\operatorname{Im}(w_\rho^2)=2\delta_\rho\gamma_\rho\ne0\). This is a
genuine pole in the Stieltjes holomorphy domain, contradicting analytic
continuation and the meromorphic identity theorem. Hence every \(\delta\)
vanishes.

This criterion uses the standard Bernstein representation theorem. Original
primary provenance:

- S. Bernstein, *Sur les fonctions absolument monotones*, Acta Mathematica
  52 (1929), 1–66, DOI 10.1007/BF02592679:
  <https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5418-11511_2007_Article_BF02592679.pdf>.
- D. V. Widder, *Necessary and sufficient conditions for the representation
  of a function as a Laplace integral*, Transactions AMS 33 (1931), 851–892,
  DOI 10.1090/S0002-9947-1931-1501621-6.

The CM criterion is not a novelty claim. Similar classical real-zero,
moment-positivity, and spectral-transform criteria exist. The present proof
states exactly how this full-zero Gaussian family specializes them.

## 8. Derivative zero-tail bounds for matrix certification

Suppose the same explicit count estimate used in the preceding report holds:
\(N(y+1)-N(y)\le7\log(y+2)\) for \(y\ge2\). For any integer \(r\ge0\),
\(T\ge2\) with \(T^2\ge r/a\), and real \(u\),
\[
\left|\sum_{|\gamma|>T}w_\rho^r
e^{aw_\rho^2+uw_\rho}\right|
\le
\frac{14e^{a/4+|u|/2}}{(1-e^{-2a})^2}
(T^2+\tfrac14)^{r/2}e^{-aT^2}\log(T+2).
\tag{17}
\]
This applies directly to derivative moments at \(u=0\), and on bounded
\(u\)-windows when using finite differences.

Proof: let
\(f(t)=(t^2+1/4)^{r/2}e^{-at^2}\). For \(t\ge T\),
\[
\log\frac{f(t)}{f(T)}
\le \frac r2\log\frac{t^2}{T^2}-a(t^2-T^2)
\le-\frac a2(t^2-T^2).
\]
The last inequality uses \(r/T^2\le a\) and \(\log x\le x-1\). On the
unit interval beginning at \(T+k\), this is bounded by
\(f(T)e^{-2ak}\), since \((T+k)^2-T^2\ge4k\). Multiply by the local
count bound, use \(\log(T+k+2)\le(1+k)\log(T+2)\), double for positive
and negative ordinates, and sum the geometric derivative series. The factor
\(e^{a/4+|u|/2}\) controls horizontal displacement without RH.

The count estimate is an explicitly quoted input, not a new unconditional
numerical constant proved here. Formula (17) remains valid with any separately
verified local count constant in place of 7.

## 9. What remains unresolved

### Additional quantitative refinement: horizontal blindness improves

Selberg's uniform density estimate as stated in Ford–Zaharescu,
*On the distribution of imaginary parts of zeros of the Riemann zeta
function*, Lemma 2, is
\[
N(\sigma,T)\ll T^{1-(\sigma-1/2)/4}\log T,
\quad 1/2\le\sigma\le1.
\]
Here their count uses \(|\gamma|\le T\). Primary author-hosted text:
<https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf>.
By zero symmetry and layer-cake integration, this implies
\[
B(T):=\sum_{0<\gamma\le T}\delta_\rho^2
\ll T\log T\int_0^{1/2}s e^{-s\log T/4}\,ds
\ll\frac T{\log T}.
\tag{18}
\]
No RH is used. This consequence should be attributed to the quoted classical
density estimate, not presented as a new density theorem.

Let \(D_j(a)=\sum_\rho\delta_\rho^2\gamma_\rho^j e^{-a\gamma_\rho^2}\)
for \(j=0,2\). Stieltjes integration by parts in (18), splitting the integrals
at \(a^{-1/4}\), gives
\[
D_0(a)\ll\frac{a^{-1/2}}{\log(1/a)},\qquad
D_2(a)\ll\frac{a^{-3/2}}{\log(1/a)}\quad(a\downarrow0).
\tag{19}
\]
For the second integral use the absolute derivative of
\(t^2 e^{-at^2}\); its sign change creates no issue. The bounded low-height
part is absorbed in the displayed bounds.

Pairing horizontal reflections in the same Gaussian trace gives
\[
|S_a(u)-Z_a(u)|
\le e^{a/4+|u|/2}
\left[(a+u^2/2)D_0(a)+2a^2D_2(a)\right].
\tag{20}
\]
Indeed \(|e^{a\delta^2}-1|\le a\delta^2e^{a\delta^2}\), and the integral
Taylor remainder for cosh yields
\(|\cosh z-1|\le |z|^2 e^{|\operatorname{Re}z|}/2\), with
\(z=\delta(u+2ia\gamma)\). Therefore, for each fixed \(C\),
\[
\boxed{S_a(u)-Z_a(u)=
O_C\left(\frac{\sqrt a}{\log(1/a)}\right),
\qquad |u|\le C\sqrt a.}
\tag{21}
\]
This improves the preceding report's \(O_C(\sqrt a\log(1/a))\) error by two
logarithmic factors. It quantitatively strengthens the limitation of these
small-window measurements rather than proving RH.

### Independent audit of the harmonic agent's heat trace constant

Put \(r(t)=\operatorname{Re}\psi(1/4+it/2)-\log|t/2|\). Stirling's formula
gives \(r(t)=O(t^{-2})\) at infinity; the logarithmic singularity at zero is
integrable. Continuous log Gamma on the vertical line gives, for any real
\(c>0\),
\[
\int_0^R\operatorname{Re}\psi(c+ix)\,dx
=\operatorname{Im}\log\Gamma(c+iR),
\]
and Stirling gives
\[
\operatorname{Im}\log\Gamma(c+iR)
=R\log R-R+(c-1/2)\pi/2+O(R^{-1}).
\]
Subtracting \(\int_0^R\log x\,dx\), taking the limit, changing variables
\(t=2x\), and doubling yields
\(\int_{\mathbb R}r(t)dt=2\pi(c-1/2)=-\pi/2\) at \(c=1/4\).
The weighted difference
\(\int(e^{-at^2}-1)r(t)dt=O(\sqrt a)\), by splitting at \(a^{-1/2}\).
Thus
\[
A_a(0)=
\frac{\log(1/a)-\gamma_E-2\log(4\pi)}{4\sqrt{\pi a}}
-\frac14+O(\sqrt a).
\]
The pole term is \(2+O(a)\), and the prime term is exponentially small:
splitting each Gaussian exponent in half bounds it by a finite
\(a_0\)-dependent sum times
\(a^{-1/2}e^{-(\log2)^2/(8a)}\). Hence
\[
R(a)=
\frac{\log(1/a)-\gamma_E-2\log(4\pi)}{4\sqrt{\pi a}}
+\frac74+O(\sqrt a).
\]
Combining (21) at \(u=0\) gives the unconditional ordinate heat trace
\[
\boxed{\sum_\rho e^{-a\gamma_\rho^2}=
\frac{\log(1/a)-\gamma_E-2\log(4\pi)}{4\sqrt{\pi a}}
+\frac74+O(\sqrt a).}
\tag{22}
\]
The constant \(7/4\) counts both signs of each ordinate; one-sided conventions
must halve the formula. This is independently audited, but literature novelty
has not been established.

### Fixed-order Gaussian positivity is automatic for narrow widths

For each fixed finite \(N\), the full-zero derivative matrix \(H_N(a)\) is
strictly positive definite for all sufficiently small \(a>0\), **without RH**.
This is a useful limitation of finite tests.

Let \(M_n(a)=\sum_\rho \gamma_\rho^n e^{-a\gamma_\rho^2}\), with odd moments
zero by conjugation. The Riemann–von Mangoldt count and Stieltjes integration
by parts give, for fixed \(k\ge0\),
\[
M_{2k}(a)\sim
\frac{\Gamma(k+1/2)}{4\pi}
a^{-k-1/2}\log(1/a).
\tag{23}
\]
For example, the leading count-density integral is
\(\pi^{-1}\int_0^\infty t^{2k}e^{-at^2}\log(t/(2\pi))dt\); the count error
is of smaller order by integration by parts. The case \(k=0\) agrees with
(22).

The paired horizontal estimate extends to complex \(|u|\le C\sqrt a\).
Indeed the base factor \(e^{iu\gamma}\) contributes at most
\(e^{C\sqrt a|\gamma|}\), which is absorbed by
\[
e^{-a\gamma^2+C\sqrt a|\gamma|}
\le e^{C^2/2}e^{-a\gamma^2/2}.
\]
The cosh Taylor remainder depends on
\(\operatorname{Re}(\delta(u+2ia\gamma))=\delta\operatorname{Re}u\), so
the same reasoning as (20) applies. Cauchy's derivative estimate therefore
gives, for each fixed \(n\),
\[
m_n(a)-M_n(a)=
O_n\left(\frac{a^{(1-n)/2}}{\log(1/a)}\right).
\tag{24}
\]
Alternatively, using only the strip bound \(|\delta|\le1/2\) gives the weaker
\(O_n(a^{(1-n)/2}\log(1/a))\), which already suffices for the following limit.

Let \(J_a=\operatorname{diag}(1,a^{1/2},\ldots,a^{N/2})\). Equations
(23)–(24) imply entrywise, hence in finite-dimensional matrix norm,
\[
\frac{\sqrt a}{\log(1/a)}J_a H_N(a)J_a
\longrightarrow C_N,
\quad C_N(j,k)=\frac1{4\pi}\int_{\mathbb R}x^{j+k}e^{-x^2}dx.
\tag{25}
\]
The limit is strictly positive definite because every nonzero polynomial has
positive square integral against the Gaussian density. Its least eigenvalue
is positive; a sufficiently small matrix-norm perturbation preserves strict
positivity. Congruence by the invertible \(J_a\) and the positive scalar factor
then proves the theorem.

Consequently, if RH fails and \(n(a)\) denotes the least degree for which
\(H_{n(a)}(a)\) fails to be positive semidefinite, then \(n(a)\to\infty\) as
\(a\downarrow0\). This does not say any fixed-width all-orders matrix family
is positive. It says every fixed finite portion becomes positive in a
specific parameter limit regardless of RH.

### Verification boundary

All implications in sections 3–8 are derived rigorously on paper under the
stated classical zero facts. They provide an all-orders local harmonic
criterion and finite negativity certificates, not an arithmetic positivity
proof. No finite positive test certifies every matrix size or every smoothing
parameter. No RH proof, universal simplicity, or literature novelty is claimed.

The most useful exact verification target for Lean is the generic finite
positive-weight kernel algebra, the derivative block decomposition, or a
finite error-budget lemma. Formalizing the full zeta explicit formula,
normal-convergence theorems, meromorphic continuation, and Bernstein theorem
requires substantial analytic infrastructure and must be distinguished from
verifying those finite algebraic consequences.


## Server verification record

All four new modules compiled successfully on the Lean server (Lean 4.33.0-rc2). Verification job `job_JaNMU6Ybru2yIFCqSw9fvRQ2TlMOMWYd` succeeded with exit code 0 and verified=true. The run imported all four modules and executed 43 public-theorem axiom checks. Publication is subject to the introducing checkpoint audit. Infinite analytic arguments in these appendices remain paper proofs, not Lean declarations.
