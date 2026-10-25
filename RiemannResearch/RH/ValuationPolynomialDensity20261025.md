# Weighted polynomial density and prime-valuation completeness

**Status (October 25, 2026):** The geometric coordinate-density theorem and the complete physical valuation-polynomial basis have passed saved-source checks on the Lean server. Final aggregate validation and publication are certified by the containing checkpoint. The broader exponential-weight theorem, explicit product approximation rate, and strengthened cofactor lower bound below are ordinary mathematical proofs; those extensions are not claimed as newly formalized. This continues commit `bbfdc8fa28da9f1aa7fe375a8a7c798bf40cea3e`. The notation follows the repository: `E_(p,0)` is the first centered polynomial mode, `E_(p,j+1)` are the higher modes, and `primePowerFrame (k+1)` is the centered wavelet indexed below by `k`.

The main new mathematical conclusion is completeness of the polynomial modes in the already defined physical valuation space. The repository already has complete wavelet and exact-valuation-level bases for that space. Completeness is therefore transferred through established physical bases, rather than used to redefine the space.

## 1. A general density theorem

Let `K` be either the real or complex numbers. Suppose that a scalar sequence `(c_k)_{k>=0}` satisfies

\[
c_k\ne0,\qquad |c_k|\le C R^{-k}\quad(k\ge0)
\]

for constants `C>0` and `R>1`. Define vectors in ordinary counting-measure `ell^2(N)` by

\[
u_m(k)=c_k k^m,\qquad m=0,1,2,\ldots,
\]

using `0^0=1`. Then

\[
\boxed{\overline{\operatorname{span}\{u_m:m\ge0\}}=\ell^2(\mathbb N).}
\]

All these vectors belong to `ell^2`, since an exponential dominates every fixed polynomial.

### Generating-function proof

Let `x` be orthogonal to every `u_m`. In the complex case use `b_k=conj(x_k)c_k`; in the real case use `b_k=x_k c_k` and regard these as complex numbers. Orthogonality gives

\[
\sum_{k=0}^{\infty} b_k k^m=0\qquad(m\ge0).
\]

Every displayed sum is absolutely convergent by Cauchy–Schwarz. Define

\[
H(z)=\sum_{k=0}^{\infty}b_kz^k.
\]

For every `0<=r<R`, Cauchy–Schwarz gives the uniform bound

\[
\sum_{k=0}^{\infty}|b_k|r^k
\le C\|x\|_2\left(\sum_{k=0}^{\infty}(r/R)^{2k}\right)^{1/2}
=\frac{C\|x\|_2}{\sqrt{1-(r/R)^2}}.
\]

Thus `H` is holomorphic on the disk `|z|<R`. Derivative series converge locally uniformly there as well: for `0<r<s<R`, the extra factor `k^m(r/s)^k` is bounded. Since `1<R`, termwise differentiation at `1` is legitimate.

There are two equivalent ways to finish. With `D=z d/dz`, one has

\[
(D^mH)(1)=\sum_k b_k k^m=0.
\]

The triangular identity

\[
D^m=\sum_{j=0}^m S(m,j)z^j\frac{d^j}{dz^j},\qquad S(m,m)=1,
\]

shows inductively that every ordinary derivative `H^(j)(1)` vanishes. Alternatively, the falling factorial `k(k-1)...(k-j+1)` is a polynomial in `k`, so the moment equations directly give

\[
H^{(j)}(1)=\sum_k b_k k(k-1)\cdots(k-j+1)=0.
\]

The Taylor expansion at `1` is therefore zero. The identity theorem on the connected disk `|z|<R` implies `H=0` throughout that disk. Consequently `b_k=H^(k)(0)/k!=0`. Since every `c_k` is nonzero, every `x_k` is zero. The orthogonal complement of the polynomial span is zero, so its closed span is all of `ell^2`.

This proves the density assertion for more than the exact geometric weights. If some `c_k` vanish, the same argument gives density in the coordinate subspace supported on `{k:c_k != 0}`.

## 2. An elementary constructive proof for the actual geometric weights

Assume now

\[
c_k=Cp^{-k},\qquad C\ne0,\qquad p\ge2.
\]

Write `q=1/p <= 1/2`. For `N>=0`, introduce the degree-`N` polynomial

\[
A_N(t)=\prod_{r=2}^{N+1}\left(1-\frac{t}{r}\right).
\]

The empty product for `N=0` is `1`. Equivalently, if

\[
P_n(t)=\sum_{i=0}^n(-1)^i\binom ti
=\prod_{r=1}^n(1-t/r),
\]

where binomial coefficients with real argument mean the falling-factorial polynomials, then

\[
A_N(t)=\frac1{N+1}\sum_{n=0}^NP_n(t).
\]

The product representation immediately gives

\[
A_N(0)=1,\qquad A_N(1)=\frac1{N+1},\qquad
A_N(k)=0\quad(2\le k\le N+1),
\]

and, for `k>=N+2`,

\[
A_N(k)=\frac{(-1)^N}{N+1}\binom{k-2}{N}.
\]

The negative-binomial geometric identity is

\[
\sum_{k=N+2}^{\infty}q^k\binom{k-2}{N}
=\frac{q^{N+2}}{(1-q)^{N+1}}.
\]

It follows either by differentiating the geometric series `N` times, or by induction using the Cauchy product of `N+1` copies of the absolutely convergent geometric series. Therefore

\[
\begin{aligned}
\left\|\bigl(c_kA_N(k)\bigr)_{k\ge0}-C e_0\right\|_1
&=\frac{|C|}{N+1}
\left(q+\frac{q^{N+2}}{(1-q)^{N+1}}\right)\\
&=\frac{|C|q}{N+1}
\left(1+\left(\frac q{1-q}\right)^{N+1}\right)\\
&\le\frac{|C|}{N+1}.
\end{aligned}
\]

Since the counting-measure `ell^2` norm is at most the `ell^1` norm,

\[
\boxed{\left\|C^{-1}(c_kA_N(k))_k-e_0\right\|_2
\le\frac1{N+1}.}
\]

Thus the first coordinate vector has explicit polynomial approximants with a uniform rate that includes the borderline prime `p=2`. This avoids an analytic identity theorem and avoids central-binomial asymptotics.

To deduce density, let `W` be the closed span of the weighted polynomials. The preceding construction shows `e_0 in W`. Let `S` be the right shift,

\[
(Sx)_0=0,\qquad (Sx)_k=x_{k-1}\quad(k\ge1).
\]

This is a bounded linear isometry. For any polynomial `P`, write `w(P)_k=Cp^{-k}P(k)`. The exact identity

\[
\boxed{S w(P)=p\,w(P(\,\cdot-1))-pC P(-1)e_0}
\]

shows that `S` sends the polynomial span into `W`. Continuity then shows `S(W) subset W`. Hence `e_j=S^j e_0 in W` for every `j`. Finite-support vectors are dense in `ell^2`, proving `W=ell^2`.

This is a constructive existence proof for every coordinate, not only for `e_0`: if `w(P)` approximates `e_j` and `v` is a polynomial approximant to `e_0`, replace the right-hand side above by

\[
p\,w(P(\,\cdot-1))-pC P(-1)v.
\]

Its error from `e_(j+1)` is at most

\[
\|w(P)-e_j\|_2+|pC P(-1)|\,\|v-e_0\|_2.
\]

The displayed `1/(N+1)` bound lets one choose the second degree explicitly after the first polynomial has been chosen. The construction can have large coefficients; it proves density without asserting coefficient stability.

## 3. The actual Q valuation space

Fix a prime `p` and let

\[
Q(n)=\frac1{\zeta(2)n^2}\quad(n\ge1),\qquad K(n)=v_p(n),\qquad q=p^{-2}.
\]

The valuation law is exactly

\[
Q(K=k)=(1-q)q^k\quad(k\ge0).
\]

Let `V_p` denote the **full** closed subspace of `L^2(Q)` consisting of functions of `K`, and let `V_p^0` denote its centered subspace. The normalized exact-level indicators

\[
B_{p,k}=\frac{1_{K=k}}{\sqrt{(1-q)q^k}}
\]

form a complete orthonormal basis of `V_p`: they identify that subspace with `ell^2` under the geometric valuation law, and finite truncations converge in squared norm by summability.

Define centered tail wavelets

\[
W_{p,k}=\frac{1_{K\ge k+1}-q1_{K\ge k}}{\sqrt{q^{k+1}(1-q)}}.
\]

They have mean zero and norm one. If `j<k`, then `W_(p,j)` is constant on the support of `W_(p,k)`, so their inner product is zero. The recurrence

\[
1_{K\ge k+1}=q1_{K\ge k}+\sqrt{q^{k+1}(1-q)}W_{p,k}
\]

starting with `1_(K>=0)=1` shows that every tail indicator, hence every exact-level indicator, is in the finite span of `1,W_(p,0),W_(p,1),...`. Consequently

\[
\boxed{\{1,W_{p,0},W_{p,1},\ldots\}\text{ is a complete ONB of }V_p,}
\]

and `{W_(p,k)}` is a complete ONB of `V_p^0`. This supplies the physical identification explicitly, rather than defining the physical space to be the wavelet closure.

Let

\[
U_p:\ell^2(\mathbb N)\longrightarrow V_p^0,
\qquad U_px=\sum_kx_kW_{p,k}.
\]

Orthonormality and completeness make `U_p` a surjective linear isometry. In particular,

\[
c_{p,k}=\langle K,W_{p,k}\rangle_Q
=\frac{p^{-k}}{\sqrt{p^2-1}}.
\]

Define the all-order monomial lifts by

\[
M_{p,m}=U_p\bigl((k^m c_{p,k})_k\bigr).
\]

The density theorem and the isometry give

\[
\boxed{\overline{\operatorname{span}\{M_{p,m}:m\ge0\}}=V_p^0.}
\]

For clarity, these lifts are actual polynomials in the valuation. At an integer valuation `t>=0`, only the terms `k<=t` in the wavelet series survive, and their values give

\[
\boxed{M_{p,m}(t)=\sum_{k=0}^{t-1}k^m-\frac{t^m}{p^2-1}.}
\]

The sum is empty at `t=0`, again using `0^0=1`. This is a centered polynomial of degree `m+1`, with leading coefficient `1/(m+1)`. In particular,

\[
M_{p,0}=K-\frac1{p^2-1}.
\]

Gram–Schmidt produces normalized innovations `E_(p,j)` from `M_(p,j)`. The established finite-span equality is the transfer mechanism:

\[
\operatorname{span}(E_{p,0},\ldots,E_{p,m})
=\operatorname{span}(M_{p,0},\ldots,M_{p,m}).
\]

Then equality of the closed unions proves

\[
\boxed{\{1,E_{p,0},E_{p,1},\ldots\}\text{ is a complete ONB of }V_p.}
\]

No new summability claim is hidden in this step: the existing unconditional-series theorem and the newly established closed-span equality are precisely the ingredients.

The constructive proof transfers as well. If `A_N(t)=sum_m a_(N,m)t^m`, the finite physical polynomial combination
\[\sqrt{p^2-1}\sum_m a_{N,m}M_{p,m}\]
approximates the first centered normalized wavelet `primePowerFrame p hp 1` in actual Q norm with error at most `1/(N+1)`. Writing `v=v_p(n)` and `d=p^2-1`, its positive physical coordinates are explicitly
\[B_{p,N}(n)=\sqrt d\left(\sum_{k=0}^{v-1}A_N(k)-\frac{A_N(v)}d\right).\]
The norm estimate includes the entire infinite valuation tail. This follows by applying the isometry `U_p` to the normalized coordinate approximation in Section 2. At `p=2` this wavelet is the already legal parity unit. The approximants are ambient valuation polynomials; this statement does not assert that each approximant is legal.


## 4. Exact consequence for the floor-log target

Write `n=p^K A`, where `p` does not divide `A`. Under `Q`, `K` and `A` are independent, with

\[
Q(A=a)=\frac{1}{\zeta(2)(1-p^{-2})a^2}\quad(p\nmid a).
\]

Indeed, multiplying this probability by `(1-p^-2)p^(-2k)` gives `Q(p^k a)` exactly. Set

\[
L_p(A)=\lfloor\log_p A\rfloor,\qquad F_p(n)=\lfloor\log_p n\rfloor.
\]

The arithmetic identity is

\[
F_p=K+L_p(A).
\]

All these variables lie in `L^2(Q)`, since logarithmic growth is square integrable against `n^-2`. Define

\[
\mu_p=\mathbb E_QF_p,\qquad R_p=L_p(A)-\mathbb E_QL_p(A).
\]

Independence implies `R_p` is orthogonal to **every** element of `V_p`, not merely to each finite family of wavelets. Therefore

\[
P_{V_p}F_p=\mu_p+K-\frac1{p^2-1},\qquad
F_p=P_{V_p}F_p+R_p.
\]

With the Gram–Schmidt sign convention taking the first innovation in the direction of `M_(p,0)`,

\[
E_{p,0}=\frac{p^2-1}{p}\left(K-\frac1{p^2-1}\right),
\]

because `Var(K)=p^2/(p^2-1)^2`. Hence

\[
\boxed{F_p=\mu_p1+\frac{p}{p^2-1}E_{p,0}+R_p,\qquad R_p\perp V_p.}
\]

In this normalization all the floor-log coefficients along `E_(p,j+1)` for `j>=0` are zero. The complete wavelet coefficient vector of its centered valuation component is `(c_(p,k))_k`, whose squared norm is `p^2/(p^2-1)^2`.

In particular,

\[
F_2=\mu_2 1+\frac23E_{2,0}+R_2,\qquad
F_3=\mu_3 1+\frac38E_{3,0}+R_3.
\]

The cofactor residual does not vanish. The cofactor events `A=1` and `A=p+1` have positive probabilities and give distinct values `L_p=0` and `L_p=1`. Quantitatively, writing

\[
u_p=\frac1{\zeta(2)(1-p^{-2})},
\]

the two events have masses `alpha=u_p` and `beta=u_p/(p+1)^2`. For every real `m`,

\[
\alpha m^2+\beta(1-m)^2\ge\frac{\alpha\beta}{\alpha+\beta}.
\]

Applying this at `m=E L_p` yields the unconditional lower bound

\[
\boxed{\|R_p\|_Q^2\ge
\frac1{\zeta(2)(1-p^{-2})((p+1)^2+1)}>0.}
\]

Thus even the complete valuation-polynomial family cannot approximate all of `F_p`: its best squared error is exactly `||R_p||_Q^2`. Completeness removes a possible missing valuation component; it leaves the actual cofactor component intact.

For any square-summable signed polynomial coefficients `a_j` and real scalar `b`, the complete error identity is

\[
\left\|F_p-b1-\sum_{j\ge0}a_jE_{p,j}\right\|_Q^2
=(\mu_p-b)^2
+\left(\frac{p}{p^2-1}-a_0\right)^2
+\sum_{j\ge1}a_j^2+\|R_p\|_Q^2.
\]

The more general signed-discrepancy identity applies to any other target with arbitrary polynomial coefficients. The simplification here is special to the floor-log target. It makes explicit why the higher-mode infinite series can only add squared discrepancy when approximating this particular target inside the valuation space.

## 5. What remains independent of completeness

Let `H` be the closed squarefree legal span in the actual `L^2(Q)` space, and let

\[
C=\overline{H+\mathbb R1}
\]

be the enlarged closure with constants. The preceding arguments concern an ambient valuation subspace. The already verified theorem `primePowerProjectionUnit_not_mem_closureWithConstants` proves the stronger obstruction

\[
\boxed{E_{p,0}\notin C.}
\]

Thus a proposed proof that puts the first valuation mode and the cofactor residual separately into `C` cannot succeed. They must cancel after projection onto `C^perp`.

Write `alpha_p=p/(p^2-1)>0`, and define the two actual legal defects

\[
e_p=P_{C^\perp}E_{p,0}\ne0,\qquad r_p=P_{C^\perp}R_p.
\]

Because `1 in C`, the exact membership condition is

\[
\boxed{F_p\in C\iff r_p=-\alpha_p e_p.}
\]

In particular, `F_p in C` would force `R_p notin C`. This is nontrivial cancellation of two nonzero legal defects. The complete signed error is

\[
\operatorname{dist}(F_p,C)^2
=\alpha_p^2\|e_p\|_Q^2+\|r_p\|_Q^2
+2\alpha_p\langle e_p,r_p\rangle_Q.
\]

Orthogonality of `R_p` to the **ambient valuation space** does not imply orthogonality of these two **legal defects** after projection. Discarding the cross term would discard the only possible cancellation mechanism.

For raw legal membership, the constant defect also remains:

\[
F_p\in H\iff
\mu_pP_{H^\perp}1+\alpha_pP_{H^\perp}E_{p,0}
+P_{H^\perp}R_p=0.
\]

The existing theorem `riemannHypothesis_of_two_targets_mem_closureWithConstants` supplies the precise arithmetic goal for the two floor-log targets: establish `F_2 in C` and `F_3 in C`, then apply that verified bridge to RH. In the present coordinates, those two membership goals become

\[
r_2=-\frac23e_2,\qquad r_3=-\frac38e_3.
\]

Polynomial completeness establishes neither equality.

For the constant target itself, if `(u_j)` is a complete ONB of the **raw legal** subspace `H`, legal Parseval saturation is

\[
1\in H
\iff\|P_H1\|_Q^2=1
\iff\sum_j|\langle1,u_j\rangle_Q|^2=1.
\]

Replacing that legal family by the complete ambient valuation basis changes the subspace and does not prove this condition. Likewise, saturation for `1` in `C` is automatic because `1 in C`, and therefore does not supply the required saturation in `H`.

The independent arithmetic work is to prove the two exact cancellation identities in `C^perp`, or another separately justified criterion that yields raw legal Parseval saturation. Completeness removes a functional-analytic gap in the valuation expansion; the checked nonmembership theorem proves why the remaining task cannot be solved by componentwise ambient approximation.

## 6. Remaining research after the completeness theorem

1. Formalize the explicit product-polynomial approximation and its uniform `1/(N+1)` Q-norm bound. Its complete ordinary proof is given above.
2. Turn the shift recursion into quantitative polynomial approximants for arbitrary specified finite wavelet heads; add certified tail data to approximate a general valuation observable. The coefficients may grow, and no stability bound is asserted here.
3. Establish the exact legal defect cancellations for `p=2` and `p=3`, retaining both defect norms and their signed cross term. These are the unresolved arithmetic providers for the existing two-target RH criterion.
4. Develop finite/infinite tensor completeness or higher closed Meixner formulas when they serve a concrete subsequent argument. Neither is needed for the one-prime basis theorem proved here, and neither automatically establishes legal membership.

The physical space is defined by coordinate constancy on valuation fibers, not by the closure of the polynomial dictionary.

## 7. Lean source map and verification ledger

The implementation is split by mathematical responsibility:

- `Analysis/GeometricPolynomialDensity.lean`: `eq_zero_of_geometric_polynomial_moments`, using the existing analytic exponential-moment determinacy theorem. All polynomial and exponential integrability hypotheses are discharged for `0 < r <= 1/2`.
- `Analysis/GeometricMonomialCoordinates.lean`: actual `lp (fun _ : Nat => Real) 2` vectors, zero annihilator, dense span, and invariance under nonzero common normalization. Main declaration: `geometricMonomial_scaled_span_dense`.
- `RH/QPrimePowerPolynomialCompleteness.lean`: `valuationPolynomial_span_dense`, `valuationPolynomialHilbertBasis`, unconditional reconstruction, and complete signed Parseval on the physically defined valuation space. The only prime-specific assumption is that `p` is prime.
- `RH/QPrimePowerLegalCancellation.lean`: exact target decomposition, signed legal defect energy, the membership/saturation cancellation equivalences, and the necessary nonzero cofactor defect and strictly negative defect pairing under legal target membership.

The scalar module built successfully during `job_8iCxu0kFMgh23AnKLCNQJPWdOD1ttqlK` (reported module build time 446 seconds), although that overall import/axiom-audit request timed out at 600.035 seconds before completion. The earlier 120- and 600-second requests also timed out; they are not counted as successful audits. The subsequent batch `job_XbKMdeC-ZLI-AHwgDw1FAQSP9h3mLU14` returned local elaboration errors after 1065.295 seconds. The explicit real inner-product annotation, typed span-membership proof, and prime-proof rewrite argument repair those errors. A failed tactic or timeout is not a mathematical refutation.

Successful saved-source checks:

| File | Server job | Result | Reported duration |
|---|---|---|---|
| GeometricMonomialCoordinates.lean | `job_CPZTKwbl3x5kNFwDNCLaUgRrWDeLh2N2` | exit 0, verified=true | 76.792 s |
| QPrimePowerPolynomialCompleteness.lean | `job_lMmzttCgATJm3PNHO7vHzNP9fsfo2I9I` | exit 0, verified=true | 577.019 s |
| QPrimePowerLegalCancellation.lean | `job_yDwZAHgJrALb6Vux127ksyO0fFqSApZZ` | exit 0, verified=true | 583.620 s |

The physical-space request includes substantial dependency unpacking. These durations are complete server verification-request durations, not isolated kernel-checking timings. The reported queue delays for these successful jobs were below 0.01 seconds; 30–60 second polling intervals are separate. Workspace-opening latency was not measured. The import/axiom audit did not reach its final `#print axioms` commands, so it is not reported as a successful axiom-output audit.

The containing server checkpoint is the aggregate validation and publication gate. An isolated file check does not certify an unrelated repository module or a later integrated source revision. No density, RH, or legal-target membership hypothesis is hidden in the new completeness theorem. The two arithmetic cancellation providers in Section 5 remain open.
