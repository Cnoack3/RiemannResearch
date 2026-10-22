# Exact Cauchy smoothing of the actual zero Gram

This is a paper-level result. The finite Schur transport candidate is separate;
the Fourier representation below has not been Lean formalized.

## 1. A finite correlation Schur map preserves both frame bounds

Let `S` be a finite Hermitian positive semidefinite matrix with `S_nn=1`.
Write `Psi_S(A)=S odot A` for entrywise multiplication. The Schur product
theorem implies that `Psi_S` is positive, and the diagonal normalization gives
`Psi_S(I)=I`. Consequently, for every Hermitian `H` and real `h_- <= h_+`,

\[
h_-I\preceq H\preceq h_+I
\quad\Longrightarrow\quad
h_-I\preceq S\odot H\preceq h_+I.                 \tag{1}
\]

Indeed apply Schur positivity separately to `H-h_-I` and `h_+I-H`.
In particular, for Hermitian `H`,

\[
\|S\odot H-I\|\leq\|H-I\|.                    \tag{2}
\]

Thus no frame error is amplified. Complete positivity also follows from a
Gram factorization of `S`, but is unnecessary for the finite proof of (1).

For positive integer frequencies, use the exact correlation kernel

\[
S_{nm}=\operatorname{sech}\!\left(\frac{\log m-\log n}{2}\right)
       =\frac{2\sqrt{nm}}{n+m}.                    \tag{3}
\]

Its positivity has the elementary Laplace Gram proof

\[
S_{nm}=\int_0^\infty
    (\sqrt{2n}e^{-nt})(\sqrt{2m}e^{-mt})\,dt,
\qquad S_{nn}=1.
\]

The quadratic form is the integral of
`|sum_n c_n sqrt(2n) exp(-nt)|^2`, hence is nonnegative.
Every original coordinate, including composites, is retained.

## 2. Actual zero Gram and its positive smoothed law

List the actual nontrivial zeros under the selected ordinate cutoff as
`rho_j=beta_j+i gamma_j`, counting each multiplicity. Let `N` be the number
of entries and suppose `N>0`. Put `a_j=beta_j-1/2` and `x_n=log n`.
With the usual complex Gram convention, the exact hyperbolic matrix is

\[
H_{nm}=\frac1N\sum_j
  e^{i\gamma_j(x_n-x_m)}\cosh(a_j(x_n-x_m)).       \tag{4}
\]

For row analyses `C_jn=N^{-1/2} exp(-i gamma_j x_n) cosh(a_j x_n)` and
`Q_jn=N^{-1/2} exp(-i gamma_j x_n) sinh(a_j x_n)`, the identity
`H=C^*C-Q^*Q` follows from
`cosh(s-t)=cosh(s)cosh(t)-sinh(s)sinh(t)`.
The negative sinh square is therefore retained exactly in (4).

For every real `|a|<1/2`, define

\[
w_a(u)=\frac{\cos(\pi a)\cosh(\pi u)}
             {\sinh^2(\pi u)+\cos^2(\pi a)}.      \tag{5}
\]

This is a strictly positive, even probability density, and

\[
\int_{\mathbb R} e^{isu}w_a(u)\,du
       =\frac{\cosh(as)}{\cosh(s/2)}.             \tag{6}
\]

Since `0<beta_j<1` for actual nontrivial zeros, (5) applies to every row
without a density cutoff. Define the probability law

\[
d\nu_T(t)=\frac1N\sum_j w_{a_j}(t-\gamma_j)\,dt. \tag{7}
\]

Multiplying (4) by (3) and using (6) gives the exact identity

\[
K_{nm}:=(S\odot H)_{nm}
       =\int_{\mathbb R}e^{it(\log n-\log m)}d\nu_T(t).  \tag{8}
\]

Equivalently,

\[
K_{nm}=\frac1N\sum_j e^{i\gamma_j\log(n/m)}
 \frac{n^{1-\beta_j}m^{\beta_j}
       +n^{\beta_j}m^{1-\beta_j}}{n+m}.           \tag{9}
\]

This is an ordinary positive phase Gram. For every finite coefficient vector,

\[
c^*Kc=\int_{\mathbb R}
       \left|\sum_n c_n n^{-it}\right|^2d\nu_T(t)\geq0. \tag{10}
\]

If a proved actual-zero Landau estimate gives
`||H_{T,D}-I|| <= epsilon(T,D)`, then (1) proves exactly

\[
(1-\epsilon)\|c\|_2^2\leq
 \int\left|\sum_{n\leq D}c_n n^{-it}\right|^2d\nu_T(t)
 \leq(1+\epsilon)\|c\|_2^2.                      \tag{11}
\]

This implication has no restriction on `delta log D` and needs no
near-critical-line density provider. Any range of `D` actually established
for the hyperbolic Landau Gram transfers with exactly the same error.

The smoothed law (7) includes continuous displacements of actual zero
ordinates. Formula (11) does not assert an unsmoothed zero-ordinate frame,
and does not establish the physical Pareto/Nyman--Beurling transfer or RH.

## 3. Self-contained Fourier proof

The residue calculation on a rectangle of height `i`, or the usual
hyperbolic-secant Fourier integral, gives

\[
\int_{\mathbb R}e^{isu}\operatorname{sech}(\pi u)\,du
       =\operatorname{sech}(s/2).                \tag{12}
\]

For completeness, at `s>=0`, shift the contour to `Im u=1`.
The upper integrand changes by the factor `-exp(-s)`;
the pole at `u=i/2` has residue `exp(-s/2)/(i pi)`.
The vertical sides tend to zero by exponential decay. Thus
`(1+exp(-s)) I(s)=2exp(-s/2)`, proving (12).
Evenness handles negative `s`.

There are no poles in either strip between `Im u=0` and `Im u=+/-a`
when `|a|<1/2`. Shift these contours in (12) to get

\[
\int e^{isu}\operatorname{sech}(\pi(u\pm ia))\,du
       = e^{\pm as}\operatorname{sech}(s/2).
\]

The algebraic identity

\[
\frac12\{\operatorname{sech}(\pi(u+ia))+
         \operatorname{sech}(\pi(u-ia))\}=w_a(u)
\]

now proves (6). Taking `s=0` proves normalization. Positivity is immediate
from (5).

## 4. Exact width and a uniform displacement tail

Differentiating (6) at zero gives

\[
\mathbb E[U_a]=0,\qquad
\mathbb E[U_a^2]=\tfrac14-a^2=\beta(1-\beta).    \tag{13}
\]

For `B>0`, substituting `z=sinh(pi u)` gives the exact tail

\[
\mathbb P(|U_a|>B)=\frac2\pi
  \arctan\!\left(\frac{\cos(\pi a)}{\sinh(\pi B)}\right)
 \leq\frac2\pi\arctan(\operatorname{csch}(\pi B)). \tag{14}
\]

The bound is sharp uniformly in `a`, attained at `a=0`, and is
`O(exp(-pi B))`. Truncating every displacement at `|u|<=B` removes a
positive Gram whose operator norm is at most `D` times the right side
of (14), because each phase vector on `D` coordinates has squared norm
`D`. Hence `B=(log D+omega)/pi` yields error `O(exp(-omega))`.


## 5. Stronger polynomial-support frame via the smoothed arithmetic main

Use the repository's complete exact signed decomposition H=I-tau*A+E,
where tau=T/(2*pi*N(T)). The Cauchy Schur transform gives exactly

    K=I-tau*B+S odot E,

with B_nm=2*Lambda(q)/(q+1) on every divisibility edge n=mq or m=nq.
The self-contained arithmetic proof in
[SmoothedPrimePowerArithmetic20261005.md](SmoothedPrimePowerArithmetic20261005.md)
gives ||B_d||=4*log(log d)+O(1). Therefore

    ||K-I|| <= tau*(4*log(log d)+O(1))+||E||.

The checked actual signed residual tends to zero whenever
 d^3/((T+3)*log(T+3))->0, including d=O(T^(1/3)*log(T)^b), b<1/3.
In that entire regime the normalized smoothed phase Gram tends to I:
the leading budget forces log(log d)=O(log(log T)), so the smoothed
arithmetic contribution also vanishes. This uses no near-line density provider. For d>=e,
a fully finite bound is

    ||K-I|| <= tau*[4*log(log d)+4*Cpsi+4*sqrt(2*Cpsi)]+||E||,
    Cpsi=4*log 2.

Every composite edge remains in B, and the negative sinh square remains
in the original exact identity before the Schur transform.

## 6. Precise information loss in the smoothing

For arbitrary matrices X, the inverse Schur map is exactly

    Psi_S^(-1)(X)=(D*X*D^(-1)+D^(-1)*X*D)/2,
    D=diag(sqrt n).

The exact operator norm of this inverse map, including on Hermitian inputs, is

    ||Psi_S^(-1)||=(d+1)/(2*sqrt(d))=cosh(log(d)/2).

For the upper bound, put x_n=log(n)/2-log(d)/4, C=diag(cosh(x_n)),
Q=diag(sinh(x_n)). The inverse map is C*X*C-Q*X*Q, factored as
(C,Q)*diag(X,X)*(C,-Q)^T. Each outside factor has squared norm
max_n[cosh(x_n)^2+sinh(x_n)^2]=cosh(log(d)/2), proving the stated bound.
For d>=2, the Hermitian matrix E_(1,d)+E_(d,1) has norm one and its
inverse image has norm (d+1)/(2*sqrt(d)), so equality holds. For d=1
the map is the identity. This proves the exact growth of the information
loss and rules out a dimension-independent reverse norm estimate.

Moreover inverse smoothing restores the hyperbolic Gram H, rather than
the original discrete phase Gram G; the per-zero cosh displacement
still has to be removed. The unsmoothed phase and physical screened
Pareto transfers remain distinct obligations.

## 7. Verification and references

Wolfram Language returned exactly `{0,0,a^2-1/4,0}` for the differences
in the shifted-sech density identity, the derivative of the antiderivative
`ArcTan[Sinh[Pi u]/Cos[Pi a]]/Pi`, the characteristic-function second
derivative at zero, and the identity (3). A direct symbolic Fourier
integration exceeded its 25-second limit; (6) is proved above by contour
shifts rather than inferred from this computation.

Relevant primary-source background: Rajendra Bhatia and K. R.
Parthasarathy, *Positive Definite Functions and Operator Inequalities*,
Bulletin of the London Mathematical Society **32** (2000), 214--228,
DOI [10.1112/S0024609399006797](https://doi.org/10.1112/S0024609399006797).
The proof above is independent of any inaccessible theorem statement.

Mathlib provides `Matrix.PosSemidef.hadamard` in
`Mathlib/Analysis/Matrix/Order.lean`. The finite bound transport only
requires this theorem, distributivity, and `S odot I=I`; it requires
neither Fourier analysis nor a completely-positive-map API.

The generic finite frame transport is kernel-checked in
[CorrelationSchurFrameBounds.lean](../Analysis/CorrelationSchurFrameBounds.lean),
with only the usual foundational axioms. The actual Cauchy correlation,
Fourier specialization, and sharp arithmetic norm remain paper proofs.
