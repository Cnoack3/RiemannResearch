# Actual residual: refined tail estimate and the Abel interchange obstruction

Status: paper derivations from the project's verified Hilbert and dilation
identities and the newly verified bounded-primitive pairing theorem. The
additional formulas in this note have not individually been checked in Lean.
No proof of RH or mathematical novelty is claimed.

Write

\[
r=\mathrm{limitResidual},\qquad E=\|r\|_P^2,
\qquad w_k=\frac1{k(k+1)}\quad(k\ge1),
\]

and let \(D_m\) be the project's integer dilation. Its physical coordinates are
\((D_m f)(k)=m f(\lfloor k/m\rfloor)\), with the coordinate at zero anchored at
zero, and \(\|D_m f\|_P^2=m\|f\|_P^2\).

## 1. An exact tail refinement of the quadratic-correlation estimate

Define the actual residual tail energy

\[
E_m=\sum_{k\ge m}w_k r(k)^2.
\]

Then \(0\le E_m\le E\) and \(E_m\to0\). Since \(D_mr\) vanishes on
\(1\le k<m\), Cauchy--Schwarz applied only to its support proves

\[
\boxed{\left|\langle r,D_mr\rangle_P\right|^2
       \le m E E_m.}
\]

The verified exact partial-sum identity is

\[
S_N:=\sum_{k=1}^Nr(k)
=2\sum_{m=1}^N\langle r,D_mr\rangle_P
-N\langle r,D_{N+1}r\rangle_P.
\]

Consequently

\[
\boxed{|S_N|\le\sqrt E\left(
2\sum_{m=1}^N\sqrt{mE_m}
+N\sqrt{(N+1)E_{N+1}}\right).}
\]

Taking \(E_m\le E\) recovers the already checked cutoff-dependent bound.
Taking \(E_m\to0\) gives

\[
\lim_{N\to\infty}\frac{S_N}{N^{3/2}}=0.
\]

For completeness, fix \(\varepsilon>0\), choose \(M\) with
\(\sqrt{E_m}\le\varepsilon\) for every \(m\ge M\), and split the displayed
sum at \(M\). The fixed prefix divided by \(N^{3/2}\) tends to zero, while
\(\sum_{m=M}^N\sqrt m\le N\sqrt N\). The boundary term divided by
\(N^{3/2}\) is at most \(\varepsilon\sqrt{(N+1)/N}\).
Then let \(\varepsilon\) decrease to zero.

This is a strict improvement over a fixed constant bound at the same scale,
but it supplies no fixed improvement in the exponent. The ordinary Hilbert
condition alone cannot supply one: the vector
\(f(k)=\sqrt{k}/\log(k+1)\) belongs to this weighted Hilbert space, yet for
every \(\delta>0\), its positive partial sums divided by
\(N^{3/2-\delta}\) tend to infinity. This example is not asserted to be the
actual orthogonal residual. It identifies the limitation of arguments using
only the Hilbert norm and dilation support.

## 2. Exact Abel estimates

For \(0<z<1\), set

\[
R(z)=\sum_{k\ge1}r(k)z^k,
\qquad A(z)=\sum_{m\ge1}\langle r,D_mr\rangle_Pz^m.
\]

Both series and the differentiated series used below converge absolutely on
compact subintervals of \((0,1)\), by the polynomial bounds above. Summing the
verified coordinate identity gives the exact equality

\[
\boxed{R(z)=(z-1)A'(z)+(1+z^{-1})A(z).}
\]

The cancellation represented by the factor \(z-1\) should be retained before
taking absolute values. It gives the unconditional bound linear in \(E\),

\[
|R(z)|\le E\left[
(1-z)\sum_{m\ge1}m\sqrt m\,z^{m-1}
+(1+z^{-1})\sum_{m\ge1}\sqrt m\,z^m\right].
\]

The tail-sensitive version replaces every \(E\sqrt m\) on the right by
\(\sqrt{E}\sqrt{mE_m}\). These sums are finite for every fixed \(z<1\),
but their factors are not uniformly bounded as \(z\uparrow1\).

Independently, Cauchy--Schwarz gives the explicit bound

\[
|R(z)|^2\le E\sum_{k\ge1}k(k+1)z^{2k}
=\boxed{\frac{2Ez^2}{(1-z^2)^3}}.
\]

Splitting the Cauchy--Schwarz estimate at a fixed tail cutoff, then using
\(E_m\to0\), improves this to

\[
\lim_{z\uparrow1}(1-z^2)^{3/2}R(z)=0.
\]

Neither this normalization nor the exact differentiated-series identity
forces the unnormalized Abel means to stay bounded.

## 3. The two iterated limits can be computed exactly

Let \(e_N=\mathbf1-\mathrm{rawMobiusHilbert}(N)\), and damp the actual
residual by \(r_z(k)=z^kr(k)\), for \(0<z<1\).

The positive coordinates of \(r_z\) are absolutely summable, because

\[
\sum_{k\ge1}|r_z(k)|
\le\sqrt E\left(\sum_{k\ge1}k(k+1)z^{2k}\right)^{1/2}<\infty.
\]

Thus their ordinary partial sums are bounded. The newly verified
bounded-primitive pairing theorem gives, for each fixed \(z<1\),

\[
\lim_{N\to\infty}\langle e_N,r_z\rangle_P=0.
\]

On the other hand \(r_z\to r\) in the full Pareto norm as \(z\uparrow1\),
by dominated convergence. For each fixed \(N\), continuity of the inner
product and the exact orthogonality identity give

\[
\lim_{z\uparrow1}\langle e_N,r_z\rangle_P
=\langle e_N,r\rangle_P=E.
\]

Therefore the two iterated limits are exactly

\[
\boxed{\lim_{z\uparrow1}\lim_{N\to\infty}
\langle e_N,r_z\rangle_P=0,\qquad
\lim_{N\to\infty}\lim_{z\uparrow1}
\langle e_N,r_z\rangle_P=E.}
\]

This is an unconditional pair of identities; it does not assume that the
limits are unequal. If the actual residual is nonzero, they are unequal.

To derive RH from Abel damping one must justify a uniform interchange, for
example

\[
\lim_{z\uparrow1}\sup_N
|\langle e_N,r-r_z\rangle_P|=0.
\]

This uniform statement implies \(E=0\), and conversely is automatic when
\(E=0\). It is therefore another exact form of the open residual-vanishing
obligation, rather than an unconditional consequence of fixed-test decay.
Here the supremum is taken in the extended nonnegative reals; equivalently,
for every \(\varepsilon>0\) the displayed absolute value must be at most
\(\varepsilon\) simultaneously for all \(N\), whenever \(z\) is sufficiently
close to one.
The crude bound
\(|\langle e_N,r-r_z\rangle_P|\le\|e_N\|_P\|r-r_z\|_P\)
does not provide uniformity without additional control of the raw residual
norms or of the actual residual's damping error.

## Research conclusion

The quadratic dilation identities give a sound tail-sensitive refinement and
normalized Abel cancellation. They do not presently improve the cutoff power
or bound the actual ordinary partial sums. The exact pair of iterated limits
isolates the missing uniform estimate in the Abel approach and prevents an
illegitimate exchange of limits from being mistaken for an RH proof.
