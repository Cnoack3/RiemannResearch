# Coordinate Fourier bridge and its boundary-space limitation

September 10, 2026.

**Status: ordinary mathematical derivations, not Lean verified.** This note
uses the verified integer-tent, signed-step, and fixed-conductor approximation
results recorded in `DyadicTentTerminalVerification20260910(1).md`. The periodic-extension and Fourier arguments below are not formally
verified; the binary logarithmic coefficient and root-tent integral have
separate Lean proofs in the accompanying continuation. RH and the uniform signed arithmetic energy estimate remain open.

## 1. Exact continuous coordinate functions

Fix a boundary index `i`, and put

\[
\ell=i+1\ge1,\qquad a=2\ell,\quad c=2\ell+1,\quad b=2\ell+2,
\quad L=\log2.
\]

Here `a` is a tent endpoint; a residue conductor will instead be denoted `A`.
Define

\[
\tau_\ell(x)=\max(0,1-|x-c|),\qquad
\Psi_\ell(x)=\sum_{d\in\mathbb Z}\tau_\ell(2^{-d}x),\quad x>0.
\]

This sum is locally finite: on a compact positive interval only finitely
many dilates of the support `[a,b]` can occur. Its summands have disjoint
positive supports, since `b/a≤2`. Thus `Ψ_ℓ` is continuous,
`0≤Ψ_ℓ≤1`, and

\[
\Psi_\ell(2x)=\Psi_\ell(x).
\]

For every positive integer `k`,

\[
\boxed{\Psi_\ell(k)=s_k(\ell-1).}
\]

A complete route to this integer identification is as follows. Negative
`d` contribute zero at integers, because their arguments are even integers
and the tent has its peak at the odd integer `c`. For nonnegative `d` the
sum is finite at each integer. These finite sums obey

\[
u_{2m}=u_m,\qquad
u_{2m+1}=\mathbf1_{m=\ell}+\tfrac12(u_m+u_{m+1}),
\qquad u_0=u_1=0.
\]

For the odd recurrence, each scaled tent with scale at least two is affine
between the consecutive integer arguments `m` and `m+1`: all its knots are
integers. Its midpoint value is therefore their average. The unscaled tent
contributes precisely the displayed indicator. Strong induction gives
uniqueness of this recurrence and identifies it with the actual `s_k`.

In particular, `Ψ_ℓ(1)=0`.

## 2. Fourier coefficients, including the constant contribution

The continuous function `φ_ℓ(t)=Ψ_ℓ(2^t)` has period one. Use the convention

\[
C_{\ell,h}=\int_0^1\phi_\ell(t)e^{-2\pi iht}\,dt,
\qquad \omega_h=2\pi h/L.
\]

Unfolding the locally finite periodization gives

\[
C_{\ell,h}=\frac1L\int_a^b\tau_\ell(x)x^{-1-i\omega_h}\,dx.
\]

Integrating the two affine pieces yields

\[
\boxed{C_{\ell,0}
=\frac{a\log a-2c\log c+b\log b}{L}.}
\]

For `h≠0`,

\[
\boxed{C_{\ell,h}
=\frac{a^{1-i\omega_h}-2c^{1-i\omega_h}+b^{1-i\omega_h}}
{L(-i\omega_h)(1-i\omega_h)}.}
\]

Positive real bases use `x^z=exp(z log x)`. To check the denominator and
signs, the general two-piece integral, for `z≠0,−1`, is

\[
\int_a^b\tau_\ell(x)x^{z-1}\,dx
=\frac{a^{z+1}-2c^{z+1}+b^{z+1}}{z(z+1)}.
\]

The value at `z=0` is the removable limit stated for `C_{ℓ,0}`.
Since the tent has area one,

\[
\frac1{bL}\le C_{\ell,0}\le\frac1{aL},\qquad
|C_{\ell,h}|\le\frac{4c}{L|\omega_h|\sqrt{1+\omega_h^2}}
\quad(h\ne0).
\]

Thus the Fourier series is absolutely and uniformly convergent for each
fixed `ℓ`. Fourier uniqueness for continuous periodic functions gives

\[
\Psi_\ell(x)=\sum_{h\in\mathbb Z}C_{\ell,h}x^{i\omega_h},
\qquad
\boxed{C_{\ell,0}+\sum_{h\ne0}C_{\ell,h}=0.}
\]

The last identity is evaluation at `x=1`. The constant contribution is
essential and has not been discarded.

The terminal binary octave gives a second identification of the mean:

\[
\boxed{r_2(\ell-1)=LC_{\ell,0}
=a\log a-2c\log c+b\log b.}
\]

Indeed, along `N=2^j` its exact finite sum is the right Riemann sum for
`∫_1^2 Ψ_ℓ(x) dx/x`. The verified complete-boundary terminal estimate
identifies its limit with `r_2(ℓ−1)`. The logarithmic integral equals
`LC_{ℓ,0}` by the change of variables `x=2^t`.

The separate Lean continuation proves this last displayed formula directly
through finite harmonic blocks in `DyadicResidueBinaryLogMean.lean` and identifies
it with the weighted root-tent integral. The periodic construction and Fourier
arguments in this note remain ordinary, not Lean verified.

## 3. A justified fixed-conductor scalar residue identity

Fix an integer conductor `A≥2`, and define the signed reset coefficients

\[
v_A(k)=1-A\mathbf1_{A\mid k},\qquad
D_{A,K}(\omega)=\sum_{k=1}^K v_A(k)k^{i\omega-1}.
\]

Their exact partial sums are

\[
\sum_{k=1}^n v_A(k)=n\bmod A=:R_A(n),\qquad 0\le R_A(n)\le A-1.
\]

Here is a bound strong enough for the Fourier interchange. Write
`W=√(1+ω²)` and `M=⌈1+|ω|⌉`. For `K>M`, summation by parts gives

\[
\begin{aligned}
\sum_{k=M+1}^K v_A(k)k^{i\omega-1}
={}&R_A(K)K^{i\omega-1}-R_A(M)(M+1)^{i\omega-1}\\
&+\sum_{k=M+1}^{K-1}R_A(k)
\bigl(k^{i\omega-1}-(k+1)^{i\omega-1}\bigr).
\end{aligned}
\]

The derivative of `x^(iω−1)` has modulus `W/x²`, so the tail is bounded by

\[
(A-1)\left[\frac{1+W}{M+1}+\frac{1-W}{K}\right]
\le A-1,
\]

because `1≤W≤M`. The first `min(K,M)` terms have absolute sum at most
`(A−1)H_M`, with `H_M≤1+log M` and `M≤2+|ω|`. Consequently

\[
\boxed{\sup_{K\ge0}|D_{A,K}(\omega)|
\le(A-1)\bigl[2+\log(2+|\omega|)\bigr].}
\]

The same tail identity with `M→∞`, for fixed `ω`, proves convergence to
`D_A(ω)`. Combining this bound with `C_{ℓ,h}=O_ℓ(h^(−2))` gives a summable
dominating sequence in the frequency index `h`.

At each finite `K`, substitute the absolutely convergent scalar Fourier
series into the actual signed boundary prefix. There are only finitely
many `k`, so this first interchange is valid. Then dominated convergence
in `h`, together with the verified fixed-conductor boundary approximation,
gives

\[
\boxed{r_A(\ell-1)=\sum_{h\in\mathbb Z}C_{\ell,h}D_A(\omega_h).}
\]

This frequency series is absolutely convergent for each fixed pair
`(A,ℓ)`. The mean is

\[
D_A(0)=\log A,
\]

as is seen along `K=AN` from `D_{A,AN}(0)=H_{AN}−H_N`.

For identification with the zeta function, first use absolute convergence
on `Re(s)>1` to obtain

\[
\sum_{k\ge1}v_A(k)k^{-s}=(1-A^{1-s})\zeta(s).
\]

Bounded reset partial sums continue the left side holomorphically to
`Re(s)>0`, locally uniformly by summation by parts. Analytic continuation
then identifies both sides there, with the singularity at `s=1` removed.
At `s=1−iω`, this yields, for `ω≠0`,

\[
D_A(\omega)=(1-A^{i\omega})\zeta(1-i\omega).
\]

The complete scalar formula is therefore

\[
\boxed{
r_A(\ell-1)=C_{\ell,0}\log A
+\sum_{h\ne0}C_{\ell,h}(1-A^{i\omega_h})\zeta(1-i\omega_h).
}
\]

For `A=2`, all nonzero-frequency multipliers vanish, recovering precisely
the binary logarithmic mean. For `A=1`, all reset coefficients and the
residue are zero; that case can be handled separately.

## 4. Why this is not automatically a boundary Hilbert Fourier transform

The continuous extension above is a family of scalar functions. It is
false that its values always form a square-summable boundary vector.

Take `x=4/3`. For `j≥1`, set

\[
\ell_j=\left\lfloor\frac{2^{j+1}}3\right\rfloor
=1,2,5,10,21,\ldots.
\]

These are distinct positive integers. The fractional part of
`2^(j+1)/3` is either `1/3` or `2/3`. Accordingly,

\[
\tau_{\ell_j}(2^j x)=\frac23.
\]

The supports in the periodization have disjoint positive interiors, so
this is its unique positive contribution for that coordinate. Hence

\[
\boxed{\Psi_{\ell_j}(4/3)=\frac23,
\qquad\sum_{\ell\ge1}\Psi_\ell(4/3)^2=+\infty.}
\]

There is also an integrated obstruction, independent of the exceptional
point above. Unfolding and using the tent's squared area `2/3` gives

\[
\int_0^1|\phi_\ell(t)|^2\,dt
=\frac1L\int_a^b\frac{\tau_\ell(x)^2}{x}\,dx
\ge\frac2{3bL}.
\]

The sum of these lower bounds over `ℓ` diverges. Tonelli's theorem
therefore rules out an `L²([0,1];ℓ²)` interpretation of this family.

Thus the coordinatewise Fourier identities do not justify interchanging
the frequency sum with the complete boundary square sum. Such an
interchange needs its own convergence argument for the actual signed
arithmetic expressions. A coordinatewise identity must not be substituted
for that argument, and no mixed boundary-energy terms have been removed
by this note.

## Next bounded formal target

After the binary logarithmic coefficient, formalize the scalar signed
residue identity through `D_A`: first the exact reset partial sums and
uniform logarithmic frequency bound, then the coordinatewise Fourier
interchange. Zeta identification can be a subsequent endpoint. The full
boundary signed-energy convergence and the arithmetic estimate uniform as
damping vanishes remain separate obligations toward RH.
