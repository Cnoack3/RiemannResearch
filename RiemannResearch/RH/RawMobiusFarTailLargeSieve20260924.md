# Unconditional vanishing of the far tail of the raw Möbius energy

Status: rigorous mathematical proof assembled in this continuation from the classical additive large sieve and elementary finite Fourier analysis. **The complete arithmetic theorem is not kernel-verified in Lean in this batch.** Its generic Abel transfer and actual raw-tail application are kernel-verified; the finite Fourier/CRT and large-sieve providers remain unformalized. No large-sieve provider was found by bounded declaration and source searches in the current RiemannResearch repository. This argument does not prove RH and does not estimate the unresolved middle window by a subpower.

For an integer N ≥ 1, let

\[
m_N=\sum_{d=1}^N\frac{\mu(d)}d,\qquad M_N=\sum_{d=1}^N\mu(d),\qquad
U_N(k)=1+\sum_{d=1}^N\mu(d)\frac{k\bmod d}{d},
\]

and put

\[
T_N=\sum_{k>N^2}\frac{U_N(k)^2}{k(k+1)},\qquad
A_N=1+\frac{M_N-m_N}{2},\qquad H_N=\sum_{d=1}^N\frac1d.
\]

The d=1 term in U_N is zero, so this agrees with the raw residual in the existing budget module.

## Precise theorem

Define the finite signed quantity

\[
V_N=\frac1{12}\sum_{d,e=1}^N
\mu(d)\mu(e)\frac{\gcd(d,e)^2-1}{de}.
\]

Then V_N is nonnegative and

\[
\boxed{
T_N\le\frac{2(A_N^2+V_N)}{N^2+2}
\le\frac{2A_N^2+(N/6)H_N^2}{N^2+2}.
}
\]

In particular, the prime number theorem implies unconditionally that T_N tends to zero.

## Proof of the finite signed variance formula

Let L be the least common multiple of 1,...,N, and average over integers k modulo L. The average of (k mod d)/d is (d−1)/(2d). Thus the average of U_N is exactly A_N.

For d,e ≤ N put g=gcd(d,e). For a uniformly distributed k modulo lcm(d,e), the two residues k mod d and k mod e have the same residue r modulo g. Conditional on r, their quotients after subtracting r are independent uniform variables on {0,...,d/g−1} and {0,...,e/g−1}; this follows from the ordinary CRT for the coprime moduli d/g and e/g. Consequently their conditional covariance vanishes, and their centered conditional expectations are

\[
\frac{r-(g-1)/2}{d},\qquad
\frac{r-(g-1)/2}{e}.
\]

Since a uniform integer in {0,...,g−1} has variance (g²−1)/12, the exact covariance is

\[
\frac1{\operatorname{lcm}(d,e)}
\sum_{k=0}^{\operatorname{lcm}(d,e)-1}
\left(\frac{k\bmod d}{d}-\frac{d-1}{2d}\right)
\left(\frac{k\bmod e}{e}-\frac{e-1}{2e}\right)
=\frac{g^2-1}{12de}.
\]

Expanding the square before taking any majorant gives

\[
\frac1L\sum_{k=0}^{L-1}(U_N(k)-A_N)^2=V_N,\qquad
\frac1L\sum_{k=0}^{L-1}U_N(k)^2=A_N^2+V_N.
\]

These identities retain the signs of every Möbius cross term. For the unconditional upper bound, use |μ| ≤ 1 and the nonnegative covariance kernel:

\[
12V_N\le\sum_{d,e\le N}\frac{\gcd(d,e)^2}{de}
\le\sum_{g\le N}g^2\sum_{\substack{d\le N\\g\mid d}}\frac1d
                         \sum_{\substack{e\le N\\g\mid e}}\frac1e
=\sum_{g\le N}H_{\lfloor N/g\rfloor}^2\le NH_N^2.
\]

The second inequality holds because the sum of the squares of the common positive divisors includes the square of the gcd.

## Classical large sieve input and its applicability

Each d-periodic function (k mod d)/d has a finite Fourier expansion with frequencies a/d modulo 1. After collecting equal frequencies, U_N therefore has an expansion

\[
U_N(k)=\sum_{\theta\in\mathcal F_N}c_\theta e^{2\pi i k\theta},
\]

where the distinct frequencies belong to the reduced fractions with denominator at most N, including 0/1. Orthogonality on the common period L gives

\[
\sum_{\theta\in\mathcal F_N}|c_\theta|^2=A_N^2+V_N.
\]

Distinct reduced frequencies a/q and b/r have circular distance at least 1/(qr), hence at least 1/N². The standard dual additive large sieve gives, for any interval containing J consecutive integers,

\[
\sum_{k=K+1}^{K+J}|U_N(k)|^2
\le (J-1+N^2)\sum_\theta|c_\theta|^2
\le (J+N^2)(A_N^2+V_N).
\]

An explicit primary author-hosted reference is E. Kowalski, *Amplification Arguments for Large Sieve Inequalities*, pp. 1–2, equations (2) and (3), with the constant Δ = J−1+N²: https://people.math.ethz.ch/~kowalski/two-remarks-large-sieve.pdf . The shift K is absorbed by replacing c_θ with c_θ exp(2πiKθ), which preserves coefficient norms. The sharp constant is unnecessary; the weaker displayed J+N² suffices. For N=1 the same statement is immediate since U_1 is constant.

## Exact Abel step

The following elementary implication is useful independently of the Möbius application. Suppose Q is a nonnegative integer, C ≥ 0, f(k) ≥ 0, and

\[
S_j:=\sum_{i=1}^j f(Q+i)\le(Q+j)C\quad(j\ge1).
\]

With w_k=1/[k(k+1)], finite summation by parts gives

\[
\sum_{i=1}^J f(Q+i)w_{Q+i}
=S_Jw_{Q+J}+\sum_{i=1}^{J-1}S_i(w_{Q+i}-w_{Q+i+1}).
\]

All weight differences are nonnegative. Substituting the prefix bound and using

\[
w_k-w_{k+1}=\frac2{k(k+1)(k+2)}
\]

therefore gives the explicit finite estimate

\[
\sum_{i=1}^J f(Q+i)w_{Q+i}
\le C\left[\frac2{Q+2}-\frac1{Q+J+1}\right].
\]

Letting J increase proves summability and the bound 2C/(Q+2). Apply this with Q=N², f(k)=U_N(k)², C=A_N²+V_N and the preceding large-sieve prefix estimate. This proves the boxed theorem.

Finally M_N/N tends to zero by the prime number theorem, |m_N| ≤ H_N, and H_N²/N tends to zero. Hence A_N/N tends to zero and both terms of the explicit upper bound tend to zero.

## Consequence for the exact continuous energy

Set

\[
R_N(x)=\mathbf1_{(0,1]}(x)+\sum_{d=1}^N\mu(d)\{1/(dx)\},\qquad
E_N=\int_0^\infty R_N(x)^2\,dx.
\]

For y=k+t with k≥1 and 0≤t<1,

\[
R_N(1/y)=U_N(k)+tm_N.
\]

For 0<y<N+1 the Möbius divisor identity gives R_N(1/y)=ym_N. Thus, with

\[
b_k=\int_0^1\frac{t}{(k+t)^2}\,dt
=\log\frac{k+1}{k}-\frac1{k+1},\qquad
c_k=\int_0^1\frac{t^2}{(k+t)^2}\,dt
=1-2k\log\frac{k+1}{k}+\frac{k}{k+1},
\]

the change of variables y=1/x and the cell partition give the exact identity

\[
E_N=B_N+T_N+\delta_N,
\qquad
\delta_N=m_N^2+2m_N\sum_{k>N}b_kU_N(k)+m_N^2\sum_{k>N}c_k.
\]

Here B_N is the existing finite budget. Since |U_N(k)| ≤ N, 0≤b_k,c_k≤1/[k(k+1)], and the latter tail sums to 1/(N+1),

\[
|\delta_N|\le2|m_N|+\left(1+\frac1{N+1}\right)m_N^2.
\]

The already available unconditional limit m_N→0 gives δ_N→0. Together with the far-tail theorem, this proves the unconditional conclusion

\[
\boxed{E_N-B_N\longrightarrow0.}
\]

This is an additive identification of the full continuous energy with the actual finite budget. It leaves the middle-window cancellation estimate needed for RH unresolved. In particular, boundedness or subpower growth of either quantity has not been proved here.

## Formalization boundary

Still to formalize: finite Fourier expansion of the residue functions; the CRT covariance identity and its finite gcd bound; a dual additive large-sieve theorem; and the continuous cell partition/change-of-variables identification. The elementary Abel transfer is now proved in Analysis/ReciprocalEnergyFromPrefix.lean, and rawMobiusFarEnergy_le_of_prefix specializes it to the actual raw-tail energy with its finite-interval premise explicit. The classical analytic large sieve is the principal provider absent from the inspected repository. None of these missing providers is to be introduced as an axiom or labeled verified merely because it appears in this report.
