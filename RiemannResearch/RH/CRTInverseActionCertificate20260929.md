# Exact signed CRT inverse-action certificate

Status: rigorous finite-dimensional deduction from the checked full sparse CRT
quadratic-form comparison. The matrix inversion and this deduction have not
been checked in Lean in this draft. No mathematical novelty claim is made.

Let Q be squarefree, and index all divisors of Q. For M ≥ 1 put

\[
K_{de}=\frac{\gcd(d,e)^2}{de},\qquad
B=\zeta(2)K,\qquad A=G_M,
\]

where A is the full Pareto Gram of the sparse columns
\(Md\,1_{Md\mid n}\), with positive physical indices n. The already checked
signed-form estimate is

\[
\frac M{M+1}B\preceq A\preceq B.
\]

Both matrices are positive definite. Define

\[
a_Q=\zeta(2)\prod_{p\mid Q}(1-p^{-2})\ge1.
\]

The tensor inverse is exact:

\[
(B^{-1})_{de}=\frac{\mu(d)\mu(e)}{a_Q}
\frac{\gcd(d,e)^2}{de}.
\]

For an arbitrary signed source vector h set c=A^{-1}h and c^0=B^{-1}h.
Then the complete leading row is

\[
c^0_d=\frac{\mu(d)}{a_Qd}
  \sum_{e\mid Q}\frac{\mu(e)\gcd(d,e)^2}{e}h_e.
\]

There is a dimension- and conductor-independent inverse-action certificate:

\[
\boxed{
|c_d-c^0_d|^2\le\frac{1}{M^2a_Q}\,h^{\mathsf T}B^{-1}h.
}
\]

More generally, every signed test vector z satisfies

\[
\boxed{
|z^{\mathsf T}(c-c^0)|^2
\le\frac1{M^2}(z^{\mathsf T}B^{-1}z)
                    (h^{\mathsf T}B^{-1}h).
}
\]

Proof: inversion reverses the full Loewner comparison, so
\(0\preceq D=A^{-1}-B^{-1}\preceq M^{-1}B^{-1}\).
Positive-semidefinite Cauchy--Schwarz gives
\((z^{\mathsf T}Dh)^2\le(z^{\mathsf T}Dz)(h^{\mathsf T}Dh)\), and
each of the two factors has the displayed bound. The one-row statement uses
\((B^{-1})_{dd}=1/a_Q\).

The exact equation and complete energy remainder are

\[
A(c-c^0)=(B-A)c^0,
\qquad
h^{\mathsf T}A^{-1}h
=h^{\mathsf T}B^{-1}h+h^{\mathsf T}Dh,
\]
\[
0\le h^{\mathsf T}Dh\le M^{-1}h^{\mathsf T}B^{-1}h.
\]

Nothing is dropped: the matrix B−A is the full positive CRT remainder, with

\[
(B-A)_{de}=de\sum_{\substack{k\ge1\\d\mid k,\ e\mid k}}
                 \frac1{k^2(Mk+1)}.
\]

Thus Abel summation can be applied to the leading signed Möbius row, and the
remaining inverse-action error has an explicit dimension-free bound in the
natural reference energy. Even if Q grows, it suffices for this error to
vanish that \(h^{\mathsf T}B^{-1}h=o(M^2)\).

This concerns the normalized sparse derivative Gram only. It cannot replace
the original legal residue Gram or the prime-power screened legal Gram.
Uniform primitive control was already disproved in the current repository;
an actual legal correction must retain its primitive remainder.
