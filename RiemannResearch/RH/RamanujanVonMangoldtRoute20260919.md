# Ramanujan → orthogonal sums → CRT → von Mangoldt → seed coefficients

19 September 2026. Source: Christian Noack's requested route and clarification
that lambda is the von Mangoldt function. All norms use the complete Pareto
law \(w_k=1/(k(k+1))\), \(k\ge1\). The finite construction is established;
convergence to one is not proved.

## Exact coordinates and the marked vector

Write \(R_d(k)=k\bmod d\) and
\[
 B_q(k)=\sum_{d\mid q}\mu(q/d)R_d(k)=-\sum_{j=1}^{k}c_q(j).
\]
The allowed conductors are \(q>1\) with \(2\mid q\) or \(3\mid q\).
They are independent and span exactly the algebraic two-seed space
(IntegratedRamanujanBasis).

The genuine weighted mean, already proved in ParetoResidueMean, is
\[
 b_q=\langle1,B_q\rangle_w
 =\sum_{d\mid q}\mu(q/d)\log d=\Lambda(q).
\]
The arithmetic identity is also documented in
[Mathlib's von Mangoldt module](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.html).
The vector \(b\) is supported on powers of 2 and 3 among allowed conductors.
All allowed mixed conductors remain in the dictionary and Gram matrix.

## Orthogonal sums with the actual weights

Let \(s\) be a finite set of conductors greater than one, and let \(q>\max s\),
with the last condition interpreted as \(\forall d\in s,\ d<q\). Define
\[
 K_{de}=\langle B_d,B_e\rangle_w,\qquad
 k_d=\langle B_d,B_q\rangle_w,\qquad a=K_s^{-1}k.
\]
The inverse exists by the previously established strict Gram positivity.
Set
\[
 u_q=B_q-\sum_{d\in s}a_dB_d,\qquad
 \sigma_q=\|u_q\|_w^2
   =K_{qq}-k^\top K_s^{-1}k>0,
\]
\[
 \eta_q=\langle1,u_q\rangle_w
   =\Lambda(q)-\sum_{d\in s}a_d\Lambda(d).
\]
The new module RamanujanOrthogonalScores.lean constructs this inverse fit,
proves orthogonality, identifies the exact von Mangoldt score and Schur
pivot, and proves strict pivot positivity by
\(D_q u_q=-q\), where \(D_q\) is the repository's Mobius difference.

For the old full regression \(F_s\), its exact scalar update is
\[
 F_s^+=F_s+\frac{\eta_q}{\sigma_q}u_q,\qquad
 \|1-F_s^+\|_w^2
 =1-\operatorname{mass}(s)-\frac{\eta_q^2}{\sigma_q}.
\]
This identity and legality are checked as update_error and update_legal.
The gain is bounded above by the old error (gain_le_error).

For an increasing allowed enumeration \(q_1,q_2,\ldots\), finite regression
uniqueness identifies the orthogonal synthesis with the ordinary Gram solve:
\[
 F_N=\sum_{j=1}^{N}\frac{\eta_j}{\sigma_j}u_j
     =\sum_{q\in s_N}(K_{s_N}^{-1}b_{s_N})_q B_q,
 \qquad
 \|1-F_N\|_w^2=1-\sum_{j=1}^{N}\frac{\eta_j^2}{\sigma_j}.
\]
Indeed the update has the same span and the same normal equations as the
enlarged regression: its residual remains orthogonal to the old span and
becomes orthogonal to \(u_q\), hence also to \(B_q\). This explains the
finite orthogonal display. The new Lean module checks the one-step identity;
the existing RamanujanMeanOptimizer supplies the finite Gram optimizer.

Even when \(\Lambda(q)=0\), the screened score
\(-\sum a_d\Lambda(d)\) can be nonzero. Thus von Mangoldt is the target
correlation vector, not a rule for deleting mixed conductors.

## CRT computes the full Gram matrix

For a common positive period \(Q\), divisible by the relevant conductors,
\[
 K_{de}=\sum_{r=1}^{Q}W_Q(r)B_d(r)B_e(r),\qquad
 W_Q(r)=\sum_{\ell=0}^{\infty}
       \frac{1}{(r+\ell Q)(r+\ell Q+1)}.
\]
The theorems ramanujanPacket_period_of_dvd and periodic_paretoInner_mixed give
this exact regrouping. CRT can organize the finite residue evaluations into
prime-power coordinates. The weights \(W_Q(r)\) include every infinite
progression tail and every signed cross term.

Uniform CRT orthogonality alone does not make this weighted matrix
diagonal. The orthogonal sums above use the actual matrix \(K\).

## Explicit finite change back

For each allowed \(q\), choose \(p=2\) if \(2\mid q\), otherwise \(p=3\).
Write \(q=p^{v+1}u\) with \(p\nmid u\). Then
\[
 \boxed{B_q=\sum_{d\mid u}\mu(u/d)\,
                  \operatorname{dilation}_{p^v d}(R_p).}
\]
This is newly checked as ramanujanPacket_prime_pow_mul_inverse in
IntegratedRamanujanInverse.lean. It includes \(u=1\) and arbitrary
additional prime factors. The proof uses the prime divisor transform for
\(v=0\), then prime multiplication and dilation composition.

Consequently, if \(F=\sum_q H_qB_q\), its seed coefficient at \((p,m)\) is
the finite sum of \(H_q\mu(u_q/d)\) over terms with the selected seed
\(p_q=p\), \(d\mid u_q\), and \(m=p^{v_q}d\). Equal seed scales are combined.

Here dilation m (residue p)(k) means
\(m(\lfloor k/m\rfloor\bmod p)\). For the normalized generators
\(h_{p,m}(k)=\lfloor k/m\rfloor\bmod p\), multiply these seed coefficients
by \(m\).

## Retaining the previously prescribed exact head

The unconstrained regression just displayed need not have \(F_N(k)=1\)
for \(1\le k\le N\). To retain that condition, use the same finite
coordinate change on the affine space already used by TwoSeedSchurCandidates.

For a finite allowed conductor set, put \(A_{kq}=B_q(k)\), \(1\le k\le N\).
Choose \(AH_0=\mathbf1\) and let the independent columns of \(U\) span
\(\ker A\). The exact affine optimizer is
\[
 S=U^\top K U,\quad d=U^\top(b-KH_0),\quad
 H_*=H_0+US^{-1}d,\quad F_*=\sum_q(H_*)_qB_q,
\]
\[
 \|1-F_*\|_w^2
 =1-2b^\top H_0+H_0^\top KH_0-d^\top S^{-1}d.
\]
Orthogonalize the columns of \(U\) in the full \(K\) metric to turn the last
term into a sum of squared scores over positive pivots. Every direction
then has zero head, so all updates retain the head exactly. Applying the
finite inverse above produces seed coefficients for the same function.
This matrix display describes the existing finite affine Schur construction;
no new all-scale affine estimate is claimed.

## Remaining convergence obligation

For the exhaustive unconstrained sequence, the exact remaining statement is
\[
 \sum_{j\ge1}\frac{\eta_j^2}{\sigma_j}=1.
\]
Nonnegativity and finite regression prove only that the partial sums increase
and stay at most one. Their limit being one is the missing density statement.

For growing exact-head candidates, the corresponding full affine Schur
errors above must tend to zero along a chosen finite-budget schedule.
Neither CRT regrouping, the von Mangoldt mean identity, nor uniqueness of
finite regression establishes that estimate. A fixed-dictionary CLT likewise
does not provide a bound uniform in the growing dictionary. These are open
research obligations, not assumptions discharged by the new finite lemmas.
