# CRT carry screening: a complete-Q contraction estimate

Date: 22 October 2026.

## Result and status

For a fixed prime p and any finite real zero-charge paired family, write
h = sum_e a_e (g_{pe} - g_e) = L - C using any exact CRT carry decomposition.
Let S contain g_p and every g_e in the support, and let P be its actual Q
orthogonal projection. Put A = L - PC and D = (I-P)C.

The complete energy obeys

\[
\boxed{\|D\|_Q^2\le\frac1p\|h\|_Q^2,\qquad
\|A\|_Q^2\le\|h\|_Q^2\le\frac p{p-1}\|A\|_Q^2.}
\]

Thus uniform control of the retained lower-conductor term controls the
screened carry term as well. The uniform upper bound on that retained term
has NOT been proved. RH remains open.

The two Lean modules prove the general exact identity, its contraction
consequences, the actual finite zero-charge residue synthesis identity, and
the specialized complete-Q carry estimates. The finite synthesis and
estimates do not assume RH, squarefreeness, prime-coprimality, exact-head
matching, or a uniform energy bound. Those arithmetic restrictions are
needed when assembling the RH application.

## 1. Definitions and zero-charge identity

Work on positive integers with Q(n)=1/(Z n^2), Z=zeta(2). Extend all physical
sequences by f(0)=0. Define g_e(n)=(n mod e)/e, including g_1=0, and

\[
(T_pf)(n)=f(\lfloor n/p\rfloor),\qquad
f_a=\sum_e a_e g_e,\qquad
h_a=\sum_e a_e(g_{pe}-g_e).
\]

Integer division gives the exact identity

\[
T_pg_e=g_{pe}-\frac1e g_p.
\]

Hence the one scalar balance equation sum_e a_e/e=0 yields

\[
\boxed{h_a=(T_p-I)f_a.}
\]

This equality sums all signs before estimating anything. No modulo-one
identification is used inside the Hilbert norm.

## 2. Sharp full-Q contraction and its exact defect

Regrouping the complete physical sum into quotient blocks gives

\[
\|T_pf\|_Q^2
=\frac1Z\sum_{m\ge1}|f(m)|^2
\sum_{r=0}^{p-1}\frac1{(pm+r)^2}.
\]

Each inner sum is at most 1/(pm^2). Therefore

\[
\|T_pf\|_Q^2\le \frac1p\|f\|_Q^2.
\]

Retain the full nonnegative defect:

\[
\mathcal D_p(f):=\frac1p\|f\|_Q^2-\|T_pf\|_Q^2
=\frac1Z\sum_{m\ge1}
\left(\frac1{pm^2}-\sum_{r=0}^{p-1}\frac1{(pm+r)^2}\right)|f(m)|^2
\ge0.
\]

This sharp estimate and exact infinite-series defect were already proved in
RH/QFloorDilationEnergy.lean. The present work applies them to the carry
decomposition.

## 3. Exact contraction-screening identity

For any real Hilbert space, orthogonal projection P onto a subspace
containing f, any v, and any real q, square completion gives

\[
\boxed{
q\|v-f\|^2
=\|(I-P)(v-f)\|^2+\|Pv-qf\|^2
+(1-q)(q\|f\|^2-\|v\|^2).
}
\]

Proof: since Pf=f, the first term is ||v-Pv||^2. Expand the second
square, use <Pv,f>=<v,f>, and use
||v||^2=||Pv||^2+||v-Pv||^2. Every cross term is retained in the equality.

If q<=1 and ||v||^2<=q||f||^2, both remainders on the right are
nonnegative. Thus

\[
\|(I-P)(v-f)\|^2\le q\|v-f\|^2.
\]

If q<1, Pythagoras also gives

\[
\|v-f\|^2\le\frac{\|P(v-f)\|^2}{1-q}.
\]

## 4. Application to the CRT decomposition

Choose integers alpha_e,beta_e with e alpha_e+p beta_e=1, and let

\[
\kappa_e(n)=\lfloor\alpha_e g_p(n)+\beta_e g_e(n)\rfloor.
\]

Then

\[
g_{pe}=\alpha_e g_p+\beta_e g_e-\kappa_e,
\]

\[
L=\left(\sum_ea_e\alpha_e\right)g_p+
\sum_ea_e(\beta_e-1)g_e,\qquad C=\sum_ea_e\kappa_e,
\qquad h=L-C.
\]

For S as above, L and f_a belong to S, so

\[
Ph=A=L-PC,\qquad (I-P)h=-D=-(I-P)C.
\]

Apply Section 3 with v=T_pf_a and q=1/p. The full identity is

\[
\boxed{
\frac1p\|h\|_Q^2
=\|D\|_Q^2+
\left\|PT_pf_a-\frac1p f_a\right\|_Q^2+
\left(1-\frac1p\right)\mathcal D_p(f_a).
}
\]

Equivalently, the exact total energy is

\[
\boxed{
\|h\|_Q^2
=\frac p{p-1}\|A\|_Q^2
-\frac p{p-1}\left\|PT_pf_a-\frac1p f_a\right\|_Q^2
-\mathcal D_p(f_a).
}
\]

The two subtracted quantities are explicit nonnegative remainders. Keeping
them gives the exact equality; dropping them gives the upper bound in the
opening result. Also ||D||^2<=||A||^2/(p-1).

For p=2, the screened carry accounts for at most half of the total energy,
and ||A||^2<=||h||^2<=2||A||^2.

## 5. Independence of CRT representatives

Changing Bezout representatives by
alpha'_e=alpha_e+p t_e, beta'_e=beta_e-e t_e changes both L and C by the
same vector

\[
W=\sum_ea_e t_e(pg_p-eg_e)\in S.
\]

Consequently A'=L+W-P(C+W)=A and D'=(I-P)(C+W)=D.
The estimates therefore do not depend on the chosen CRT lifts.
This invariance is existing infrastructure in Analysis/ScreenedCarry.lean;
it is not a new unproved premise.

## 6. The precise arithmetic obligation still open

Fix ONE prime p. For every M, require finite real coefficients supported on
squarefree e>=1 with p not dividing e, including the index e=1, such that

\[
a_e=\mu(e)\quad(e\le M,\ p\nmid e),\qquad \sum_ea_e/e=0.
\]

These conditions give h_a(n)=1 for 1<=n<=M. With S_a equal to the span
of g_p and the supported g_e, the remaining sufficient provider is

\[
\boxed{
\exists B<\infty\ \forall M\ \exists a\text{ as above}:
\quad\|L_a-P_{S_a}C_a\|_Q^2\le B.
}
\]

The new theorem gives ||h_a||^2<=pB/(p-1). Weak compactness and continuous
coordinate evaluation then place 1 in the squarefree legal closure. The
existing squarefree-closure-to-RH implication supplies RH.

Conversely, a uniform bound on the original feasible h_a immediately bounds
their retained terms. The two uniform arithmetic targets are equivalent
within this paired construction.

No uniform provider has been supplied by the contraction estimate.

## 7. Why the inverse contraction does not finish RH

From ||T_p||<=p^(-1/2),

\[
(1-p^{-1/2})\|f_a\|_Q\le\|h_a\|_Q
\le(1+p^{-1/2})\|f_a\|_Q.
\]

Moreover, exact heads and h_a=T_pf_a-f_a imply, by finite iteration down to
the zero anchor,

\[
f_a(n)=-(1+\lfloor\log_p n\rfloor)\qquad(1\le n\le M).
\]

The candidate limiting source is therefore -(1+F_p), which belongs to the
ambient Q Hilbert space. The required legal approximation in the
p-coprime squarefree source span remains the arithmetic issue. Projection
onto that span supplies bounded vectors but does not supply their required
coordinate agreement. Ambient boundedness of the target alone cannot
replace this membership statement.

## 8. Formalization ledger

- Analysis/ContractionScreening.lean:
  screening_identity; screened_sq_le; retained_energy_controls_total.
- RH/QCarryContraction.lean:
  pairedVector_eq_floor_sub; floor_screening_identity;
  paired_screened_sq_le; paired_total_sq_le_retained;
  carry_screened_sq_le; carry_total_sq_le_retained.
- Coherent isolated candidate:
  job_TbqRqhx3JJsy8lm0cQhO97h-RqgIHp3l, verified=true, exit 0,
  reported Lean execution 7.246 seconds.
- Eight central declarations were axiom-audited in that candidate:
  only propext, Classical.choice, and Quot.sound occurred.
- The final project publication is separately gated by the server checkpoint.
- Open: the uniform retained-energy arithmetic provider in Section 6.

Source of this derivation: the user's CRT reduction proposal and the
elementary contraction-screening square completion above. No claim of
mathematical priority is made.
