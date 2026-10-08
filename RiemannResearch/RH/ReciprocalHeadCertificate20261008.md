# An unconditional rational cap for the actual reciprocal compression

8 October 2026. Base repository commit:
`08b89f7b6c0bfb642f67e90cb2f269df20023822`.

## Result and verification scope

For the actual inverse-square squarefree optimizer stages defined in
`RH/ZetaTwoOptimizerStage.lean`, the following paper theorem holds for every
stage containing the atoms at conductors two and three (the repository index
condition is `n ≥ 2`):

\[
 0\le m_2(n)=\frac{\|(I-P_n)D r_n\|_Q^2}{e_n}
 \le \frac9{49}<\frac3{16}.
\]

This is an unconditional fixed cap. It does not prove that the normalized
moment tends to zero and therefore does not prove RH. It supplies an actual
operator estimate that the current status document leaves open, with a cap
stronger than the displayed `3/16` candidate.

The companion `ReciprocalHeadCertificate.lean` has passed a complete
Lean source check for the exact finite rational certificate and its
Young-inequality assembly. The audited declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The infinite
weighted-Cauchy assembly and the actual stage specialization below remain
paper proofs; they are not claimed as kernel-verified operator theorems.

Mathematica independently evaluated the rational 34-site head sum and returned
`True` for all three displayed certificate inequalities. No floating point
value is used as a proof input.

## Physical setting

Write

\[
 Z=\sum_{k\ge1}\frac1{k^2},\qquad
 \|v\|_Q^2=\frac1Z\sum_{k\ge1}\frac{v(k)^2}{k^2},\qquad
 (Dv)(k)=\frac{v(k)}k.
\]

The legal atoms are \(g_d(k)=(k\bmod d)/d\). The proof first treats every
real vector \(v\in L^2(Q)\) satisfying

\[
 \langle v,g_2\rangle_Q=\langle v,g_3\rangle_Q=0.
\]

Neither optimization nor a prime-independence assertion is needed for this
universal two-constraint estimate.

Put \(a_k=k\bmod2\), \(b_k=k\bmod3\). Both pairing series converge
absolutely by Cauchy--Schwarz. Their complete normal equations give

\[
 v(1)=-\sum_{k\ge3}\frac{a_kv(k)}{k^2},\qquad
 v(2)=2\sum_{k\ge3}\frac{(a_k-b_k)v(k)}{k^2}.
\]

All coordinates from three onward remain in these signed equations.

## An exact head and complete tail Gram certificate

Let

\[
 \tau=\frac37,\quad p_1=\frac47,\quad p_2=\frac1{56},\quad
 w(k)=\begin{pmatrix}-a_k\\2(a_k-b_k)\end{pmatrix},\quad
 t_k=\frac{\tau-1/k}{k^2}>0\quad(k\ge3).
\]

The tail energy and the two head charges are

\[
 T(v)=\sum_{k\ge3}t_kv(k)^2,\qquad
 J(v)=p_1v(1)^2+p_2v(2)^2.
\]

Define the complete positive Gram matrix

\[
 C=\sum_{k\ge3}\frac{w(k)w(k)^\top}{k^2(\tau-1/k)},\qquad
 H=\operatorname{diag}(\sqrt{p_1},\sqrt{p_2})\,
 C\,\operatorname{diag}(\sqrt{p_1},\sqrt{p_2}).
\]

The denominator is bounded below by \(\tau-1/3=2/21\), so all four
matrix-entry series converge absolutely. Split this matrix exactly into
the head \(3\le k\le36\) and the complete tail \(k\ge37\).

The head before scaling is the exact rational matrix

\[
 C^{\rm head}=
 \begin{pmatrix}
 \dfrac{2493976140235121749}{1608222368576023200}
 &-\dfrac{3780433736577163}{1870026009972120}\\[5pt]
 -\dfrac{3780433736577163}{1870026009972120}
 &\dfrac{149070916904792105699926}{17215715152609904839545}
 \end{pmatrix}.
\]

The rational certificates used in the proof are

\[
 H^{\rm head}_{11}\le\frac{89}{100},\qquad
 H^{\rm head}_{22}\le\frac4{25},\qquad
 (H^{\rm head}_{12})^2=
 \frac{(C^{\rm head}_{12})^2}{98}\le\frac{21}{500}.
\]

For the entire tail, the residue bounds \(0\le a_k\le1\),
\(0\le b_k\le2\) prove

\[
 p_1a_k^2+4p_2(a_k-b_k)^2
 =\frac47a_k^2+\frac1{14}(a_k-b_k)^2\le\frac9{14}.
\]

The telescoping bound retains its finite terminal term:

\[
 \sum_{k=37}^{M}\frac1{k^2}
 \le \sum_{k=37}^{M}\left(\frac1{k-1}-\frac1k\right)
 =\frac1{36}-\frac1M.
\]

Consequently the complete positive tail matrix satisfies

\[
 0\preceq H^{\rm tail}\preceq
 \operatorname{tr}(H^{\rm tail})I\preceq\frac{37}{832}I,
\]

because

\[
 \operatorname{tr}(H^{\rm tail})
 \le\frac{9/14}{3/7-1/37}\sum_{k\ge37}\frac1{k^2}
 \le\frac{9/14}{36(3/7-1/37)}=\frac{37}{832}.
\]

In particular every residue channel is present in the full tail.

For any real \(x,y\), the signed head cross term obeys

\[
 2H^{\rm head}_{12}xy
 \le\frac3{50}x^2+\frac7{10}y^2.
\]

This follows by completing the square; the product of the two Young
coefficients equals \(21/500\), the proved bound on the cross-term square.
Adding the complete tail gives

\[
 \begin{aligned}
 (x,y)H(x,y)^\top
 &\le\left(\frac{89}{100}+\frac3{50}+\frac{37}{832}\right)x^2
 +\left(\frac4{25}+\frac7{10}+\frac{37}{832}\right)y^2\\
 &=\frac{4137}{4160}x^2+\frac{18813}{20800}y^2\\
 &\le\lambda(x^2+y^2),\qquad
 \lambda=\frac{4137}{4160}<1.
 \end{aligned}
\]

## Weighted Cauchy--Schwarz and the first-moment remainder

Let \(z=(\sqrt{p_1}v(1),\sqrt{p_2}v(2))\), so \(\|z\|^2=J(v)\).
The complete signed normal equations above express \(z\) as the sum of
the two tail functionals with their weights. For any real two-vector \(u\),
weighted Cauchy--Schwarz gives

\[
 (u^\top z)^2\le T(v)\,u^\top Hu
 \le\lambda T(v)\|u\|^2.
\]

Taking \(u=z\), and dividing if \(z\ne0\), proves
\(J(v)\le\lambda T(v)\); when \(z=0\) it is immediate.

The entire reciprocal quadratic form therefore satisfies the exact identity
and unconditional remainder estimate

\[
 \boxed{
 Z\bigl(\tau\|v\|_Q^2-\langle v,Dv\rangle_Q\bigr)
 =T(v)-J(v)
 \ge\frac{23}{4160}T(v)\ge0.
 }
\]

The coefficient at site one is \(\tau-1=-4/7\), and at site two it is
\((\tau-1/2)/4=-1/56\); these are exactly the two retained terms in
\(J(v)\). No negative site contribution was discarded.

## Actual screened second moment

Let \(V\) be any closed subspace containing \(g_2,g_3\), and let
\(r\in V^\perp\). Put \(s=(I-P_V)Dr\). Then \(s\in V^\perp\), and

\[
 \|s\|_Q^2=\langle s,Dr\rangle_Q.
\]

Cauchy--Schwarz for the positive form \(\langle x,Dy\rangle_Q\), followed
by the proved two-constraint cap on each of \(r,s\), gives

\[
 \|s\|_Q^4
 \le\langle s,Ds\rangle_Q\langle r,Dr\rangle_Q
 \le\tau^2\|s\|_Q^2\|r\|_Q^2.
\]

If \(s=0\) the desired bound is immediate; otherwise division proves

\[
 \boxed{\|(I-P_V)Dr\|_Q^2\le\frac9{49}\|r\|_Q^2.}
\]

Apply this to the actual cumulative squarefree stage \(V_n\) and its
residual \(r_n\). The existing strict positivity of \(e_n=\|r_n\|_Q^2\)
allows the displayed normalized cap. The complete signed identity remains

\[
 e_nm_2(n)=\varepsilon_n+\Gamma_n,\qquad
 \Gamma_n=\delta_n-s_n,
\]

where both \(\delta_n\) and \(s_n\) are the existing positive squared
norms. Thus the unconditional consequences are

\[
 \Gamma_n\le\frac9{49}e_n-\varepsilon_n,
 \qquad 0\le\frac{\Gamma_n^+}{e_n}\le\frac9{49}.
\]

This fixed positive cap supplies no decay. The arithmetic obligation remains
\(\Gamma_n^+/e_n\to0\), possibly cofinally.

## Reproducible Mathematica arithmetic

```wolfram
w[k_] := {-Mod[k, 2], 2 (Mod[k, 2] - Mod[k, 3])};
c = Sum[Outer[Times, w[k], w[k]] / (k^2 (3/7 - 1/k)),
        {k, 3, 36}];
{(4/7) c[[1, 1]] <= 89/100,
 c[[2, 2]]/56 <= 4/25,
 c[[1, 2]]^2/98 <= 21/500}
(* {True, True, True} *)
(9/14)/(36 (3/7 - 1/37))
(* 37/832 *)
```

The argument itself is finite rational arithmetic, complete positive-tail
control, and weighted Cauchy--Schwarz. Existing special-function residue
identities are compatible with the sums but are not required for this cap.
