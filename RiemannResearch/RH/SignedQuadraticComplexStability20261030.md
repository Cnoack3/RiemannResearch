# Signed quadratic correction: complex squarefree symmetry and quantitative stability

Date: 30 October 2026.

## Conclusion and scope

This continuation advances the supplied signed-quadratic agenda through exact finite results. It does not prove RH. The new results concern the complete arithmetic covariance on arbitrary finite squarefree support, quantitative perturbation control, and sharper nonresonant rational-frequency peaks.

The attached 22 October handoff predates the repository's 25 October continuation. The real Möbius sign identity, qualitative Hermitian perturbation, rational logarithmic separation, weighted Cauchy, and decaying-profile formulas already existed. They are reused here, not counted as new results. The 28 October source note deliberately leaves the known analytic density theorem as an explicit hypothesis; this continuation respects that decision.

## 1. Complete squarefree covariance: complex symmetry and spectral consequences

Let S be any finite set of positive squarefree integers. Frequency 1 may be included or omitted. Let
$$
W_{nm} = \begin{cases}
\Lambda(m/n)/\sqrt{m/n},& n<m,\ n\mid m,\\
\Lambda(n/m)/\sqrt{n/m},& m<n,\ m\mid n,\\
0,&\text{otherwise},
\end{cases}
\qquad B=-\frac{W}{2\pi}.
$$
Here Lambda is the ordinary von Mangoldt function. Set
$$
Q_S(a)=\operatorname{Re}\sum_{n,m\in S}\overline{a_n}B_{nm}a_m,
\qquad (Ma)_n=\mu(n)a_n .
$$

The pre-existing arithmetic lemma proves that a nonzero edge on squarefree support has prime ratio, and that the two Möbius signs are opposite. The new complex extension and finite-sum assembly establish
$$
MBM=-B,\qquad BM=-MB,\qquad
Q_S(Ma)=-Q_S(a),\qquad \|Ma\|_2^2=\|a\|_2^2
$$
for arbitrary complex coefficients, with all composite vertices and support boundaries retained.

Consequences checked in Lean:

* If Ba=z a on S, then B(Ma)=-z Ma. A vector nonzero on S remains nonzero after twisting.
* A uniform upper quadratic bound Q_S(a)<=C||a||_2^2 for all complex a is equivalent to the matching lower bound Q_S(a)>=-C||a||_2^2.
* For b_n>=0, the previously established exact identity
  $$
  Q_S(\mu b)=\frac1{2\pi}\sum_{n,m\in S}W_{nm}b_nb_m
  $$
  is now strengthened to strict positivity whenever one active edge has b_n b_m>0.

Thus a universal sign estimate for the full arithmetic correction cannot be obtained merely by exploiting its signed notation. A coefficient-specific estimate for the actual optimized family remains possible and is the relevant target.

The reflected eigenvector equations and nonzero preservation are checked. This does not claim completion of the separate general prime-tower inertia classification.

## 2. Quantitative stability and exact characterization of cancellation

For an arbitrary finite Hermitian complex kernel B, write
$$
Q_B(a)=\operatorname{Re}(a^*Ba),\qquad
\delta_i\ge |(Ba)_i|.
$$
The existing exact equality
$$
Q_B(a+h)=Q_B(a)+2\operatorname{Re}(h^*Ba)+Q_B(h)
$$
is retained. The new checked bounds are
$$
|Q_B(a+h)-Q_B(a)-Q_B(h)|
\le 2\sum_i |h_i|\delta_i
$$
and, if |Q_B(h)|<=C,
$$
|Q_B(a+h)-Q_B(a)|\le 2\sum_i|h_i|\delta_i+C.
$$

A new converse supplies the exact criterion:
$$
[\forall h,\ Q_B(a+h)=Q_B(h)]\quad\Longleftrightarrow\quad Ba=0.
$$
For the nontrivial direction, h=0 gives Q_B(a)=0; testing h=Ba then gives
2||Ba||_2^2=0. No positive-definiteness assumption on B is needed.

The full squarefree application also retains the zero diagonal. If |B_nm|<=eta for distinct support indices, its checked perturbation budget is
$$
|Q_S(a+h)-Q_S(a)|
\le 2\sum_{n\in S}|h_n|\delta_n
+\eta\left[\left(\sum_{n\in S}|h_n|\right)^2
-\sum_{n\in S}|h_n|^2\right].
$$
This is valid for arbitrary complex perturbations. It does not assume that a is a kernel vector or discard a norm-square remainder.

Wolfram independently checked the diagnostic three-coordinate example:
for a=(1,-r/2,1), Q=c a^*(I-K_r)a=0, whereas adding t to the middle coordinate gives exactly -4crt. This calculation is corroborative only; no Wolfram output is a proof dependency.

## 3. A stronger arithmetic peak bound

For positive integers m,n,q, assume
$$
q\le 2n/m,\qquad n\ne mq.
$$
The existing logarithmic separation theorem implies 1/|log(n/(mq))|<=2n.
The new result keeps the exact integer mismatch:
$$
\boxed{\frac1{|\log(n/(mq))|}\le\frac{2n}{|n-mq|}.}
$$
Combining it with the checked exact identity
$$
\frac{2n}{\sqrt{n/m}}=2\sqrt m\sqrt n
$$
gives
$$
\boxed{\frac1{\sqrt{n/m}\,|\log(n/(mq))|}
\le\frac{2\sqrt{mn}}{|n-mq|}.}
$$
The weaker bound 2sqrt(mn) is also checked. No primality or prime-power assumption on q is needed. The proof combines the tangent inequality for log with the integer gap and preserves the denominator instead of immediately replacing it by one.

This sharpens a finite arithmetic ingredient. It is not itself a complete actual-zeta remainder theorem or a proved larger support range.

## 4. What remains between these results and RH

1. **Actual optimized coefficients.** Relate the actual legal squarefree optimizer to a comparison family while controlling the action defect Ba, the perturbation magnitudes, and the complete quadratic remainder. Möbius signs alone give a nonnegative arithmetic correction and generally a strictly positive one.
2. **Use the mismatch denominator in a full error sum.** Combine the new gap-dependent peak estimate with the complete signed Landau expansion and sum the actual coefficient-weighted errors. Establish an explicit support range; do not replace a fixed-support conclusion by a growing-support one.
3. **Supply an RH-sensitive estimate.** The fixed-frequency phase law and sublinear horizontal energy allow finitely many off-line zeros. A proof must control tests that detect an individual off-line zero, or prove the existing actual legal-closure/optimizer-growth condition.
4. **Keep the analytic premise visible.** The known Selberg/Conrey–Baluyot density input is intentionally deferred as recorded in ActualZeroSelbergDensity.lean. Neither the present finite results nor an axiom audit discharge that hypothesis.
5. **Separate finite spectral work.** The squarefree eigenvalue reflection is completed here. The general Kac–Murdock–Szegő inverse/congruence/inertia and prime-tower kernel classification still require their own complete formalization.

Published analytic context: Ford–Meng–Zaharescu, Lemmas 1–2,
https://arxiv.org/pdf/1511.06814, provides the Landau and restricted-range phase comparison used in the original agenda. The present algebraic proofs do not assume those lemmas. No novelty claim is made.

## 5. Source and verification ledger

Nineteen new theorem declarations are added to three existing modules:

* Analysis/HermitianQuadraticPerturbation.lean: four quantitative/characterization results.
* Analysis/SquarefreeSignedCovariance.lean: ten complex, spectral, strict-positivity and perturbation results.
* Analysis/RationalLogSeparation.lean: five inverse-peak, exact-weight and gap-sensitive estimates.

All use the existing exact definitions. No sorry, admit, project-local axiom, or unsafe declaration is introduced. An axiom audit was requested during development but no completed audit is asserted in this ledger; the final checkpoint is the authoritative source-validation and publication result. The root module already exports these three modules.

Successful development jobs include:
* job_BFyh4NpT5miiZD3a22nKMBtbB7bbfsEM: general quantitative stability and kernel equivalence, 4.298 seconds reported by server.
* job_UZLUohupe7j16xRdlMrSx4MMvfNOTaOo: complex squarefree consequences using the existing arithmetic proof, 59.547 seconds reported by server.
* job_CGuTsbe05q0abaVZCKr0m0vkKre5L8xL: sharper arithmetic peak bounds, 4.668 seconds reported by server.

These times are server-reported job execution, not measured kernel-only times. Workspace-opening request latency was not separately instrumented. The jobs were serialized; observed queue-start delays were below one second, while the server required 30- or 60-second polling intervals. Final source acceptance and publication are controlled by the subsequent checkpoint and its terminal result, which are reported to the user separately.

The old handoff checkpoint job_Q0yYR1bboekEDKbgU5AuMZoEWcah0_r9 was recovered as a terminal Git clone network failure. Current main already contained the rescued modules; this development starts from main commit a7bfa6cdabeb9c4cacfd99cbc4725c16c58fff21 in workspace ws_BJkNzN9gtEOLYyot5qVqv8MbqxLyt8z_.
