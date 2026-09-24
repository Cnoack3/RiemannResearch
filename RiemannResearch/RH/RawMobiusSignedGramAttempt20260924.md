# RH attempt: signed Gram energy and large-sieve tail
Date: 2026-09-24
Base: d494d53c08c9c10c2ad3fe10eada8a1ac3ee4487

## Outcome

This attempt does not prove unconditional RH. It proves additional
unconditional structure for the actual arithmetic energy, isolates the exact
remaining signed correlation bound, and derives a classical-large-sieve
far-tail theorem in a separately audited mathematical proof.
The latter is only partly formalized in Lean.

No external result is introduced as an axiom. No conditional theorem is
reported as an unconditional proof of its conclusion.

## The actual signed Gram decomposition

Write
\[
r_d(k)=\frac{k\bmod d}{d},\quad
g_d=\mu(d)r_d,\quad
U_N=1+\sum_{d\le N}g_d,\quad
L_N=\sum_{d\le N}\frac{\mu(d)\log d}{d}.
\]
All norms and inner products below are the actual Pareto ones, with weights
\(1/[k(k+1)]\). Define
\[
D_N=\sum_{d\le N}\|g_d\|_P^2,\qquad
Q_N=\sum_{\substack{d,e\le N\\d\ne e}}\langle g_d,g_e\rangle_P.
\]
Every ordered distinct pair, its sign, and the entire physical tail are retained.

**Kernel-verified** in RawMobiusSignedGramEnergy.lean:
\[
\boxed{\|U_N\|_P^2=1+2L_N+D_N+Q_N,\qquad 0\le D_N\le2H_N.}
\]
The previously checked classical logarithmic Möbius mean gives \(L_N\to-1\).
Combining these facts with the exact budget comparisons yields, eventually,
\[
\boxed{Q_N-4\le B_N\le2Q_N+4H_N.}
\]

For each fixed \(\varepsilon>0\), Lean now proves the exact equivalence
\[
\begin{aligned}
&\exists C,\ \text{cofinally many }N:
 B_N\le C(N+1)^\varepsilon\\
&\quad\Longleftrightarrow
\exists C,\ \text{cofinally many }N:
 Q_N\le C(N+1)^\varepsilon.
\end{aligned}
\]
The constants and cofinal sets on the two sides need not be identical.
Thus upper subpower control of the actual signed off-diagonal energy would
prove RH through the existing budget criterion.

**Open:** this arithmetic upper estimate on \(Q_N\). The verified logarithmic
diagonal bound does not supply it. Positivity of a Gram matrix controls the
total quadratic form from below and does not give the missing upper estimate
for this growing signed coefficient family.

## Unconditional cancellation with every fixed head

NaturalMobiusSourceLimits.lean now proves that every fixed raw head is a
vanishing test of \(U_N\). For \(W_N=\sum_{d\le N}g_d\) and each fixed \(M\),
\[
\langle U_N,W_M\rangle_P\to0,\qquad
\boxed{\langle W_N-W_M,W_M\rangle_P\to-L_M-\|W_M\|_P^2.}
\]
The Lean statements use rawMobiusHilbert \(=-W_N\); the rectangle inner
product is unchanged when both signs are reversed.

These are unconditional limits of complete signed fixed-head/expanding-tail
rectangles. Their quantifier keeps \(M\) fixed. They do not justify putting
\(M=N\), and do not control the block where both indices grow.

## Exact completed-budget correction

RawMobiusBudgetQuantitative.lean now proves
\[
B_N+T_N-\|U_N\|_P^2\longrightarrow0,
\qquad
T_N=\sum_{k>N^2}\frac{U_N(k)^2}{k(k+1)}.
\]
Its proof uses the already established exact identity
\[
B_N+T_N-\|U_N\|_P^2=m_N^2(H_{N+1}-1)
\]
and the existing unconditional square-harmonic Möbius decay.
The far tail remains present in this Lean theorem.

## A stronger far-tail theorem using established large-sieve mathematics

The independently audited proof in
[RawMobiusFarTailLargeSieve20260924.md](RawMobiusFarTailLargeSieve20260924.md)
derives
\[
T_N\le\frac{2A_N^2+(N/6)H_N^2}{N^2+2}\longrightarrow0,
\qquad
A_N=1+\frac{M_N-m_N}{2},\quad M_N=\sum_{d\le N}\mu(d).
\]
It uses exact finite Fourier/CRT covariance, the dual additive large sieve,
and Abel summation. The primary reference for the large-sieve input is
E. Kowalski, *Amplification Arguments for Large Sieve Inequalities*, equations
(2)–(3), pp. 1–2:
https://people.math.ethz.ch/~kowalski/two-remarks-large-sieve.pdf .

The complete theorem is proved in the mathematical note, **not yet
kernel-verified in Lean**. The formalization completed here consists of:
- reciprocal_energy_sum_le_of_prefix;
- reciprocal_energy_tsum_le_of_prefix;
- rawMobiusFarEnergy_le_of_prefix.

The last theorem controls the actual infinite physical tail from its explicit
finite-interval mean-square premise. The arithmetic Fourier/CRT and
large-sieve providers for that premise remain to be formalized.
They are established mathematical inputs, distinct from the genuinely open
subpower bound on the middle window.

The note also proves, by exact continuous cells, that the classical raw
Nyman–Beurling energy \(E_N\) satisfies \(E_N-B_N\to0\).
That continuous identification is not formalized in this batch.

## Why the attempted RH proof stops

The standard large sieve supplies control beyond the \(N^2\) scale.
RH's unresolved estimate concerns the actual middle window \(N<k\le N^2\).
Extending a long-interval average bound to that shorter window without
retaining its \(N^2\) loss would be an unjustified step.

Similarly, convergence against each fixed residue or fixed Möbius head does
not bound the growing Gram sum. This attempt does not establish the required
cofinal upper subpower bound on \(Q_N\), and consequently does not establish RH.

## Verification and next exact task

The signed Gram and fixed-head declarations, completed-budget correction,
and Abel transfer were kernel-checked in serialized snippets. Their printed
dependencies contain only propext, Classical.choice, and Quot.sound.
The assembled project is accepted and published through one checkpoint.

Next formalization: construct the collected rational Fourier coefficients,
identify their squared norm with the signed CRT mean square, and provide the
dual large-sieve estimate needed by rawMobiusFarEnergy_le_of_prefix.

Next research obligation: prove upper subpower growth of the actual moving
off-diagonal sum \(Q_N\) on cofinal cutoffs for every positive exponent.
This remains Open.
