# Complete physical mean-one packet advance — 8 October 2026

This continues `CriticalZeroMeanOneAdvance20261008.md` and commit
`9d216a284767a4bb302e444297cc3e6b5cc8f000`. The work uses the actual Pareto
weights rho(k)=1/[k(k+1)] at positive integers, without a finite-tail truncation.

## Arithmetic core and physical specialization

For a positive common period Q define cot_Q(r)=cot(pi*r/Q) for 0<r<Q,
with cot_Q(0)=cot_Q(Q)=0, and
h_ab(r)=R_a(r)R_b(r)−(b−1)R_a(r)/2−(a−1)R_b(r)/2, where R_a(r)=r mod a.
The independently defined finite residue core is

    F_Q(a,b) = (1/(2Q)) sum_{0<=r<Q} h_ab(r)[cot_Q(r)−cot_Q(r+1)].

Endpoint products vanish explicitly. Digamma reflection and the complete
progression weights prove

    <R_a,R_b>_P = pi F_Q(a,b)
                 + [(b−1)log a+(a−1)log b]/2.

The complete signed double Möbius divisor expansion gives the arithmetic packet
core and actual Gram identity Gamma=pi F+(lambda phi^T+phi lambda^T)/2.
The finite arithmetic core equals the independently Gram-derived core.
Its value is independent of the chosen positive common period.

The finite cotangent multiplication theorem and summation by parts also give

    F_Q(a,b) = -[V(a,b)+V(b,a)-V(1,a)-V(1,b)]/2.

The simultaneous-divisibility term in the first difference is retained and
then cancels by cotangent reflection; no coprimality premise is introduced.
Only after that contraction do the two single-conductor terms cancel in the
complete Möbius sum for packet conductors greater than one. This identifies
the actual physical core with the previously specified
`ramanujanCotangentCoreEntry`, rather than merely naming a Gram-derived core.
Pairwise product periods discharge every period premise in this identity.

Actual packet independence proves strict positivity on phi-perp. At every odd
prime p the full physical norm retains the first-site deficit and gives
F_pp <= −(p−2)/(2pi)<0. Thus every squarefree divisor stage L>2 has nonsingular
core, negative charge C=phi^T F^-1 phi, and an exact Lorentz decomposition into
one negative scalar square and the positive mean-zero kernel. This is the
formal inertia statement; no eigenvalue-count API is invoked.

The literal ordinary period mean of synthesis is phi^T c/2. Therefore the
mean-one constraint is actual ordinary mean one, and both logarithmic terms
cancel in the complete physical error:

    E(c)=1+pi c^T F c,
    c0=2 F^-1 phi/C,
    E0=1+4pi/C.

The full correction square proves uniqueness. At L=6 the packet coefficients
(2/3,1/2,1/6) synthesize g_2+g_3+g_6, with C_6=−8sqrt(3) and exact minimum
1−pi/(2sqrt(3)). Wolfram exact arithmetic cross-checks these quantities;
only the Lean declarations constitute their formal proof.

## Ordinary mean-one repair

The genuine normalized-residue repair a_d=2d*g_d/(d−1) has ordinary mean one.
Its complete physical norm satisfies

    ||a_d||^2 < 16d/[3(d−1)^2] <= 64/(3d),  d>1.

An arbitrarily large fresh prime conductor repairs each fixed squarefree
finite packet with arbitrarily small norm. Thus the closure of mean-one
squarefree packets equals the closure of all squarefree packets. This does
not assert that the constant target belongs to the common closure.

## Complete Schur calculation and finite lower floors

The full block elimination retains A'=A+U^T S^-1 U,
B'=B+U^T S^-1 V, and C'=C+V^T S^-1 V. The mixed update is signed.
The actual mean-zero tangent core is S+VV^T/C=S−VV^T/gamma, gamma=−C;
the negative rank-one correction is retained. The exact error gain is
4pi*delta/[gamma*(gamma−delta)], under its stated finite hypotheses.
Positivity alone supplies no uniform gain toward gamma=4pi.

For a bounded L-periodic sequence with zero at multiples of L and ordinary
mean one, let w_r be the complete progression mass and H_L=sum_{1<=r<L}1/w_r.
The exact physical affine completion is

    E=q_L+1/H_L+sum_{1<=r<L} w_r*(e_r+1/(H_L*w_r))^2,

where q_L=w_L and e_r=1−f(r). Hence E>=q_L+1/H_L
>=q_L+3/[L(L^2−1)]. The physical packet reflection additionally forces
f(L−1)=2, giving the separate floor E>=q_L+w_{L−1}.
Corresponding inverse-charge bounds retain these full progression masses.
In particular E>=2/(L^2−1) and
C_L<=−4pi/[1−2/(L^2−1)] whenever the actual odd-prime inertia hypotheses hold.
Actual zero extension of packet coefficients proves constrained-error
antitonicity and charge monotonicity, without a supplied Schur inverse.
For every L>2 divisible by six this gives the unconditional bounds

    −8sqrt(3) <= C_L < −4pi,
    E_L^0 <= 1−pi/(2sqrt(3)).

On every nested divisor chain containing six, the charge converges to some
C_infinity in the closed interval [−8sqrt(3),−4pi]. The formal convergence
theorem does not assume squarefreeness or identify the limiting endpoint.
These upper and lower finite bounds do not drive error to zero or prove
saturation. A paper consequence of the complete mixed updates is
(B_m−B_n)^2 <= (A_m−A_n)(C_m−C_n), under positive complete inverse-Schur
forms. If alpha_n>0 and the separate source limits A_m->0 and B_m->−2pi are supplied, it
implies gamma_infinity <= gamma_n−D_n^2/alpha_n (D=2pi+B, alpha=−A).
This retains the signed source coupling, but does not force gamma_infinity=4pi.
This source-limit consequence is an informal investigation, not a new Lean
provider in this advance.

## Established/open boundary

The cotangent-difference arithmetic identity is proved independently of the
Gram definition, and its complete signed finite contraction identifies the
previously named double-cotangentV core. The originally specified core has
the same inertia, constrained optimizer and exact unique minimum, with no
supplied analytic Gram-identification premise. Algebraicity of rational-angle
entries is separate from these results.

The missing arithmetic limit remains C_L -> −4pi along a cofinal squarefree
family. The sufficient implication from this charge limit to RH is instantiated
through the existing legal physical approximation theorem. The arithmetic
endpoint is an explicit hypothesis of that consumer. The reverse
RH-to-squarefree saturation implication is not supplied by this finite work. The critical-zero obstruction to the coarse stretched
optimizer-tail saving remains in force; that invalid estimate is not used
as an RH provider. No RH proof is claimed.

References supporting the reflection strategy and prior equivalence context:
DLMF 5.5.4, https://dlmf.nist.gov/5.5 ;
Bagchi, https://arxiv.org/abs/math/0607733, Remarks 4 and 8.

All sixteen new modules passed one coherent isolated Lean check (exit code 0).
A transitive axiom audit of all 227 public definitions and theorems permitted
only propext, Classical.choice and Quot.sound. The accompanying
PhysicalMeanOneVerification20261008.json records source hashes, declarations
and the verification job. The publication checkpoint successfully built all
16 affected modules and pushed Lean commit
81ae700c5360cc443d093ff1c829d5c9e3fb102d. The only integration repair was a
direct ParetoNoiseSignal import for paretoError; theorem bodies were unchanged.
