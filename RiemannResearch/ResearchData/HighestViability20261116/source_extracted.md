# Extracted source text

Source URL: https://drive.google.com/file/d/1smLPEbJDfOV2Z5mMSMMQvFEd3_qRYopL/view

This is unverified source material. Extraction may damage mathematical typography.

An audited proof attempt at the RH-level CRT estimate
Exact-head extension, the spectral-correction infimum, and the surviving uniformity obstruction
Research note
23 July 2026
Abstract
We attempt the remaining estimate
Vx,π(x) ≪ x
2
logx
without treating its implication of the Riemann hypothesis as a reason to weaken the attack. The attempt
produces a new unconditional theorem. On the Haar divisor cube we construct an explicit residual
derivative with exactly the required prime coefficients, zero error at every integer 1 ≤ k ≤ x, and optimal-scale derivative energy O(x
2
logx). The construction uses only a (π(x)+1)-dimensional positive-definite
normal equation. Its key input is a quantitative uniform first-chaos frame inequality on the event that the
random squarefree divisor exceeds x. We prove that inequality with four explicit prime-exponent bands,
thereby removing an ambiguity in the earlier “cyclic partition” argument.
This does not prove the RH-level variance estimate. An exact discrete Fourier calculation does,
however, prove the full uniform-period part of the Green norm. Only one explicit fixed-origin weighted
antiderivative estimate remains. We prove that it would close the argument and hence imply RH, and
show exactly why Hardy’s inequality, Haar orthogonality, smooth-number gap theorems, and the cur-rently cited cotangent/Kloosterman estimates do not supply it. Thus the note advances the proof to a
single structured arithmetic discrepancy estimate while making no claim that RH has been proved. We
also separate this full-degree construction from the earlier O(x)-column paired dyadic family: neither is
presently proved to approximate the other at the RH scale.
Finally, we execute the proposed common-divisor and Kloosterman-fraction reduction. An upper
Mobius transform converts the Ramanujan coefficients to explicit grid coefficients, after which every ¨
cotangent term splits canonically as d = gm,e = gn, with g,m,n pairwise coprime. The exact finite
Fourier expansion does match Bettin–Chandee term by term, but its long phase range makes their bound
worse than the elementary estimate in the balanced boxes. We then complete the signed reciprocity
step: the logarithmic Vasyunin main term cancels HxBx exactly, and the whole variance becomes a
multiplicative fractional-part Gram form minus H
2
x
. Mellin–Plancherel converts it to one exact critical-line integral. Finally, the associated Dirichlet polynomial factors into a first-chaos polynomial minus
a head-weighted finite inverse Euler product. This does not prove the target, but it identifies the most
structured surviving estimate without discarding the cancellation. We then execute the first proposed
Mellin block 1 ≤ |t| ≤ 4. The normal equation gives an exact scalar Schur formula, but the direction-free
Riesz factor required by a subsequent Cauchy–Schwarz step is exponentially unbounded along subse-quences. Larger finite tests exhibit the corresponding inverse-Euler resonances. This forces a revision
of the proof strategy: the best surviving program is to add a moment-null higher-chaos correction on
the free tail and optimize the spectral block directly. We carry out that optimization here. The con-strained infimum has an exact trust-region dual formula, and projected degree-two seeds give an explicit
polynomial-dimensional subspace of the moment-null tail. We then compress the entire
π(x)
2

-column
problem exactly to an O(x)-dimensional head Schur kernel and prove that the simpler diagonal pair
energy is a sufficient majorant. With diagonal budget x
2
logx, the independently validated residual on
1 ≤ |t| ≤ 4 is below 0.012x
2
logx at every tested prime cutoff through x = 2999, even where the uncor-rected block reaches 9.15 · 104
x
2
logx. This is strong finite evidence and narrows the open problem to
one explicit signal-direction kernel estimate; it is not a uniform theorem and does not prove RH.
11 Outcome and proof status
Status Result
Proved The unconditional baseline Vx,d ≪ x
3
; the signal-specific
fixed-degree obstruction; a quantitative uniform first-chaos frame
inequality on the free-divisor event; and an explicit exact-head
mixed trial whose Haar derivative energy is O(x
2
logx). The
complete uniform-period Green term is also O(x
2
logx).
Proved audit The simple feasible trial supported on Px/p and Px has error ≫ x
3
,
so feasibility at very late atoms cannot yield the target.
Proved block reduction The block 1 ≤ |t| ≤ 4 has the exact normal-equation formula (46).
The direction-free Riesz factor needed after Cauchy–Schwarz is
exponentially unbounded along subsequences, so optimal Haar
energy alone cannot close this block.
Proved infimum formula The energy-constrained spectral correction is an exact
finite-dimensional trust-region problem. Its minimizer, minimum
value, and projected degree-two Gram and spectral matrices are
given explicitly in theorems 7.11 and 7.12. The full pair Gram
inverse also has the exact O(x)-head compression (66), and
G
(2)
x ≤ D2.
Open The uniform diagonal pair-kernel estimate (71). It would give
correction energy O(x
2
logx) and block residual O(x
2
logx). Finite
optimization verifies the desired scale through x = 2999, but no
asymptotic bound is proved.
2 The target and a rigorous baseline
Put
P = Px = ∏
p≤x
p, Jq = ∑
m|q
µ(q/m)(K mod m),
where
P(K = k) = 1
k(k +1)
(k ≥ 1).
Let
Zx = ∑
p≤x
(log p)Jp, Hx = ∑
p≤x
(log p)
2
.
For
Mx,d = {q | P : q squarefree, 2 ≤ ω(q) ≤ d},
the scalar residual is
Vx,d = inf
b
Var Zx − ∑
q∈Mx,d
bqJq
!
. (1)
The parent manuscript proves that
d(x) −→ ∞, Vx,d(x) ≪ x
2
logx (2)
implies RH.
2Proposition 2.1 (Unconditional baseline). Uniformly for every admissible d,
Vx,d ≪ x
3
.
Proof. The competitor b = 0 gives Vx,d ≤ Var(Zx) ≤ EZ
2
x
. Since Jp = K mod p, for K = k ≤ x,
0 ≤ Zx(k) ≤ kϑ(x), ϑ(x) = ∑
p≤x
log p,
whereas for every k,
Zx(k) ≤ ∑
p≤x
plog p.
Consequently
EZ
2
x ≤ ϑ(x)
2 ∑
k≤x
k
2
k(k +1)
+

∑
p≤x
plog p
!2
P(K > x)
≪ xϑ(x)
2 +x−1

∑
p≤x
plog p
!2
≪ x
3
,
by Chebyshev’s bound ϑ(x) ≪ x, partial summation, and P(K > x) = 1/(x+1).
Thus the desired theorem must save a factor of order x/logx over a direct second-moment estimate.
Proposition 2.2 (The pair obstruction is already signal-specific). For the pair cutoff,
Vx,2 ≥
H
2
x
2620
.
In particular Vx,2 ̸≪ x
2
logx.
Proof. The audited ten-point functional
L2(f) = f(1) + f(2)−2 f(5) + f(6)− f(9) + f(10)− f(14) + f(15) + f(29)− f(30)
has squared norm 2620, satisfies L2(1) = 1, and annihilates every Jp and Jpq. Therefore, for every pair trial
T = Zx −∑bpqJpq,
L2(T −Hx) = −Hx.
Cauchy–Schwarz gives ∥T −Hx∥
2 ≥ H
2
x /2620. Taking the infimum proves the claim. Since Hx ≍ x logx,
the last assertion follows.
3 A failed explicit trial: late feasibility is not cancellation
The exact-head formulation uses Haar gcd atoms
wd = PR mod P((R,P) = d) = ϕ(P/d)
P
=
ax
ϕ(d)
, ax =
ϕ(P)
P
.
One simple feasible constraint vector is supported on P/p and P. Writing
T = Hxax, mp =

1−
1
p

log p, zd = wdud,
it is
zP/p = T −mp, zP = ∑
p≤x
mp −(π(x)−1)T.
3Proposition 3.1 (The late-atom trial loses the required factor). For all sufficiently large x, the weighted
squared exact-head error of this trial is ≫ x
3
.
Proof. Let pmax be the largest prime not exceeding x. Since P/pmax > 2x for all sufficiently large x, none of
the atoms P/p or P occurs before 2x. Hence on 1 ≤ r ≤ 2x the error is
HxC(r), C(r) = #{2 ≤ n ≤ r : (n,P) = 1}.
For 3x/2 ≤ r ≤ 2x, every integer counted by C(r) is a prime greater than x, and the prime number theorem
gives
C(r) ≥ π(3x/2)−π(x) ≫
x
logx
.
The Pareto residue weight is at least 1/[r(r + 1)] ≫ x
−2
. There are ≍ x integers in this interval, so the
weighted squared error is at least
H
2
x

x
logx
2
x
x
2 ≫ x
3
.
This rules out a tempting but invalid strategy: satisfying the moment constraints on atoms that occur
only near the end of a primorial period.
4 The free-divisor frame theorem
Let Ip, p ≤ x, be independent Bernoulli variables with
P(Ip = 1) = 1
p
, D = ∏
p≤x
p
Ip
.
This is exactly the Haar law of (R,P). Define
X0 = 1, Xp = pIp −1.
Then
EXp = 0, EXpXq = 0 (p ̸= q), EX
2
p = p−1. (3)
Theorem 4.1 (Uniform first-chaos mass on D > x). There is an absolute c > 0 such that, for all sufficiently
large x and all complex coefficients a0,(ap)p≤x,
E

1D>x





a0 + ∑
p≤x
apXp





2

 ≥ c

|a0|
2 + ∑
p≤x
(p−1)|ap|
2
!
. (4)
Proof. Put
βj =

51
1001−j/4
(0 ≤ j ≤ 4)
and split the primes in x
β0 < p ≤ x into the four explicit bands
Cj = {p : x
βj−1 < p ≤ xβj} (1 ≤ j ≤ 4).
4Mertens’ theorem for reciprocal primes gives, for each fixed j,
∑
p∈Cj
1
p
= log
βj
βj−1

+o(1) = 1
4
log
100
51
+o(1).
Consequently, for all sufficiently large x, every displayed sum is at least
σ =
1
8
log
100
51
> 0.
Take A1 = C1,A2 = C2,B1 = C3,B2 = C4, put all remaining primes into either side, and thereby extend
A1 ∪A2 and B1 ∪B2 to a partition A∪B of all primes up to x.
Let EA be the event that at least one prime from each of A1,A2 is selected. The two selections have
product greater than x
1.02 > x. Independence and
P(some p ∈ S is selected) = 1−∏
p∈S

1−
1
p

≥ 1−exp − ∑
p∈S
1
p
!
show that P(EA) ≥ η > 0, with an absolute η. Likewise an event EB, depending only on the B-coordinates,
has probability at least η, and both EA,EB imply D > x. In fact one may take
η = (1−e
−σ
)
2
.
Write
Y = a0 +YA +YB, VA = E|YA|
2
, VB = E|YB|
2
, V = VA +VB.
If VA ≥ V/2, then on the independent event EB,
EA|a0 +YB +YA|
2 = |a0 +YB|2 +VA ≥ VA.
Thus E[1D>x|Y|
2
] ≥ ηV/2. The same conclusion follows from EA when VB ≥ V/2.
It remains to control the constant coefficient. Put ρ = P(D > x) ≥ η and Z = Y −a0. If V ≤ ρ|a0|
2/4,
then
|E[1D>xZ]| ≤ (ρV)
1/2 ≤
ρ|a0|
2
.
Hence
E[1D>x|Y|
2
] ≥
|E[1D>xY]|
2
ρ
≥
ρ|a0|
2
4
.
If V > ρ|a0|
2/4, the previously proved lower bound for V controls |a0|2 +V, because
|a0|
2 +V <

1+
4
η

V.
Thus (4) holds, for example, with the explicit constant
c = min
η
5
,
η
2
2(η +4)

.
Numerically this certified choice is c > 5.29 · 10−6.
Remark 4.2. The proof is uniform in the direction (a0,ap). It is stronger than the signal-state comparison
actually needed below and uses no zeta zero, cotangent estimate, or unproved independence assumption.
55 A proved exact-head trial at the correct Haar scale
Let
Ax = {d | P : d ≤ x}, Ux = {d | P : d > x}.
For functions on the positive integers, fix the convention ∆f(k) = f(k)− f(k −1). Regard
X = (X0,(Xp)p≤x)
T
as a column vector and put
Dx = E[XXT] = diag1,(p−1)p≤x

, Mx = E[1D>xXXT].
By theorem 4.1,
Mx ≥ cDx > 0. (5)
Henceforth x is sufficiently large for (5); all vectors and matrices in the construction below are real.
Define the prime signal derivative
Sx(D) = ∑
p≤x
(log p)Xp(D)
and prescribe on the arithmetic head
Φhead(1) = −Hx, Φhead(d) = 0 (1 < d ≤ x).
Put
gx(D) = Sx(D)−Φhead(D) (D ∈ Ax), (6)
hx = E[1D≤xgx(D)X(D)], (7)
vx = M−1
x hx, ∆x(D) = 1D>xv
T
x X(D). (8)
Finally define
Φx(D) = (
Φhead(D), D ≤ x,
Sx(D) +∆x(D), D > x.
(9)
Theorem 5.1 (Exact-head first-chaos extension). For all sufficiently large x, the function Φx is well defined
and satisfies
EΦx = 0, (10)
E[ΦxXp] = (p−1)log p (p ≤ x), (11)
E|Φx|
2 ≪ x2
logx. (12)
Its Haar Ramanujan expansion
Φx(D) = ∑
q|P
αqcq(D), αq =
E[Φxcq]
ϕ(q)
has
α1 = 0, αp = log p.
6Consequently, with bq = −αq for ω(q) ≥ 2,
Wx = ∑
p≤x
(log p)Jp − ∑
q|P
ω(q)≥2
bqJq = ∑
q|P
q>1
αqJq
is an admissible full mixed trial, has mean Hx, and obeys
Wx(k) = Hx (1 ≤ k ≤ x).
Proof. Equations (7)–(8) give
E[1D>x∆xX] = Mxvx = hx.
Thus
E[(Φx −Sx)X] = E[1D≤x(Φhead −Sx)X] +E[1D>x∆xX] = −hx +hx = 0.
Taking the X0 and Xp coordinates, and using (3), proves (10) and (11).
The extension energy is
E[1D>x|∆x|
2
] = h
T
x M−1x hx ≤ c
−1
h
T
x D
−1
x hx.
By Bessel’s inequality for the orthogonal family (X0,Xp),
h
T
x D
−1
x hx ≤ E[1D≤x|gx(D)|
2
].
Moreover
E|Sx|
2 = ∑
p≤x
(p−1)(log p)
2 ≪ x2
logx,
while Mertens’ product theorem and Hx ≪ x logx give
P(D = 1)H
2
x =
ϕ(P)
P
H
2
x ≪ x
2
logx.
Equations (6) and (9), followed by the triangle inequality in L
2
, now prove (12).
For squarefree q,
cq(D) = ∏
p|q
Xp(D),
and the Ramanujan functions are Haar-orthogonal with squared norm ϕ(q). Therefore the displayed expan-sion is exact. Equations (10)–(11) give the constant and prime coefficients. The definition of bq then gives
the displayed trial.
For completeness, if m ≥ 2, Abel summation for the bounded function k mod m gives
E(K mod m) = lim
N→∞

HN −H⌊N/m⌋

= logm.
Consequently
EJq = ∑
m|q
µ(q/m)logm = Λ(q).
Thus the prime terms have means (log p)
2
, while every squarefree mixed term has mean zero, proving
EWx = Hx.
Finally, ∆Jq = −cq, so ∆Wx(k) = −Φx((k,P)). For k ≤ x, (k,P) ≤ k. Hence the first difference is Hx at
k = 1 and zero for 2 ≤ k ≤ x. Since every Jq(0) = 0, this proves Wx(k) = Hx on the whole head.
7Proposition 5.2 (Canonical minimum-energy completion). Among all corrections δ supported on D > x
and satisfying
E[1D>xδX] = hx,
the choice δ∗ = v
T
x X is the unique L2
-minimum-energy completion of the fixed head with the prescribed
constant and prime moments. Moreover
E|Φx|
2 ≍ x2
logx.
Proof. Write Φ(δ) for the global completion obtained by using δ on D > x. For any other admissible δ,
E[1D>x(δ −δ∗)X] = 0.
Since Sx+δ∗ is first chaos on D > x, the difference is orthogonal to it. The head is unchanged, so Pythagoras
gives
∥Φ(δ)∥
2
2 = ∥Φ(δ∗)∥
2
2 +E[1D>x|δ −δ∗|
2
].
This proves minimality and uniqueness up to Haar-null sets. The upper energy bound is (12). For the lower
bound, Parseval and the fixed prime coefficients give
E|Φx|
2 ≥ ∑
p≤x
(p−1)(log p)
2 ≍ x2
logx.
Proposition 5.3 (On-demand formula for every mixed coefficient). Put ax = ϕ(P)/P. For every squarefree
q | P with ω(q) ≥ 2,
αq = −
ax
ϕ(q) ∑
d|P
d≤x

gx(d) +v
T
x X(d)

cq(d)
ϕ(d)
. (13)
Thus the exponentially indexed coefficient vector need not be stored: each coefficient is the transform of the
O(x) squarefree head values and the single (π(x) +1)-dimensional solution vx.
Proof. Globally,
Φx = Sx −1D≤xgx +1D>xv
T
x X.
If ω(q) ≥ 2, the first-chaos functions Sx and v
T
x X are orthogonal to cq. Since 1D>x = 1 − 1D≤x, it follows
that
E[Φxcq] = −E
-
1D≤x

gx +v
T
x X

cq

.
Finally P(D = d) = ϕ(P/d)/P = ax/ϕ(d) for d | P. Dividing the resulting finite sum by ϕ(q) proves
(13).
Corollary 5.4 (What has genuinely been gained). The residual derivative has the exact prime signal, uses
only admissible mixed conductors, vanishes after its initial head jump, and satisfies the Parseval bound
∑
q|P
ϕ(q)|αq|
2 = E|Φx|2 ≪ x2
logx.
The exponentially large mixed coefficient vector is generated by the (π(x) +1)-dimensional system Mxvx =
hx.
Remark 5.5 (Compatibility boundary with the completed N1 construction). The smooth paired N1 family
has only O(x) coefficient columns, whereas (13) generally has nonzero entries at all Boolean degrees. No
argument here places this exact-head vector in the paired column space, and no argument in the N1 theorem
proves that the paired projection approximates it with error O(x
2
logx). The two constructions are therefore
complementary candidates, not interchangeable proofs of the same estimate.
86 The fixed-origin term that survives
Let
Ex(r) = Wx(r)−Hx.
By theorem 5.1, Ex(r) = 0 for 1 ≤ r ≤ x. For 1 ≤ r ≤ P, define the exact residue weight
ωP(r) = ∑
j≥0
1
(jP+r)(jP+r +1)
.
Then
Var(Wx) =
P
∑
r=1
ωP(r)|Ex(r)|
2
.
Lemma 6.1 (Two-term form of the Green obligation). Uniformly for 1 ≤ r ≤ P,
1
r(r +1)
≤ ωP(r) ≤
1
r(r +1)
+
ζ (2)
P2
.
Consequently it is enough to prove
P
∑
r=x+1
|Ex(r)|
2
r
2
+
1
P2
P
∑
r=1
|Ex(r)|
2 ≪ x2
logx. (14)
Proof. The j = 0 summand is 1/[r(r +1)]. For j ≥ 1,
1
(jP+r)(jP+r +1)
≤
1
j
2P2
.
Summation proves the weight bounds. Since 1/[r(r+1)] ≤ 1/r
2
, (14) implies the required variance estimate.
Theorem 6.2 (The uniform-period Green term). For the exact-head trial of theorem 5.1,
1
P2
P
∑
r=1
|Ex(r)|
2 ≪ x2
logx. (15)
Proof. For a P-periodic function F, use the normalized transform
Fb(h) = 1
P
P
∑
r=1
F(r)e
−2πihr/P
(0 ≤ h < P).
The Ramanujan identity
cq(r) = ∑
a mod q
(a,q)=1
e
2πiar/q
shows that, if h ̸= 0 has exact additive conductor
q =
P
(h,P)
,
then Φx\((·,P))(h) = αq. Since ∆Ex = −Φx((·,P)),

1−e
−2πih/P

Ebx(h) = −αq.
9Parseval and grouping the nonzero frequencies by their exact conductor give
1
P2
P
∑
r=1
|Ex(r)|
2 =
|Ebx(0)|
2
P
+
1
12P ∑
q|P
q>1
q
2∏
p|q

1−
1
p
2

|αq|
2
. (16)
Indeed,
∑
a mod q
(a,q)=1
1
|1−e
2πia/q
|
2
=
q
2
12 ∏
p|q

1−
1
p
2

.
This follows by Mobius inversion from ¨ ∑
q−1
a=1
csc2(πa/q) = (q
2 −1)/3.
The average of Jq over a complete period is ϕ(q)/2 for q > 1. Hence
Ebx(0) = 1
2 ∑
q|P
q>1
ϕ(q)αq −Hx.
Cauchy–Schwarz, ∑q|P ϕ(q) = P, and ∑q ϕ(q)|αq|
2 ≪ x2
logx show that the first term on the right of (16) is
≪ x
2
logx+
H
2
x
P
.
For the nonzero term, divide its q-summand by the Parseval weight ϕ(q)|αq|
2
. The resulting factor, apart
from 1/12, is
w(q) = q
P ∏
p|q

1+
1
p

.
If q ≤ P/logx, Mertens’ product theorem gives
w(q) ≤
1
logx ∏
p≤x

1+
1
p

≪ 1.
These conductors therefore contribute O(x
2
logx).
It remains to dispose of q > P/logx. For any function F on the divisor cube, successive averaging in
the coordinates dividing q gives the finite-difference identity
E[F(D)cq(D)]
ϕ(q)
=
1
q
E{Ip:p∤q}∆qF,
where ∆q is the alternating Boolean difference in the ω(q) coordinates dividing q. Consequently
|αq| ≤ 2
ω(q)
q
∥Φx∥∞
. (17)
The frame estimate and the extension-energy proof imply
v
T
x Dxvx ≪ x
2
logx.
Also
X(D)
TD−1
x X(D) ≤ 1+ ∑
p≤x
(p−1) + ∑
p≤x
1
p−1
≪
x
2
logx
.
10Cauchy–Schwarz, together with ∥Sx∥∞ ≪ ∑p≤x plog p ≪ x
2
, now gives
∥Φx∥∞ ≪ x
2
. (18)
Write s = P/q. In the high-conductor range, s < logx, so (17) bounds its contribution to (16) by
∥Φx∥
2
∞
P ∑
s|P
s<logx
4
π(x)−ω(s) ≤
∥Φx∥
2
∞
4
π(x)
logx
P
= o(1).
The last equality follows from logP = ϑ(x) ∼ x and π(x) ≪ x/logx. Combining the low conductors, high
conductors, and constant frequency in (16) proves (15).
Conjecture 6.3 (Weighted fixed-origin Green estimate). The explicitly defined Φx in (9), with
Ex(r) = −
r
∑
n=x+1
Φx((n,P)),
satisfies
P
∑
r=x+1
|Ex(r)|
2
r
2 ≪ x
2
logx. (19)
Corollary 6.4. Theorem 6.3 implies
Vx,π(x) ≪ x
2
logx
and therefore implies RH.
Proof. Theorems 6.1 and 6.2 give Var(Wx) ≪ x
2
logx. Since Wx is an admissible mixed trial, Vx,π(x) ≤
Var(Wx). The established one-dimensional sufficient criterion then gives RH.
7 Executing the common-divisor and Kloosterman step
This section carries out steps G3 and G4 from the previous version of this note. The outcome is partly posi-tive and partly negative: the reduction is exact, but a direct termwise application of the strongest applicable
published trilinear theorem loses too much.
7.1 The grid coefficients of the exact-head trial
Extend the notation by putting α1 = 0, and define the upper Mobius transform ¨
γd = ∑
q|P
d|q
µ(q/d)αq (d | P). (20)
Also put
Fx(e) = Sx(e) +v
T
x X(e), Gx(e) = gx(e) +v
T
x X(e) (e ≤ x).
Proposition 7.1 (Exact grid transform). For every integer k and every divisor t | P,
Wx(k) = ∑
d|P
γd(k mod d), (21)
Φx(t) = ∑
d|t
dγd, (22)
dγd = ∑
e|d
µ(d/e)Φx(e). (23)
11In particular,
γ1 = −Hx, γp =
Hx
p
(p ≤ x), (24)
and, whenever ω(d) ≥ 2,
γd = −
1
d ∑
e|d
e≤x
µ(d/e)Gx(e). (25)
Proof. The definition of Jq and a change in the order of summation give
∑
q|P
αqJq(k) = ∑
d|P
(k mod d)∑
q|P
d|q
µ(q/d)αq,
which is (21). The standard divisor formula
cq(t) = ∑
d|q
d|t
dµ(q/d)
similarly proves (22). Divisor Mobius inversion gives (23). The exact head has ¨ Φx(1) = −Hx and Φx(p) = 0,
yielding (24).
Globally,
Φx(e) = Fx(e)−1e≤xGx(e).
If ω(d) ≥ 2, the lower Mobius transform at ¨ d of the first-chaos function Fx is zero. Substitution in (23)
therefore proves (25).
Thus (25), rather than the exponentially indexed αq formula, is the natural coefficient formula for the
Vasyunin kernel.
Proposition 7.2 (Norms furnished by the head construction). One has
∑
e|P
e≤x
ax
ϕ(e)
|Gx(e)|
2 ≪ x2
logx, (26)
∑
d|P
|γd|
2 ≪ x2
(logx)
3
, (27)
∑
d|P
D<d≤2D
|γd|
2 ≪
x
3
(logx)
2
D
(D ≥ 2). (28)
Proof. The first sum is E[1D≤x|Gx(D)|
2
]. The proof of theorem 5.1 gives E[1D≤x|gx|
2
] ≪ x
2
logx and
v
T
x Mxvx ≪ x
2
logx. Since Mx ≥ cDx,
E[1D≤x|v
T
x X|
2
] ≤ v
T
x Dxvx ≪ v
T
x Mxvx.
This proves (26).
For the mixed divisors, Minkowski’s inequality and (25) give

∑
ω(d)≥2
|γd|
2
!1/2
≤ ∑
e|P
e≤x
|Gx(e)|

∑
d|P
e|d
1
d
2


1/2
≪ ∑
e≤x
|Gx(e)|
e
.
12By Cauchy–Schwarz, (26), a
−1
x ≪ logx, and ∑e≤x ϕ(e)/e
2 ≪ logx, the last expression is O(x(logx)3/2
).
The constant and prime terms in (24) contribute O(H
2
x
), proving (27).
For a dyadic interval, the elementary estimate
∑
D<d≤2D
e|d
1
d
2 ≪
1
eD
and Minkowski give

 ∑
D<d≤2D
ω(d)≥2
|γd|
2


1/2
≪ D
−1/2 ∑
e≤x
|Gx(e)|
√
e
.
Another Cauchy–Schwarz application, now using
a
−1
x ∑
e≤x
ϕ(e)
e
≪ x logx,
bounds the last numerator by O(x
3/2
logx). The prime contribution is smaller, and (28) follows.
7.2 Exact common-divisor reduction
For coprime positive integers a,b, let
c0(a/b) = −
b−1
∑
k=1
k
b
cot
πka
b

, V (a,b) = −c0(a/b),
where a is the inverse of a mod b, and set V (a,1) = 0. The rational fractional-part autocorrelation formula
of [1] gives, for squarefree q,r > 1,
Cov(Jq,Jr) = 1
2
{Λ(q)ϕ(r) +ϕ(q)Λ(r)} −Λ(q)Λ(r)
−
π
2 ∑
d|q
e|r
µ(q/d)µ(r/e)(d,e){V (d/(d,e),e/(d,e))
+V (e/(d,e),d/(d,e))}. (29)
Theorem 7.3 (Exact gcd split of the surviving quadratic form). Put
Bx = ∑
q|P
q>1
ϕ(q)αq.
Then
Var(Wx) = HxBx −H
2
x
−
π
2 ∑
gmn|P
(g,m)=(g,n)=(m,n)=1
gγgmγgn{V (m,n) +V (n,m)}. (30)
13Proof. Because the conductors are squarefree,
∑
q>1
Λ(q)αq = ∑
p≤x
(log p)
2 = Hx.
The first line of (29), after summing against αqαr, is therefore HxBx −H
2
x
. In the cotangent part, changing
the order of summation and using (20) gives
∑
d,e|P
γdγe(d,e){V (d/(d,e),e/(d,e)) +V (e/(d,e),d/(d,e))}.
Write g = (d,e), d = gm, and e = gn. Since P is squarefree, g,m,n are pairwise coprime, and this corre-spondence is bijective. This proves (30).
The identity is signed. In particular, the affine term HxBx − H
2
x must not be discarded before possible
cancellation against the two reciprocal Vasyunin terms has been analyzed.
7.3 Signed reciprocity, exact cancellation, and Mellin form
The rational autocorrelation identity of [1] is
A(a/b) = 1−a/b
2
log(a/b) + a/b+1
2
{log(2π)−γ} − π
2b
{V (a,b) +V (b,a)}, (31)
where
A(λ) = Z ∞
0
{t}{λt}
dt
t
2
.
This is the form of the signed Vasyunin reciprocity that is most useful here. Bettin–Conrey [4] expresses the
same hidden symmetry through an analytic period function.
Define the finite Dirichlet polynomial
Γx(z) = ∑
d|P
γdd
z
. (32)
Theorem 7.4 (Complete signed cancellation). The three moments of the grid coefficients are
Γx(0) = 0, Γ
′
x
(0) = Hx, Γx(1) = Bx. (33)
Insertion of (31) into (30) cancels the entire HxBx term and the universal constant term. Precisely,
Var(Wx) = ∑
d,e|P
γdγe eA(d/e)−H
2
x
. (34)
Proof. From (20),
Γx(z) = ∑
q|P
αq∏
p|q
(p
z −1). (35)
At z = 0, every nonconstant product vanishes. Its first derivative also vanishes unless q is prime, so
Γ
′
x
(0) = ∑
p≤x
αp log p = Hx.
At z = 1, the product is ϕ(q), proving (33).
14For d = ga,e = gb, multiplication of (31) by e gives
−
πg
2
{V (a,b) +V (b,a)} = eA(d/e)−
e−d
2
log(d/e)
−
d +e
2
{log(2π)−γ}. (36)
The last term in its quadratic sum vanishes because it contains Γx(0)Γx(1). Expanding the logarithmic term
and again using Γx(0) = 0 shows that
1
2 ∑
d,e
γdγe(e−d){logd −loge} = Γx(1)Γ
′
x
(0)
= BxHx.
Thus the logarithmic main term cancels the affine HxBx in (30), proving (34).
The cancellation can be diagonalized exactly. Put
Rx(t) = ∑
d|P
γd d{t/d}, χ(t) = 1[1,∞)(t).
Since ∑dγd = 0, Rx(t) = Wx(k) whenever k ≤ t < k +1.
Theorem 7.5 (Critical-line Mellin identity). One has
Var(Wx) = 1
2π
Z
R

Hx +ζ (
1
2 −it)Γx(
1
2 +it)


2
t
2 +
1
4
dt. (37)
Consequently the RH-level estimate for this explicit trial is equivalent to the bound
Z
R

Hx +ζ (
1
2 −it)Γx(
1
2 +it)


2
t
2 +
1
4
dt ≪ x
2
logx. (38)
Proof. First,
Z ∞
0
d{t/d}e{t/e}
dt
t
2
= eA(d/e),
while
Z ∞
0
Rx(t)χ(t)
dt
t
2
= ∑
k≥1
Wx(k)
k(k +1)
= EWx = Hx
and R ∞
1
t
−2 dt = 1. Thus (34) is
Var(Wx) = Z ∞
0
|Rx(t)−Hxχ(t)|
2
dt
t
2
.
This also follows directly because the integrand is |Wx(k)−Hx|
2
t
−2 on [k,k +1).
For −1 < ℜs < 0, the classical fractional-part Mellin transform is
Z ∞
0
{t}t
s−1
dt =
ζ (−s)
s
.
Therefore
Z ∞
0
Rx(t)t
s−1
dt =
ζ (−s)
s
Γx(s+1),
Z ∞
0
Hxχ(t)t
s−1
dt = −
Hx
s
.
Mellin–Plancherel on the line ℜs = −1/2 proves (37). The equivalence with (38) is immediate.
15The Mellin identity is an exact advancement of the signed calculation, but not a proof of the required
estimate: it returns the cotangent problem to a structured Nyman–Beurling approximation problem on the
critical line. The useful new point is that Γx has an explicit truncated Euler-product factorization.
Proposition 7.6 (Head-weighted Euler-product factorization). Write vx = (v0,(vp)p≤x)
T
, and put
F
♯
x
(z) = v0 + ∑
p≤x
(log p+vp)(p
z −1), (39)
Px(z) = ∏
p≤x
(1− p
z−1
), (40)
Hx(z) = ∑
e|P
e≤x
Gx(e)e
z−1
∏p|e
(1− p
z−1)
. (41)
For every ℜz < 1,
Γx(z) = F
♯
x
(z)−Px(z)Hx(z). (42)
Hence the numerator in (37) is exactly
Hx +ζ (1−z)F
♯
x
(z)−ζ (1−z)Px(z)Hx(z), z =
1
2 +it. (43)
Proof. Let γ
F
d
be the grid transform of the global first-chaos function Fx = Sx +v
T
x X. Directly,
γ
F
1 = v0 − ∑
p≤x
(log p+vp), γ
F
p = log p+vp,
and γ
F
d = 0 for ω(d) ≥ 2. Thus its Dirichlet polynomial is F
♯
x (z). Since Φx = Fx −1D≤xGx, divisor Mobius ¨
inversion gives, now for every d | P,
γd = γ
F
d −
1
d ∑
e|d
e≤x
µ(d/e)Gx(e).
Multiplying by d
z
and changing the order of summation yields
Γx(z) = F
♯
x
(z)− ∑
e≤x
Gx(e)e
z−1 ∏
p≤x
p∤e
(1− p
z−1
)
= F
♯
x
(z)−Px(z)Hx(z).
No denominator in (41) vanishes when ℜz < 1.
On the critical line,
ζ (1−z)Px(z) = ζ (1−z)∏
p≤x

1− p
−(1−z)

is a finite, well-defined truncated inverse-Euler factor. No convergent Euler product on ℜ(1 − z) = 1/2 is
being asserted. The remaining analytic task is to bound the combined expression (43); estimating its three
summands separately would destroy precisely the cancellation exposed by theorem 7.4.
167.4 The moderate Mellin block after the normal equation
We now execute the proposed first dyadic step, 1 ≤ |t| ≤ 4, with the normal equation inserted before any
inequality. The result is an exact finite-dimensional reduction, followed by a rigorous obstruction to the
suggested Cauchy–Schwarz closure.
Put ax = ϕ(P)/P, and define
mx =

0,

(p−1)log p

p≤x
T
, x1 = X(1) = (1,(−1)p≤x)
T
,
mfr
x = mx +axHxx1.
For ℜz < 1, introduce the Boolean Mellin kernel
Kx,z(D) = ∏
p≤x

1+
p
z −1
p−1
Xp(D)

(44)
and the signal representer
Ux(D) = ∑
p≤x
log p
p−1
Xp(D).
Finally put
ηx,z(D) = Ux(D) +ζ (1−z)Kx,z(D), bx,z = E[1D>xX(D)ηx,z(D)]. (45)
Theorem 7.7 (Exact normal-equation formula for a Mellin block). Let
Nx(z) = Hx +ζ (1−z)Γx(z).
Then, for every ℜz < 1,
Nx(z) = −axHxηx,z(1) + (mfr
x
)
TM−1
x bx,z
. (46)
Moreover the exact energy of the constructed derivative is
E|Φx|
2 = axH2
x + (mfrx
)
TM−1
x mfrx
. (47)
Thus (46), rather than a separate estimate for the two Euler terms in (43), is the canonical combined scalar
certificate on every t-block.
Proof. Expanding (44) in the orthogonal Ramanujan basis gives
Kx,z(D) = ∑
q|P
∏p|q
(p
z −1)
ϕ(q)
cq(D).
Consequently
E[ΦxKx,z] = Γx(z).
The prescribed prime moments also give
E[ΦxUx] = ∑
p≤x
log p
p−1
E[ΦxXp] = Hx.
It follows that Nx(z) = E[Φxηx,z].
On the head, Φx = −Hx at D = 1 and is zero at every other head atom. On D > x, write
Φx(D) = w
T
x X(D), wx = (v0,(log p+vp)p≤x)
T
.
17The global prescribed moment is mx, whereas the head contributes −axHxx1. Therefore
Mxwx = E[1D>xXΦx] = mfr
x
.
Splitting E[Φxηx,z] into its head and free parts proves (46). The same disjoint split gives
E|Φx|
2 = axH2
x +w
T
x Mxwx,
which proves (47).
For a compact interval I ⊂ (0,∞), define its two-sided Mellin block and the associated direction-free
Riesz factor by
Bx(I) = 1
π
Z
I
|Nx(
1
2 +it)|
2
t
2 +1/4
dt, (48)
Rx(I) = 1
π
Z
I
ax|ηx,
1
2+it(1)|
2 +b∗
x,
1
2+itM−1
x bx,
1
2+it
t
2 +1/4
dt. (49)
The factor 1/π accounts for the two conjugate blocks. Cauchy–Schwarz applied only after (46) gives
Bx(I) ≤ E|Φx|
2 Rx(I). (50)
Thus Rx([1,4]) ≪ 1 would prove the desired moderate-block estimate. The following proposition shows
that this sufficient condition is false.
Proposition 7.8 (Inverse-Euler obstruction to direction-free Cauchy–Schwarz). Let I ⊂ (0,∞) be a compact
interval with nonempty interior. There are cI > 0 and a sequence xj → ∞ for which
Rx j(I) ≥ expcI
√xj
logxj

.
In particular, the exact normal equation and the optimal head energy do not close the block 1 ≤ |t| ≤ 4
through (50). Any proof for the present trial must retain the signed scalar cancellation between the two
terms of (46).
Proof. Choose t0 in the interior of I for which ζ (
1
2 −it0) ̸= 0; this is possible because the zeros are discrete.
At D = 1,
ηx,z(1) = − ∑
p≤x
log p
p−1
+
ζ (1−z)
ax
Px(z), Px(z) = ∏
p≤x
(1− p
z−1
). (51)
For fixed t0 ̸= 0, the prime number theorem and partial summation give
∑
p≤x
p
−1/2+it0 =
x
1/2+it0
(
1
2 +it0)logx
+Ot0
 √
x
(logx)
2

.
Also ∑p p
−1+2it0 converges conditionally, while all higher terms in the logarithm of the Euler factors con-verge absolutely. Hence
log|Px(
1
2 +it0)| = −
√
x
logx
ℜ

x
it0
1
2 +it0
!
+Ot0
 √
x
(logx)
2

. (52)
18Choose xj so that the real part in (52) is bounded above by a fixed negative constant. Then
|Px j(
1
2 +it0)| ≥ exp
c
√xj
logxj

.
Furthermore,

∂t
logPx(
1
2 +it)

 ≤ ∑
p≤x
(log p)p
−1/2
1− p
−1/2 ≪
√
x.
The same exponential lower bound, with a smaller c, therefore holds throughout |t −t0| ≤ x
−1
j
. On this
interval zeta is bounded away from zero. Mertens’ theorem gives a
−1
x ≍ logx, and the first term of (51) is
only O(logx). Thus the first, nonnegative term in (49), integrated over this interval, already has the asserted
lower bound after absorbing its polynomial factors into the exponential.
Remark 7.9 (What the computation says). The exact formula (46) can be evaluated without enumerating
the Boolean cube: Mx is the diagonal full Haar Gram matrix minus the sum over the O(x) squarefree head
atoms. The double-precision stress test in section 9 shows rapid growth of the normalized block for the
present minimum-Haar-energy completion. This does not prove divergence, because the two terms in (46)
can still cancel on untested scales. It does falsify the earlier small-x suggestion that the block is numerically
stable.
There is a canonical way to retain the exact head and prime moments while changing the spectral be-havior. Let
Nx = {r : r = 0 on D ≤ x, E[1D>xr(D)X(D)] = 0}.
Proposition 7.10 (Spectrally regularized free-tail correction). For every r ∈ Nx, the derivative Φex = Φx +r
has the same exact head, mean, and prime moments as Φx, and
E|Φex|
2 = E|Φx|2 +E[1D>x|r|2
].
On a block I, its numerator is
Nex(z) = Nx(z) +ζ (1−z)E[rKx,z].
If Tx,I: Nx → L
2
(I, dt/{π(t
2 +1/4)}) denotes the second term, then for every λ > 0 the unique minimizer
of
∥Nx +Tx,Ir∥
2
2 +λ∥r∥
2
2
satisfies the finite normal equation
(T
∗
x,ITx,I +λI)r = −T
∗
x,INx.
Proof. The defining moment condition for Nx preserves all constant and prime moments. On the free event,
Φx = w
T
x X, so it is orthogonal to r; the energy identity follows by Pythagoras. The numerator formula
follows from Γx(z) = E[ΦxKx,z]. The final assertion is the Euler equation for a strictly convex quadratic
functional on the finite divisor cube.
7.5 The constrained infimum and projected-pair reduction
The infimum proposed after theorem 7.10 can be solved exactly at each finite x. Complex L
2
spaces in the
next statement are regarded as real Hilbert spaces, because the correction r is real.
19Theorem 7.11 (Exact trust-region formula). Let T : H → Y be a linear map between finite-dimensional
real Hilbert spaces, let N ∈ Y , and put
S = T
∗T, g = T∗N, E > 0.
If the minimum-norm least-squares solution of Sr = −g has squared norm at most E, it solves
inf
∥r∥
2≤E
∥N +Tr∥
2
.
Otherwise there is a unique λ > 0 such that
rλ = −(S+λI)
−1
g, ∥rλ ∥
2 = E, (53)
and rλ is the unique minimizer. In the active case the minimum has the exact dual form
∥N∥
2 −


g,(S+λI)
−1
g

−λE. (54)
More explicitly, if T vν = σν uν is a singular system and aν = ⟨N,uν ⟩, then
∥rλ ∥
2 = ∑ν
σ
2
ν a
2
ν
(σ2
ν +λ)
2
, (55)
∥N +Trλ ∥
2 = ∥N⊥∥2 +∑ν
λ
2a2
ν
(σ2
ν +λ)
2
, (56)
where N⊥ ⊥ ranT .
Proof. For λ ≥ 0, the Lagrangian is
L (r,λ) = ∥N +Tr∥
2 +λ(∥r∥2 −E).
Its stationary equation is (S +λI)r = −g. When the unconstrained least-squares solution is infeasible, the
function
λ 7−→

(S+λI)
−1
g


2
is continuous and strictly decreasing from a value larger than E to zero, after deleting the nullspace of S. This
proves existence and uniqueness of the multiplier and the Karush–Kuhn–Tucker conditions are sufficient
because the objective and constraint are convex. Substitution in the Lagrangian gives (54). Expanding in a
singular system gives (55)–(56).
This theorem is not an asymptotic estimate: it identifies exactly which signal-direction singular values
must be controlled. It also avoids the irrelevant global operator norm that failed in theorem 7.8.
There is a polynomial-dimensional test space with completely explicit entries. Write B = {D > x}, let
cq(D) = ∏
p|q
Xp(D), ω(q) = 2,
and put
uq = E[1BXcq], ψq = 1B{cq −u
T
q M−1x X}.
20Proposition 7.12 (Projected-pair infimum). Every ψq belongs to Nx. Its energy Gram matrix and spectral
column are
Gqr = E[1Bcqcr]−u
T
q M−1x ur
, (57)
Lq(z) = ζ (1−z)

E[1BcqKx,z]−u
T
q M−1x E[1BXKx,z
]

. (58)
Consequently, for
Aqr = Re
Lq,Lr

, dq = Re
Nx,Lq

, ν = ∥Nx∥
2
,
the projected-pair infimum is exactly
inf
c
T Gc≤E
{ν +2d
T
c+c
TAc}. (59)
Modulo the nullspace of G, its minimizer satisfies
(A+λG)c = −d, λ ≥ 0, λ(c
TGc−E) = 0. (60)
All entries in (57) and (58) are computable from the O(x) squarefree head atoms and the
π(x)
2

pair labels.
Proof. Directly,
E[1BXψq] = uq −MxM−1
x uq = 0,
and ψq = 0 off B, proving membership in Nx. Expanding E[ψqψr] and using the same identity gives (57).
Expanding E[ψqKx,z] gives (58). The remaining assertions follow by substitution and theorem 7.11.
Remark 7.13 (Why this evades the fixed-degree obstruction). The seed cq has Boolean degree two, but
multiplication by 1B and exact projection off the restricted first chaos introduce all global Boolean degrees.
Thus theorem 2.2, which excludes a globally fixed-degree approximation, does not exclude the functions
ψq.
Conjecture 7.14 (Projected-pair block estimate). There are absolute constants C0,C1 such that, for every
sufficiently large prime cutoff x,
inf
c
T G
(2)
x c≤C0x
2
logx



Nx +L
(2)
x c



2
[1,4]
≤ C1x
2
logx. (61)
Theorem 7.14 is stronger than the original free-tail infimum because it restricts the correction to pro-jected pair seeds. It is now the most concrete open theorem in this route. The finite tests in section 9 support
it, but do not control either the quadrature limit or x → ∞.
Theorem 7.15 (Exact head-Schur compression of all pair columns). Index the squarefree head atoms D ≤ x
by rows. Let P = diag(P(D)), let X be the head matrix with columns 1,Xp, and let C be the head matrix with
columns cpq = XpXq. Put
D1 = diag(1,(p−1)p≤x), D2 = diag((p−1)(q−1)p<q≤x).
Then
Mx = D1 −X
TPX, (62)
G
(2)
x = D2 −C
TQC, (63)
Q = P+PXM−1
x X
TP, Q−1 = P−1 −XD−1
1 X
T
. (64)
21For all sufficiently large x, the matrix
Sx = Q
−1 −CD−1
2 C
T
(65)
is positive definite, and Woodbury gives
(G
(2)
x )
−1 = D−1
2 +D
−1
2 C
T S−1
x CD−1
2
. (66)
Consequently the signal-direction kernel of all
π(x)
2

projected pair columns can be evaluated using only
the O(x)-dimensional matrix Sx.
Proof. Since a degree-two character is orthogonal on the full cube to first chaos,
u = −X
TPC.
Substitution in (57) gives (63); the matrix inversion lemma gives (64). The two Schur complements
D2 −C
TQC, Q−1 −CD−1
2 C
T
are positive definite simultaneously. It remains only to verify injectivity on the free event.
Use Bernoulli rather than centered coordinates; this preserves polynomial degree. A multilinear poly-nomial
a+∑
i
biIi + ∑
i<j
ci jIiIj
in at least four variables which vanishes on every set of Hamming weight at least two is zero. Indeed, the
pair equations give ci j = −a−bi −bj. The triple equations imply that all bi = b and 3b = −2a; a quadruple
equation then gives a/3 = 0.
Choose four primes larger than √x. After fixing arbitrarily all other prime coordinates, every state
containing at least two of these four primes lies in D > x. Applying the preceding lemma for every fixed
assignment first kills the high-prime coefficients, then all cross coefficients, and finally the polynomial in
the remaining coordinates. Thus no nonzero degree-at-most-two polynomial vanishes on the free event. In
particular the projected pair Gram matrix is positive definite. Equation (66) is now the Woodbury identity.
The compression has a closed form which does not even require forming C. Let Y = (Xp(D))D,p,
dp = (p−1)
−1
, and
H2 = CD−1
2 C
T =
1
2
n
Ydiag(dp)Y
T
◦2 −Y
◦2
diag(d
2
p
)(Y
◦2
)
T
o
. (67)
Here ◦2is entrywise squaring. The identity is simply ∑p<q ypyq = {(∑p yp)
2 −∑p y2
p}/2.
For az(p) = p
z −1, set
s(z,w) = ∑
p≤x
dpaz(p)aw(p), s2(z,w) = ∑
p≤x
d
2
paz(p)
2
aw(p)
2
,
Tz = Y(dpaz(p))p, Uz = Y
◦2
(d
2
paz(p)
2
)p,
Jz = T
◦2
z −Uz
.
Writing kz = E[1BXKx,z], define the head vector
ρz = P

XM−1
x
kz −(Kx,z(D))D≤x

, Rz = ζ (1−z)

1
2
Jz +H2ρz

.
22Corollary 7.16 (Closed pair kernels and a diagonal sufficient target). The bilinear kernel associated with
the diagonal pair energy is
Bx(z,w) = ζ (1−z)ζ (1−w)
2

s(z,w)
2 −s2(z,w) +ρT
z
Jw +J
T
z ρw +2ρ
T
z H2ρw

. (68)
The exact projected-pair kernel is
K
(2)
x (z,w) = Bx(z,w) +R
T
z S
−1
x Rw. (69)
Moreover
0 < G
(2)
x ≤ D2. (70)
Hence the stronger diagonal-energy estimate
inf
∑p<q
(p−1)(q−1)c
2
pq≤C0x
2
logx





Nx + ∑
p<q
cpqLpq





2
[1,4]
≪ x
2
logx (71)
would prove theorem 7.14.
Proof. The pair-sum identity applied to the columns (58) gives (68). Substitution of (66) gives (69). Equa-tion (70) follows directly from (63); it shows that every vector feasible for the diagonal constraint is feasible
for the true energy constraint.
There is also an exact explanation of the resonance being removed. Let
V(D) = ∑
p≤x
(log p)Xp(D), h(D) = −Hx1{D=1}, g = (V −h)|D≤x.
The normal equation gives
Nx(z) = Hx +ζ (1−z)
(
∑
p≤x
(log p)az(p) +ρ
T
z g
)
, (72)
∑
p<q
cpqLpq(z) = ζ (1−z)
(
∑
p<q
cpqaz(p)az(q) +ρ
T
z Cc
)
. (73)
Thus Cc = −g would cancel the inverse-Euler term identically, leaving an ordinary quadratic Dirichlet poly-nomial. This tempting block-independent shortcut is generally impossible: −g has a nonzero component
outside ranC, exactly as required by the fixed-degree separator in theorem 2.2. The successful minimizer
must therefore be adapted to the spectral block; Euclidean least-squares interpolation of g is not enough.
Thus the strongest surviving version of the critical-line program is no longer the minimum-Haar-energy
completion by itself. It is the constrained projected-pair correction problem, now reduced further to the
explicit diagonal kernel (68): spend part of the available O(x
2
logx) energy budget precisely where the
inverse-Euler resonances occur.
7.6 Termwise match to Bettin–Chandee
With exp(2πi(z)) = exp(2πiz), the finite Fourier identity
cot(πu/n) = i
n−1
∑
h=1

1−
2h
n

exp(2πi(−hu/n))
23gives the exact coprime expansion
V (m,n) = i
n−1
∑
h=1
n−1
∑
k=1
k
n

1−
2h
n

exp(2πi(−hkm/n)). (74)
For rectangular dyadic ranges h ≍ H, k ≍ K, put
ν
(0)
a (H,K) = ∑
hk=a
h≍H, k≍K
k,
ν
(1)
a (H,K) = ∑
hk=a
h≍H, k≍K
hk.
The corresponding part of the first Vasyunin term in (30) is
i ∑
m≍M, n≍N
(m,n)=(m,g)=(n,g)=1
γgm
γgn
n ∑a
ν
(0)
a exp(2πi(−am/n))
−2i ∑
m≍M, n≍N
(m,n)=(m,g)=(n,g)=1
γgm
γgn
n
2 ∑a
ν
(1)
a exp(2πi(−am/n)). (75)
The interior ranges on which h,k < n throughout are already rectangular. For the negative comparison below
this is enough: even granting a lossless separation of the remaining boundary ranges cannot repair the power
loss. A complete smooth dyadic decomposition of those boundary ranges can also be separated by Mellin
inversion or repeated Abel summation at logarithmic cost, but no such auxiliary lemma is needed for the
conclusion below. The divisor bound gives



ν
(0)



2
≪ε H
1/2K3/2
(HK)
ε
,



ν
(1)



2
≪ε (HK)
3/2+ε
. (76)
The applicable published theorem is [3, Theorem 1]. For
B = ∑
a≍A, m≍M, n≍N
(m,n)=1
νaαmβn exp(2πi(ϑam/n)),
it states
B ≪ε ∥α∥2
∥β∥2∥ν∥2

1+
|ϑ|A
MN 1/2
×
n
(AMN)
7/20+ε
(M +N)
1/4 + (AMN)3/8+ε
(AM +AN)
1/8
o
. (77)
The conditions involving g in (75) are absorbed into the arbitrary coefficient sequences. Thus every coprime
rectangular box has now been matched term by term to the theorem.
The recent partially fixed-modulus theorem of Wright [6] does not improve this match as it stands. Its
phase is exp(2πi(ϑam/(nR))), with a fixed divisor R in the modulus. In (75), however, the common factor
g occurs in γgm, γgn, and the outer scalar g; after the mandatory gcd reduction the phase modulus is n, not
gn. Thus setting R = g would change the sum rather than specialize Wright’s theorem to it.
24Proposition 7.17 (The direct match is quantitatively lossy). Let
Ag(L) =

 ∑
m≍L
(m,g)=1
|γgm|
2


1/2
.
In a balanced Fourier box M ≍ N ≍ H ≍ K ≍ L, (77) bounds (75), apart from the outer factor g, by
≪ε L
23/8+εAg(L)2
. (78)
The elementary estimate V (m,n) ≪ nlog(2n) instead gives
≪ L
2
log(2L)Ag(L)
2
. (79)
Consequently the exact finite-Fourier match to Bettin–Chandee is worse by a factor of order L7/8−o(1)in
these boxes.
Proof. Here A ≍ HK ≍ L
2
. The bracket in (77) is Oε (L
15/8+ε
). For the first line of (75),
∥γgm∥2∥γgn/n∥2



ν
(0)



2
≪ Ag(L)
2L−1L2 = LAg(L)2
.
The second line gives the same factor:
Ag(L)
2L−2L3 = LAg(L)2
.
This proves (78). For the elementary bound, apply Cauchy–Schwarz separately in m and n: ∑m≍L|γgm| ≤
L
1/2Ag(L), and similarly for n.
7.7 The residual Estermann-compressed obligation
The loss in theorem 7.17 comes from expanding a cotangent sum of modulus n into two variables with prod-uct A ≍ n
2
. A smooth Estermann approximate functional equation should instead be used before absolute
values. To make the needed gain falsifiable, define
B(A,M,N) = 1+
A
MN 1/2
×
n
(AMN)
7/20+ε
(M +N)
1/4 + (AMN)3/8+ε
(AM +AN)
1/8
o
. (80)
If a signed Estermann transformation compresses the phase length to A ≪ N
1+ε with transformed coefficient
norm ≪ NA−1/2+ε, then a sufficient absolute-value box obligation would be
∑
G,M,N,A
NA−1/2+εB(A,M,N) ∑
g≍G
gAg(M)Ag(N) ≪ x
2
logx, (81)
together with the reciprocal term and the main, dual, and error terms of the approximate functional equation.
This is a precise next lemma, not a theorem proved here.
Even (81) cannot follow from the generic norm (28). In the balanced case A = M = N = L, its weight is
L
15/8+ε
, whereas
∑
g≍G
gAg(L)
2 ≪ε
x
3
(logx)
2
L
(GL)
ε
. (82)
25Indeed d = gm ≍ GL, each d has at most τ(d) ≪ε d
ε
such factorizations, and (28) applies. The resulting
bound is only x
3
(logx)
2L7/8+ε
, far above the target. This does not show that the signed quadratic form is
large. It proves that a generic coefficient-norm argument, even after the anticipated compression, cannot
close the estimate.
The viable version of this route must therefore preserve cancellation between HxBx − H
2
x
, the two re-ciprocal Vasyunin sums, and the main/dual terms of the Estermann transformation. Equivalently, it needs a
new signed box estimate that uses the explicit head transform (25), rather than only ℓ
2 norms.
The attempted last step and its exact failure
Since Ex(x) = 0 and ∆Wx = −Φx,
Ex(r) = −
r
∑
n=x+1
Φx((n,P)).
The discrete Hardy inequality gives
P
∑
r=x+1
|Ex(r)|
2
r
2
≤ 4
P
∑
n=x+1
|Φx((n,P))|
2
.
This is rigorous but useless at the target scale: Haar averaging supplies only
P
∑
n=1
|Φx((n,P))|
2 = PE|Φx|2 ≪ Px2
logx.
The missing factor P cannot be discarded. Doing so would silently replace the fixed arithmetic origin by
a random translate. Thus the proved Haar derivative theorem is not a proof of (19). The exact Fourier
argument in theorem 6.2 does control the translation-invariant term, but it does not control the singular
weight near the fixed origin.
8 Literature boundary after the new reduction
• Baez-Duarte–Balazard–Landreau–Saias [1] gives the exact rational fractional-part autocorrelation and ´
hence the Vasyunin kernel. It identifies the Green quadratic form but does not prove (19).
• Maier–Rassias [2] proves a fixed power saving for one Mobius-weighted Wilton/cotangent sum. The ¨
coefficient vector generated by M−1
x hx is a thresholded first-chaos Boolean transform, and (19) is a
quadratic fixed-origin partial-sum estimate. The published theorem does not contain this form.
• Bettin–Chandee [3] proves the trilinear Kloosterman-fraction estimate recorded in (77). Section 7
verifies the coefficient, coprimality, and range match. The direct finite-Fourier match is nevertheless
quantitatively worse than the elementary cotangent bound in balanced boxes.
• Bettin–Conrey [4] develops the reciprocity and period-function structure behind cotangent sums. That
signed reciprocity, combined with an Estermann approximate functional equation, is now more relevant
than expanding every cotangent term before cancellation.
• The very recent preprint of Pyvovarov [5] independently develops gcd layers, symmetric primitive-pair
recombination, and exact edge cancellations for exponentially damped Mobius approximants. Its final ¨
obstruction is again a global bilinear cancellation. Its coefficients and canonical third-order truncation
differ from γd, so none of its unresolved estimates may be imported here.
26• Wright [6] improves Bettin–Chandee when the phase modulus has a fixed factor. The theorem is struc-turally close but not directly applicable here: the stripped common divisor g occurs in the coefficient
indices, whereas the reciprocal phase has modulus n.
• Dong–Robles–Zeindler [7] is a withdrawn preprint and is not an admissible input. The authors’ with-drawal note reports a missing factor L
2
, changing L
5
to L
7
; the remaining argument does not yield the
claimed improvement.
• Heath–Brown [8] proves strong mean bounds for large gaps between X
ε
-smooth numbers, including
∑(an+1 − an)
2 ≪ε X7/6+ε
. This can help with polynomial-size occurrence shells. It neither enforces
squarefreeness automatically nor controls repeated returns to one gcd atom, and it does not prove the
fixed-origin Green estimate over a primorial period.
• Gorodetsky [9] proves an unconditional asymptotic for the variance of integers without small prime
factors in certain short interval regimes. This is relevant to a shift-averaged rough-number model, but
its averaging over the interval origin does not control the single primorial origin in (19).
No cited theorem may therefore be substituted for (19).
9 Finite diagnostics
The script free extension diagnostic.py exactly enumerates the finite divisor cube in floating-point
arithmetic. It reports the free-event probability, the least generalized eigenvalue of Mx relative to Dx, and
the signal extension-energy ratio
h
T
x M−1x hx
E[1D≤x|gx(D)|
2
]
.
x π(x) P(D > x) least frame eigenvalue energy ratio
5 3 0.266667 0.014424 3.92077
7 4 0.219048 0.018651 4.02159
11 5 0.217316 0.024407 2.63254
13 6 0.261538 0.036052 2.10518
17 7 0.241041 0.031561 1.79265
19 8 0.271485 0.040268 1.55625
23 9 0.265733 0.039083 1.40433
29 10 0.272249 0.041175 1.28958
31 11 0.271523 0.044572 1.52155
37 12 0.264153 0.041773 1.43618
These values are consistent with theorem 4.1, which is already proved and does not depend on the com-putation. They say nothing decisive about theorem 6.3. Separately, extending the earlier dyadic diagnostic
to the first eight primes (x = 19) gives normalized residuals
V19,8
192log19
= 0.04108,
Rpaired
192log19
= 0.06128.
The paired Gram range is severely conditioned. These are double-precision falsification checks, not asymp-totic evidence.
An independent full divisor-cube reconstruction at x = 13 gives maximum mean and prime-moment
errors 1.97 · 10−15 and 1.07 · 10−14, respectively. The direct Ramanujan transform and (13) agree to 2.67 ·
2710−15; the maximum head error is 2.49 · 10−14; and the energy 348.162817387 agrees with its Parseval sum
to 1.71 · 10−13. These checks validate the finite implementation and all displayed signs at that test point, not
the open asymptotic. Direct period enumeration also agrees with (16) to 2.78·10−14, and the normalized sum
of the two Green terms is 0.22141764. The upper and lower Mobius constructions of ¨ γd agree to 7.11·10−15,
while the explicit head formula (25) agrees to 8.88 · 10−16. Finally, direct Pareto residue weighting and the
gcd-split covariance (30) agree with relative error 3.75·10−11; the larger cancellation error is expected from
double-precision cotangents. The three moment identities (33) agree to 1.15 · 10−15, and the head-weighted
Euler factorization (42) agrees at four real and complex test points to 4.15 · 10−14. The direct variance is
94.56466484. Numerical quadrature of (37) over the positive-frequency windows
[0,1], [1,4], [4,16], [16,64], [64,128]
(including the factor 1/π for the two symmetric halves) gives, respectively,
5.14455, 53.24384, 10.90052, 17.09208, 3.44434.
Their sum 89.82532 captures 94.99% of the direct variance; the unintegrated tail is positive. This is a finite
sign and normalization check, not evidence for an asymptotic bound, but it shows that the moderate Mellin
range 1 ≤ |t| ≤ 4 is already the dominant block at x = 13.
The head-only implementation of (46) permits a substantially larger stress test. The following table
gives
Bx([1,4])
x
2
logx
,
E|Φx|
2
x
2
logx
,
using 241 equally spaced positive-frequency nodes. Here x is the displayed prime cutoff.
x π(x) head atoms Bx([1,4])/(x
2
logx) energy ratio peak t
53 16 33 2.74608 0.85556 1.0000
97 25 61 9.64847 0.86790 1.0000
199 46 122 9.94202 1.02118 1.0000
499 95 306 37.79246 1.01813 1.7125
997 168 607 423.88700 1.02939 1.5375
1499 239 915 2546.59150 1.06065 1.4500
1999 303 1215 9864.38840 1.04581 1.4000
2999 430 1824 91492.72000 1.06008 1.3250
The derivative energy remains at the proved optimal scale, while this moderate spectral block grows
rapidly in the tested range. These values are not a proof of asymptotic divergence, but they are a direct
falsification test against treating the x = 13 block as stable. Together with theorem 7.8, they rule out the pro-posed direction-free Cauchy–Schwarz closure and strongly disfavor the minimum-Haar-energy completion
as the final trial.
9.1 Numerical solution of the correction infimum
We next solved (59) with the additional energy budget
E = 0.1x
2
logx.
The optimization used 80-point Gauss–Legendre quadrature on [1,4]. Every displayed objective was then
recomputed on a separate uniform grid of 1201 points. The table records the uncorrected and corrected
block integrals, both divided by x
2
logx.
28x π(x) pair columns uncorrected projected-pair residual added energy
13 6 15 0.12284 1.03 · 10−5 0.100
19 8 28 0.26652 2.19 · 10−4 0.100
29 10 45 0.54840 3.25 · 10−4 0.100
37 12 66 1.23718 0.00513 0.100
43 14 91 2.08128 0.01310 0.100
53 16 120 2.74605 0.01214 0.100
97 25 300 9.64113 0.19881 0.100
199 46 1035 9.90497 0.28871 0.100
This is the first successful attempt in the note at the proposed infimum: the projected-pair residual has
the desired O(x
2
logx) size in every tested case, even where the uncorrected block is almost ten times that
scale. It is still only a finite floating-point calculation. In particular, it gives no uniform lower bound on the
signal-direction singular values and cannot exclude eventual deterioration.
The optimal pair coefficient matrix is highly compressible. At x = 199, the first one, two, three, and
four matrix singular directions account for 75.15%, 89.27%, 97.52%, and 99.46% of its Frobenius energy.
A six-feature symmetric regression using
1, log p+logq, log plogq, p
−1 +q−1
, (pq)
−1/2
, (log p+logq)
2
has R
2 = 0.97287. Restricting the optimization itself to these six features gives:
x uncorrected six-feature residual added energy
53 2.74605 0.26934 0.100
97 9.64113 1.73041 0.100
199 9.90497 1.66111 0.100
499 37.78537 3.78374 0.100
The six-dimensional model does not reproduce the near-annihilation of the full pair space, but it contin-ues to remove most of the resonance through x = 499. This suggests that the next proof should seek a short
separable or dyadically separable coefficient formula rather than attempt a direction-free estimate for the
entire pair operator. The accompanying script spectral correction infimum.py constructs (57)–(58),
solves (60) by the singular-value trust-region formula, and performs the independent-grid validation.
9.2 Compressed full-pair kernel through cutoff 2999
Theorems 7.15 and 7.16 remove the
π(x)
2

-dimensional Gram solve. We optimized with 80 Gauss–Legendre
nodes and validated on a distinct uniform grid of 801 points. The next table compares the exact projected-pair kernel at energy 0.2x
2
logx with the stronger diagonal constraint at energy x
2
logx. Every entry is
divided by x
2
logx.
x uncorrected exact pair, E = 0.2 diagonal pair, E = 1 diagonal interpolation energy
199 9.90690 5.90 · 10−4 1.64 · 10−8 1.21157
499 37.78574 0.00348 1.15 · 10−6 1.08892
997 423.88579 0.02428 2.70 · 10−6 1.11876
1999 9864.38832 0.14109 4.45 · 10−4 1.15575
2999 91492.71881 0.55329 0.01175 1.20672
29Thus the exact pair correction remains at the RH scale through x = 2999 with only 0.2x
2
logx additional
energy. More significantly, the diagonal majorant—which is a rigorously smaller feasible set—leaves less
than 0.012x
2
logx at the largest cutoff with budget x
2
logx. The final column is the truncated pseudoinverse
energy on the optimization grid; its stability near 1.2x
2
logx motivated (71).
These are still finite floating-point calculations. The dense grid and independent quadrature make simple
node overfitting unlikely, but they do not prove a continuous uniform inequality. The block-independent
shortcut suggested by (72) also fails sharply. At x = 2999, the diagonal-energy least-squares solution of
Cc ≈ −g uses only 0.3092x
2
logx and leaves just 7.63% of g in Euclidean norm, yet its normalized spectral
residual is 81417.2. The small Euclidean remainder is almost aligned with the inverse-Euler resonance.
This is direct numerical confirmation that the required estimate is signal-directional, not an ordinary head
interpolation bound.
The accompanying script projected pair Schur kernel.py evaluates (68) and (69) without forming
the pair Gram matrix, solves the exact trust problem, and performs the separate uniform-grid validation.
10 Viability and specific next steps
Program Score Assessment
Spectrally regularized
moment-null free-tail
correction
4.8/5 Theorem 7.10 preserves the exact head and all prime
moments. The full pair space compresses exactly to an
O(x)-dimensional head Schur kernel. Even its
diagonal-energy subproblem achieves the RH scale on
[1,4] through x = 2999 with budget x
2
logx.
Uniformity in x and the remaining Mellin blocks are
unproved.
Full signal-contracted
CRT/cotangent route
3.9/5 The exact gcd split and signed reciprocity are
complete. They return the problem to the same
Nyman–Beurling critical-line norm, so cotangent
technology alone supplies no independent gain.
Paired smooth dyadic blocks 3.4/5 Rigorous O(x)-column construction and favorable
small cases, but no uniform residual estimate and
severe Gram conditioning.
Smooth-gap/occurrence route 2.8/5 Useful for polynomial shells and reset gaps. Atom
reuse and the primorial fixed origin remain
uncontrolled.
Minimum-Haar-energy
exact-head Euler trial
2.2/5 All algebraic reductions and its O(x
2
logx) derivative
energy are exact. Nevertheless theorem 7.8 rules out
the proposed post-normal-equation Cauchy–Schwarz
proof, and the moderate-block stress test grows
rapidly through x = 2999.
Wright partially fixed-modulus
theorem
1.8/5 Potentially useful after a different reciprocity
arrangement, but the current common factor g lies in
the coefficient indices rather than in the phase
modulus required by the theorem.
30Program Score Assessment
Direct one-shot
Bettin–Chandee invocation
1.0/5 The match has now been executed and is worse than
the elementary bound by L
7/8−o(1)
in balanced
exact-Fourier boxes.
Withdrawn
Dong–Robles–Zeindler
estimate
0/5 The preprint was withdrawn after a missing L
2
factor
was found; it cannot be used.
Globally fixed Boolean degree 0/5 Theorem 2.2 and the general fixed-degree separator
rule it out. The projected-pair correction is not in this
class, because the free-tail indicator introduces all
global degrees.
These scores are comparative research-priority judgments, not probabilities that a route will prove RH.
The recommended immediate work is:
G1. Prove the diagonal pair-kernel estimate. This is now the immediate theorem. Let Bx be the integral
operator with kernel (68). Find a multiplier λx ≥ 0 and prove the two signal-direction bounds


Nx,Bx(Bx +λxI)
−2Nx

≪ x
2
logx,
λ
2
x


Nx,(Bx +λxI)
−2Nx

≪ x
2
logx.
By theorems 7.11 and 7.16, these are exactly the energy and residual obligations and avoid G
(2)
x
altogether.
G2. Prove target RKHS membership. A stronger but cleaner sufficient statement is
Nx ∈ H (Bx), ∥Nx∥
2
H (Bx) ≪ x
2
logx.
The truncated interpolation energies in the table are between 1.08x
2
logx and 1.22x
2
logx. The proof
should use the explicit pair-sum kernel, not a lower bound for its least eigenvalue.
G3. Exploit the ρz-factorization. Split (68) into the ordinary semiprime term and the head-resonance
term. Estimate them only after contraction against (72). The failed Cc ≈ −g experiment proves that
an unweighted head projection destroys the relevant cancellation.
G4. Certify the continuous block. Combine interval arithmetic with analytic t-derivative bounds for
Px(
1
2 +it), Jz
, and ρz. Increasing quadrature and an 801-point independent grid agree, but a rigorous
continuous estimate needs certified control between nodes.
G5. Extend beyond the first block. After [1,4], solve the same projected-pair problem on [2
j
,2
j+1
],
track the energy required per block, and seek a summable allocation. A proof on [1,4] alone is not
RH; the full Mellin–Plancherel integral must still be controlled.
11 Conclusion
The proof attempt does not establish the Riemann hypothesis. It does prove the entire derivative-side esti-mate that had previously been only a heuristic: there is a canonical, finite-normal-equation mixed trial with
31the right prime signal, an exact head through x, and Haar energy O(x
2
logx). The construction is protected
by the unconditional free-divisor frame theorem (4).
For the minimum-Haar-energy trial, the sole formal remaining step is the weighted fixed-origin Green es-timate (19). The uniform-period term has been proved in theorem 6.2, but the surviving singularly weighted
term is not a formal consequence of the Haar bound; Hardy’s inequality exposes an otherwise hidden factor
Px. The new block calculation makes this failure sharper. Even after the normal equation is inserted exactly,
the direction-free Riesz factor is exponentially unbounded along subsequences, and the computed 1 ≤ |t| ≤ 4
mass grows rapidly through x = 2999. This is not a proof that the scalar block diverges asymptotically, but
it removes the previous basis for rating this particular completion as the leading route.
Nor does the completed N1 paired partition automatically remove this obstacle: membership or RH-scale approximation of the exact-head vector by that paired space is unproved. The common-divisor,
termwise Kloosterman, and signed-reciprocity steps have now all been completed. The signed calculation
cancels HxBx exactly, but also shows that the cotangent route is not an independent shortcut: it is precisely
the critical-line Nyman–Beurling norm (37). The most viable next attack is now the projected-pair instance
of the spectrally regularized moment-null correction in theorem 7.12. Its constrained infimum is solved
exactly at finite x, and theorem 7.15 compresses all pair columns to an O(x)-dimensional head kernel. More
importantly, (70) removes the exact Gram matrix from the sufficient target: the stronger diagonal-energy
problem has computed RH-scale [1,4] residual through x = 2999. What remains is not the finite optimiza-tion but a uniform proof of (71), followed by compatible estimates and a summable energy allocation on the
other Mellin blocks.
References
[1] L. Baez-Duarte, M. Balazard, B. Landreau, and E. Saias, ´ Etude de l’autocorr ` elation multiplicative de ´
la fonction partie fractionnaire, Ramanujan J. 9 (2005), 215–240. https://arxiv.org/abs/math/
0306251.
[2] H. Maier and M. Th. Rassias, Explicit estimates of sums related to the Nyman–Beurling criterion for
the Riemann hypothesis, J. Funct. Anal. 276 (2019), 3832–3857. https://arxiv.org/abs/1806.
05070.
[3] S. Bettin and V. Chandee, Trilinear forms with Kloosterman fractions, Adv. Math. 328 (2018), 1234–
1262. https://arxiv.org/abs/1502.00769.
[4] S. Bettin and J. B. Conrey, Period functions and cotangent sums, Algebra & Number Theory 7 (2013),
215–242. https://arxiv.org/abs/1111.0931.
[5] A. Pyvovarov, A few remarks on the Baez-Duarte criterion, preprint (2026), arXiv:2607.12084. ´ https:
//arxiv.org/abs/2607.12084.
[6] T. Wright, Trilinear Kloosterman fractions I: partially fixed moduli and unbalanced convolutions,
preprint (2026), arXiv:2604.25177. https://arxiv.org/abs/2604.25177.
[7] A. Dong, N. Robles, and D. Zeindler, Bilinear forms with Kloosterman fractions and applications,
withdrawn preprint (2026), arXiv:2601.00292; not used as an input. https://arxiv.org/abs/2601.
00292.
[8] D. R. Heath-Brown, The differences between consecutive smooth numbers, Acta Arith. 184 (2018),
267–285. https://arxiv.org/abs/1808.02947.
32[9] O. Gorodetsky, The variance of integers without small prime factors in short intervals, preprint (2024),
arXiv:2111.00853. https://arxiv.org/abs/2111.00853.
33
