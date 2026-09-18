# Explicit legal Pareto approximators with rational error certificates

September 18, 2026. Status: explicit finite witnesses and a written infinite-tail proof, checked by exact Python integer/rational arithmetic. The full error bounds have not been verified in Lean. No convergence-to-zero theorem or proof of RH is claimed.

## Concrete outcome

For positive integers n define g_d(n)=(n mod d)/d and w_n=1/(n(n+1)). All witnesses below belong to the actual legal space V=span_finite{g_d:d>=2}. We measure the full squared Pareto error

    D(F) = sum_{n>=1} w_n (1-F(n))^2.

An explicit short witness is

    F_simple = (57 g_2 +58 g_3 +11 g_4 +43 g_5 -26 g_6 +37 g_7 +5 g_8)/64.

The exact-rational certificate proves D(F_simple)<24251/1000000.

The larger witnesses are F_N=sum_{d=2}^N k_{N,d} g_d/16777216. Every integer coefficient is in LegalApproximators.json, ordered by d=2,...,N. The following strict upper bounds include the entire infinite tail; decimal entries are terminating rational numbers rounded upward, not floating-point estimates of an unknown remainder.

| Maximum modulus N | Certified full squared error upper bound |
|---:|---:|
| 8 | 0.024244528 |
| 16 | 0.017936278 |
| 32 | 0.014077116 |
| 64 | 0.011393576 |
| 128 | 0.009683675 |
| 256 | 0.008446372 |

In particular D(F_256)<8447/1000000, and ||1-F_256||_H<0.092 since 0.092^2=0.008464. These witnesses do not impose exact head interpolation or zero period mean; neither constraint is required for direct legal L2 approximation.

The coefficients were found by weighted least squares on n=1,...,200000 and then rounded to denominator 2^24. This floating-point search has no role in the certification. We do not assert that the rounded candidates are the exact minimizers, even in their finite-dimensional spans.

## Exact signed CRT covariance

Let F=sum_d c_d g_d with finite real coefficients. Over any common period Q, put

    m_d = (d-1)/(2d),
    K_de = (gcd(d,e)^2-1)/(12de).

The period mean squared error is exactly

    M = (1-sum_d c_d m_d)^2 + sum_{d,e} c_d c_e K_de.

Every signed cross term is retained.

Proof of the covariance formula: write d=ga, e=gb with g=gcd(d,e) and gcd(a,b)=1. Conditional on n mod g=r, the two residues are r+g i and r+g j, where i in {0,...,a-1} and j in {0,...,b-1} are independent uniform coordinates by CRT. Thus the conditional covariance of g_d and g_e is zero, and the covariance of their conditional means is Var(r)/(de)=(g^2-1)/(12de). Taking expectations gives m_d and the stated formula. Averaging (1-F)^2 proves the equality for M.

## Exact tail equality and certified remainder

For a periodic h: N -> [0,1] of period p and period mean mu, and an arbitrary cutoff T, set

    Delta_h(K)=sum_{n=T+1}^K (h(n)-mu),
    R_h(T)=sum_{K=T+1}^infinity Delta_h(K)(w_K-w_{K+1}).

All complete periods contribute zero. For a residual block of length k<=p, its centered sum lies between

    -min(k mu,(p-k)(1-mu))
    and min(k(1-mu),(p-k)mu).

Consequently |Delta_h(K)|<=p mu(1-mu)<=p/4. Summation by parts, with its boundary term tending to zero, gives the exact equality

    sum_{n>T} w_n h(n) = mu/(T+1) + R_h(T),
    |R_h(T)| <= p/[4(T+1)(T+2)].

Apply this to g_d (period d) and g_d g_e (period lcm(d,e)). The full error has the exact signed decomposition

    D(F) = sum_{n=1}^T w_n(1-F(n))^2 + M/(T+1)
           -2 sum_d c_d R_{g_d}(T)
           +sum_{d,e} c_d c_e R_{g_d g_e}(T).

Define the explicit rational constant, when the c_d are rational,

    B = [2 sum_d |c_d| d + sum_{d,e}|c_d c_e| lcm(d,e)]/4.

Then the magnitude of the last two terms is at most B/[(T+1)(T+2)]. This bound applies only to the retained tail remainder; it does not replace the signed covariance energy M by entrywise absolute values.

This bypasses the potentially enormous common period lcm(2,...,N): only the pairwise periods, at most N^2, enter the certificate.

## Integer certificate for the finite part

For c_d=k_d/P put L=lcm(2,...,N), D=P L and

    z_n = D - sum_{d=2}^N k_d (L/d)(n mod d).

Then the nth error summand is exactly z_n^2/[D^2 n(n+1)]. Set S=2^48. Integer division computes the floor and ceiling of S times every summand. If their sums are ell and u, then exactly

    ell/S <= sum_{n=1}^T w_n(1-F(n))^2 <= u/S,
    0 <= (u-ell)/S <= T/S.

Hence the computable rational upper certificate is

    U = u/S + M/(T+1) + B/[(T+1)(T+2)].

LegalApproximators.json stores all these quantities as exact rational strings. VerifyLegalApproximators.py recomputes them using only Python integers and Fraction, with no floating-point arithmetic. Run `python3 VerifyLegalApproximators.py` for every witness, or append a modulus to select it. The generator scripts use NumPy solely to find coefficients.

## Consequence for conditional-mean approximation

With C F(t)=t^(-1) sum_{n=1}^t F(n) and q_t=2/((t+1)(t+2)), the exact mixture identity is

    sum_{t>=n} q_t/t = w_n.

Jensen and Tonelli therefore give ||C(1-F)||_J^2<=D(F). Every witness here also has conditional-mean squared error at most its listed certificate.

## What this advances and what remains open

We have found actual finite legal approximators, rather than introducing a new unproved sufficient hypothesis. The coefficients and full infinite-tail certificates are explicit and reproducible. These are finite quantitative results, not a proof of a limiting approximation theorem.

A possible continuation is to optimize the rational certificate itself, or optimize a larger finite signed Gram system and then certify the rounded coefficients. Increasing the certification cutoff T can shrink its remainder without changing a witness. Neither operation proves that the best legal error tends to zero.

The missing mathematical assertion remains: for every epsilon>0 there is a finite legal F with D(F)<epsilon. No extrapolation of the displayed numerical sequence is used to assert it. In particular, strict improvement at finitely many cutoffs does not exclude a positive limiting error.

## Lean status

The resumed Lean endpoint verified the basic availability test `example : (1 : Nat) + 1 = 2 := rfl` in 5.005 seconds. That is an availability check only. The CRT tail argument and these numerical error certificates are not claimed to be kernel-checked. The earlier unverified residual-tail draft remains separate.

## Reproducible data and checker

Save the following two fenced blocks as the indicated filenames in the same directory, then run the checker. They are embedded here so the complete research checkpoint is self-contained.

### LegalApproximators.json

```json
[
  {
    "N": 8,
    "T": 200000,
    "denominator": 16777216,
    "numerators": [
      15040031,
      15106531,
      2881320,
      11301515,
      -6895923,
      9688574,
      1367751
    ],
    "finite_lower": "6824002401109/281474976710656",
    "finite_upper": "6824002601109/281474976710656",
    "signed_period_mean_square": "155311279535149633/972777519512027136",
    "tail_discrepancy_constant": "31412100186554155/562949953421312",
    "certified_tail_upper": "15558423319355681239553/19455842224469173847652827136",
    "certified_total_upper": "471697693361454018481872257/19455842224469173847652827136"
  },
  {
    "N": 16,
    "T": 200000,
    "denominator": 16777216,
    "numerators": [
      15554880,
      15131689,
      2151380,
      12764351,
      -8870780,
      10586916,
      -428112,
      1777883,
      -6965743,
      7385312,
      -896362,
      7254266,
      -5711708,
      -4546324,
      4148298
    ],
    "finite_lower": "5048370222501/281474976710656",
    "finite_upper": "5048370422501/281474976710656",
    "signed_period_mean_square": "309114831628338119125249/1812503393792796760473600",
    "tail_discrepancy_constant": "474081742301259833/1125899906842624",
    "certified_tail_upper": "31293386929922722666855520849/36250611628686576442292938840473600",
    "certified_total_upper": "650201044469118774283743590826449/36250611628686576442292938840473600"
  },
  {
    "N": 32,
    "T": 200000,
    "denominator": 16777216,
    "numerators": [
      15732247,
      15488366,
      1901843,
      13467811,
      -10231597,
      11386694,
      92074,
      1011382,
      -8988931,
      9486320,
      -1776455,
      8860948,
      -5822375,
      -9092687,
      2657937,
      4981131,
      -585376,
      5751041,
      -544736,
      -4162379,
      -5801370,
      5789349,
      1090407,
      -110659,
      -5991277,
      370492,
      -2660947,
      4540393,
      6859580,
      4061038,
      -7732615
    ],
    "finite_lower": "3962018329533/281474976710656",
    "finite_upper": "3962018529533/281474976710656",
    "signed_period_mean_square": "7708082229705573869407664424768189436898041/35216549331386202727101111318449026498560000",
    "tail_discrepancy_constant": "1167807552879746705/281474976710656",
    "certified_tail_upper": "76715513905564775466817805523844552148686490731/64031050147976365430384232675407015999781690408960000",
    "certified_total_upper": "901372490066979339466328131875218970886267983770731/64031050147976365430384232675407015999781690408960000"
  },
  {
    "N": 64,
    "T": 200000,
    "denominator": 16777216,
    "numerators": [
      15906192,
      15764894,
      1553702,
      13874282,
      -11321525,
      12512475,
      -14225,
      578373,
      -9959362,
      10906644,
      -1548939,
      9970459,
      -8274616,
      -9186468,
      932192,
      8196559,
      -1332916,
      8910205,
      89123,
      -9054038,
      -6668190,
      8441273,
      648815,
      -475829,
      -6345994,
      -110527,
      -1296353,
      6360000,
      6488149,
      6421001,
      -2794561,
      -5126378,
      -4610171,
      -5011945,
      2061636,
      5981179,
      -6115920,
      -5372458,
      -855350,
      5054097,
      6953050,
      3348115,
      -799772,
      387030,
      -6768848,
      3854115,
      -810734,
      274012,
      1550110,
      -3933708,
      165161,
      5720823,
      881574,
      -4543548,
      779756,
      -4348346,
      -4679569,
      3687672,
      494719,
      3788291,
      -5836438,
      755244,
      3775226
    ],
    "finite_lower": "801568259829/70368744177664",
    "finite_upper": "801568309829/70368744177664",
    "signed_period_mean_square": "120623820433066318987091541334048908041047449881555314362399085367/400916832798277571893584798927165343150233487041664054009528320000",
    "tail_discrepancy_constant": "6192905651031316789/140737488355328",
    "certified_tail_upper": "1898483883790982234819344004770595445936981030562836116528051231851397/728950630128755250358321965988779073775889104911784278768039392045957120000",
    "certified_total_upper": "8305353822888644917561155640932449922626543003665546886298371563102171397/728950630128755250358321965988779073775889104911784278768039392045957120000"
  },
  {
    "N": 128,
    "T": 200000,
    "denominator": 16777216,
    "numerators": [
      16009746,
      15912353,
      1414651,
      14256662,
      -12156587,
      13154922,
      19802,
      224214,
      -10539312,
      11615739,
      -1500007,
      11270198,
      -9746061,
      -10039952,
      -47891,
      10244897,
      -576396,
      9863958,
      -1212287,
      -9024610,
      -8101471,
      8210622,
      1351131,
      208717,
      -8472681,
      582456,
      -957807,
      7367741,
      6970377,
      8524391,
      -844427,
      -8212732,
      -5629342,
      -7975809,
      1623121,
      8278715,
      -8034864,
      -7582382,
      283893,
      7234017,
      5995281,
      6766460,
      -1308723,
      -698154,
      -3944447,
      6182333,
      -1579112,
      -410745,
      961245,
      -6817149,
      -532184,
      6190738,
      396926,
      -5807293,
      1064554,
      -6868637,
      -5046229,
      6004722,
      1236165,
      6318408,
      -6300993,
      263242,
      399156,
      -5168338,
      7071719,
      3194065,
      -1802522,
      -3967010,
      6551562,
      3442380,
      -3564844,
      3321904,
      -4869403,
      568313,
      635777,
      -4162216,
      6509036,
      4264230,
      -643774,
      -738757,
      -4322464,
      5197639,
      1486919,
      -5294931,
      -4346554,
      -2459099,
      -114101,
      3810599,
      2228244,
      -3914611,
      -1887501,
      -4935485,
      -4998221,
      -3500211,
      2433907,
      4483724,
      1330588,
      636536,
      -1253321,
      2410874,
      3543803,
      3684658,
      98840,
      4319341,
      -5243645,
      2277728,
      -1322112,
      2613258,
      3571203,
      -5300973,
      -143235,
      4165296,
      7195605,
      -2184858,
      1147293,
      18219,
      -5827866,
      -4185311,
      1034748,
      684836,
      -4392190,
      -3965658,
      -779254,
      -405250,
      -97856,
      4291252,
      945948
    ],
    "finite_lower": "1360664504927/140737488355328",
    "finite_upper": "1360664604927/140737488355328",
    "signed_period_mean_square": "338085173670319918095735346674355571475787983768041722369192403477548207698736208092930314722010615888345781154096540823001/752901096992105824926782903324603681497389279062322790953123475569196753705129886515774086469280235302695756469171650560000",
    "tail_discrepancy_constant": "150033190871036133427/281474976710656",
    "certified_tail_upper": "21315127052332005751998325377517815160369413219633764344321657088613791184823499339454800443995888384469177277081821707802062091/1368931619174919566115931084208168537670621679957051254087461658125429937154355092998778758920665416053980561219369956287667240960000",
    "certified_total_upper": "13256287717112799822650433489517858602912448330408147754902726477560907547070034521021704676809247634258527774083600535939402702091/1368931619174919566115931084208168537670621679957051254087461658125429937154355092998778758920665416053980561219369956287667240960000"
  },
  {
    "N": 256,
    "T": 200000,
    "denominator": 16777216,
    "numerators": [
      16132947,
      15990378,
      1211749,
      14660253,
      -12818076,
      13795541,
      -306569,
      610606,
      -11712114,
      12228370,
      -783057,
      11611511,
      -10725244,
      -10938227,
      368248,
      10944452,
      -928139,
      10982194,
      -903480,
      -10375952,
      -9077867,
      10353578,
      187380,
      -142489,
      -8472707,
      -757090,
      -1129190,
      9495326,
      8540313,
      8776123,
      367780,
      -8487068,
      -7807163,
      -10082143,
      451492,
      9460038,
      -8759884,
      -7820770,
      377558,
      8940053,
      7747218,
      7417352,
      -886405,
      -121051,
      -8449043,
      7314424,
      -835424,
      255119,
      1489966,
      -7729142,
      -1574403,
      8238890,
      1584070,
      -7695341,
      1310542,
      -7062095,
      -7595170,
      7228977,
      -81966,
      7019619,
      -6191530,
      -82244,
      -314929,
      -7811462,
      6620539,
      7260703,
      -1671878,
      -7402765,
      8284258,
      7396825,
      -1237314,
      7193654,
      -7660837,
      1288879,
      -697400,
      -7757001,
      5409474,
      6728638,
      873548,
      357368,
      -7401374,
      6211613,
      1699529,
      -7419966,
      -3937495,
      -6971958,
      826955,
      6435692,
      1045411,
      -6413303,
      1209608,
      -7027617,
      -3709695,
      -5816703,
      -329313,
      7071315,
      -361035,
      -1756898,
      -2602602,
      5610089,
      5007701,
      5899278,
      1296644,
      7749665,
      -5625331,
      5192398,
      -1372733,
      5214780,
      4321110,
      -8087662,
      -938993,
      6501623,
      6053475,
      -6210612,
      395007,
      1059,
      -4313998,
      -6191654,
      691522,
      -476722,
      -4018349,
      -5615208,
      -127775,
      530202,
      -59408,
      5115769,
      438041,
      -4163592,
      4742190,
      4220894,
      -1143254,
      -5577535,
      -5877626,
      1763230,
      1522823,
      4897406,
      5365798,
      4650924,
      1149017,
      -3039559,
      -4075496,
      -3895352,
      1738282,
      -4807145,
      -5361770,
      859400,
      -40095,
      3159145,
      -2510456,
      2460075,
      689853,
      -741043,
      6044611,
      -3179611,
      2070661,
      4266775,
      -4610139,
      -5541868,
      -2344404,
      -3923839,
      -599890,
      3458327,
      -1151533,
      4912958,
      -2846234,
      2429955,
      -1225786,
      727238,
      3684583,
      -1698790,
      -1103672,
      4642648,
      6892415,
      163669,
      -165424,
      -2910460,
      -5960192,
      4130817,
      -181037,
      3429851,
      4668008,
      -4793720,
      -902024,
      -4416181,
      5924697,
      -3097718,
      -1873739,
      -301905,
      6132980,
      3057571,
      1445716,
      4521393,
      -5645070,
      3832249,
      -1874649,
      2287266,
      1643915,
      4769139,
      3008061,
      -4324243,
      -4536372,
      -3394984,
      1251529,
      -2940589,
      -4653098,
      120012,
      -2206663,
      -4228853,
      -5967910,
      3679181,
      -287639,
      -3951575,
      -2117807,
      -1565735,
      1624376,
      -2549388,
      -4340448,
      -4085608,
      2691677,
      -1988737,
      7265437,
      984217,
      -234987,
      -946530,
      -6300020,
      3076518,
      1220558,
      3035497,
      5810280,
      4223759,
      -743946,
      4212458,
      372656,
      -4465118,
      -2697296,
      -3936863,
      5733938,
      3657760,
      -942713,
      2519450,
      779442,
      -145370,
      -476523,
      -345720,
      5888662,
      -2785495,
      -1044127,
      -3865422,
      296052,
      2771654,
      -52724,
      -3590707,
      -4060763,
      4779476,
      916850
    ],
    "finite_lower": "289861566151/35184372088832",
    "finite_upper": "289861591151/35184372088832",
    "signed_period_mean_square": "357440777357057786589673163333101744635676346460703539627780772226217573874105862710237101813837841251591214135264324741499975445199841642200079738266007826005642989733445624085999812510502953579206669732427605158814395522020875929/458560082528119005572053071054453065459599228204427149688084110579189855224300094755996146327127811574128221597156799288826277152605174823761398692104491318095858801450682089357826158465314325659302950239313147892129054326784000000",
    "tail_discrepancy_constant": "4596272560264268327943/562949953421312",
    "certified_tail_upper": "173429899192635702419213582393193095554868572766752889668383688047678030758509153048070525616063205137497076811710396169945883149371915782345787201661762736345134473585381120264540341084819774885331289554474298852168914091591151078570539/833758110822336239060986549325675519651461409937873050010092344227732270183796276397513620012950046923014952907613032219406271838552323198207297916859896036492463282249994163021273873319241115086279192848239791093296533922191553593344000000",
    "certified_total_upper": "7042230968822209841415139085911152657135049382950750051882958033511312222657090470897867829086891212659263623839819396236792385388875013909560827790833872702122181610664328335033980915464293999960343090968787368662211639742456118870570539/833758110822336239060986549325675519651461409937873050010092344227732270183796276397513620012950046923014952907613032219406271838552323198207297916859896036492463282249994163021273873319241115086279192848239791093296533922191553593344000000"
  },
  {
    "N": 8,
    "T": 200000,
    "denominator": 64,
    "numerators": [
      57,
      58,
      11,
      43,
      -26,
      37,
      5
    ],
    "label": "simple",
    "finite_lower": "6825740527243/281474976710656",
    "finite_upper": "6825740727243/281474976710656",
    "signed_period_mean_square": "102446123/642252800",
    "tail_discrepancy_constant": "7099/128",
    "certified_tail_upper": "3420841572441/4281749558827417600",
    "certified_total_upper": "55746221978845568644860417/2298746790603273337516851200"
  }
]
```

### VerifyLegalApproximators.py

```python
"""Independent exact-rational certificate checker; Python standard library only.
Usage: python3 VerifyLegalApproximators.py [N]
The full infinite-tail lemma and CRT covariance proof are in the companion note.
No floating-point arithmetic is used by this checker.
"""
import json, math, sys
from fractions import Fraction as Q
from pathlib import Path
rows=json.loads(Path(__file__).with_name('LegalApproximators.json').read_text())
for row in rows:
    N=row['N']
    if len(sys.argv)>1 and N!=int(sys.argv[1]):continue
    P=row['denominator']; T=row['T']; ks=row['numerators']; ds=range(2,N+1)
    assert len(ks)==N-1 and P>0 and T>0
    L=math.lcm(*ds); D=P*L; S=2**48
    a=[k*(L//d) for d,k in zip(ds,ks)]
    lower=upper=0
    for n in range(1,T+1):
        z=D-sum(v*(n%d) for d,v in zip(ds,a))
        q,r=divmod(S*z*z,D*D*n*(n+1))
        lower+=q; upper+=q+(r!=0)
    cs=[Q(k,P) for k in ks]
    mean=sum((c*Q(d-1,2*d) for d,c in zip(ds,cs)),Q())
    M=(1-mean)**2+sum((c*b*Q(math.gcd(d,e)**2-1,12*d*e) for d,c in zip(ds,cs) for e,b in zip(ds,cs)),Q())
    B=(2*sum((abs(c)*d for d,c in zip(ds,cs)),Q())+sum((abs(c*b)*math.lcm(d,e) for d,c in zip(ds,cs) for e,b in zip(ds,cs)),Q()))/4
    tail=M/Q(T+1)+B/Q((T+1)*(T+2))
    expected=dict(finite_lower=Q(lower,S),finite_upper=Q(upper,S),signed_period_mean_square=M,tail_discrepancy_constant=B,certified_tail_upper=tail,certified_total_upper=Q(upper,S)+tail)
    for field,value in expected.items():assert value==Q(row[field]),(N,field)
    assert M>=0
    if N==256:assert expected['certified_total_upper']<Q(8447,1000000)
    if row.get('label')=='simple':assert expected['certified_total_upper']<Q(24251,1000000)
    print('PASS',N,row.get('label','optimized'),flush=True)

```
