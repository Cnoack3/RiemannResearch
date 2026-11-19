# Numerical certificates for the zero-density and gap bounds

The Python programs below reproduce the finite inequalities used in the accompanying mathematical notes. The small-gap and Conrey endpoint checks use exact rational arithmetic in Python's standard library. The isolation checks use outward-rounded `mpmath.iv` intervals on a rational partition.

From the repository root, extract the programs into a temporary directory and run the relevant certificate.

```sh
replay_dir=$(mktemp -d)
python3 - "$replay_dir" <<'PYTHON'
from pathlib import Path
import re
import sys
note = Path("RiemannResearch/RH/BoundCertificateReplays20261119.md").read_text()
for name, source in re.findall(r"^### (verify_[a-z0-9_]+\.py)\n\n```python\n(.*?)^```$", note, re.M | re.S):
    (Path(sys.argv[1]) / name).write_text(source)
PYTHON
python3 "$replay_dir/verify_small_gap_kernel.py"
python3 "$replay_dir/verify_conrey_endpoint.py"
python3 "$replay_dir/verify_j21_isolation.py"
python3 "$replay_dir/verify_isolation_profile.py"
python3 "$replay_dir/verify_fixed_gap_isolation.py"
python3 "$replay_dir/verify_variational_isolation.py"
python3 "$replay_dir/verify_distinct_ordinates.py"
```

### verify_j21_isolation.py

```python
#!/usr/bin/env python3
"""Uniform J21 angular certificate from the published pair-energy enclosure.

Requires mpmath and the adjacent verify_isolation_profile.py. Only the external
J21 energy, clipped certificate score, and reward ceiling are used as inputs.
"""
from fractions import Fraction
from functools import cache
from mpmath import iv

from verify_isolation_profile import mt, pi, real, transform


STRIKE = Fraction(1425, 1000)
SLOPE = Fraction(7381, 10000)
SCORE = Fraction(67385328759554148395, 10**20)
PAIR_ENERGY_UPPER = Fraction(13280961313771574, 10**16)
REWARD_UPPER = Fraction(13, 1000)
RADIUS = Fraction(25074, 10**6)


@cache
def uniform_transform(y):
    if y == 0:
        return iv.mpf(1)
    t = pi*real(abs(y))
    return (iv.exp(t)-iv.exp(-t))/(2*t)


@cache
def covariance(x, y):
    return (uniform_transform(x+y)+uniform_transform(x-y))/2 - uniform_transform(x)*uniform_transform(y)


def certify(left, right, depth=0):
    # Truncating the proposed angular price at 1 suffices since weak<=1.
    charge = min(Fraction(1), SLOPE*max(Fraction(0), left-STRIKE))
    u = 2 - iv.sqrt(2-real(charge))
    d = 1-u
    m = transform(left)
    alpha = 4*m
    p = 2*right
    variance = (alpha*alpha*covariance(left,left) + d*d*covariance(p,p)
                -2*alpha*d*covariance(left,p))
    # The real variance is nonnegative, even if rounding straddles zero.
    sd = iv.sqrt(max(iv.mpf(0), variance.b))
    margin = 2*m*m-d*(1+transform(p)-u)-real(RADIUS)*sd
    if margin > 0:
        return 1, depth
    if depth >= 32:
        raise ArithmeticError((left,right,margin))
    middle = (left+right)/2
    n1,d1 = certify(left,middle,depth+1)
    n2,d2 = certify(middle,right,depth+1)
    return n1+n2,max(d1,d2)


def main():
    coercivity = 1-1/(2*pi**2)
    assert real(PAIR_ENERGY_UPPER) - (2-mt) < coercivity*real(RADIUS)**2
    assert 0 < real(RADIUS)
    end = STRIKE+1/SLOPE
    n0,d0 = certify(Fraction(0),STRIKE)
    n1,d1 = certify(STRIKE,end)
    u = 2*pi*real(STRIKE)
    profile = iv.log((1-iv.exp(-22*u/7))/(1-iv.exp(-8*u/7)))
    price = real(SLOPE)*profile/(4*pi)+4*pi**2/10**10
    lower = real(SCORE)-price/(1-real(REWARD_UPPER))
    assert iv.mpf("0.67385114") < lower
    print(f"{n0+n1} rational intervals, max depth {max(d0,d1)}")
    print(lower)


if __name__ == '__main__':
    main()
```

### verify_small_gap_kernel.py

```python
#!/usr/bin/env python3
"""Verify the rational Fourier kernel for Lamzouri's small-gap criterion.

Uses the Python standard library. All inequalities are checked with rational
arithmetic. Bernstein subdivision handles the two unbounded sign conditions.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from math import comb, factorial, gcd, isqrt, lcm, prod


GAP = F(784981, 1000000)
THETA = F(28571, 50000)
T_SCALE = F(3)
MARK_RADIUS = F(32543467, 40000000)
LAGUERRE_COEFFICIENTS = (
    1052183617178, 74902851334, -143856301288, -132760037152, -46186520124,
    -35159328436, 7126156103, 16089604607, -59430846, -6814169099,
    839864486, -1163592683, 2940168437, -6169623495, -709616871,
    1391150193, -1128549048, 790232133, 975437388, -2205222906,
    -1894463096, -1251437900, -376878704, -3356392499, -496759895,
    -889930464, 515817756, 559301630, -681240540, 503206622,
    444739275, -879707646, -175290345, 16002950, -21578798,
    -206679487, 571427009, -588498404, -168961892, -239860025,
    271365061, -375477409, -329935081, 408136661, 63543001,
    -24706303, 88857576, -202064335, 158371777, -112832520,
    -94700552, -93954574, 453501251, -412122175, -40445941,
    -73834170, 111085402, -180442581, 4055772, -66587260,
    -98516319, 21148014, 56191760, 70134951, -73743234,
    -12123409, 154556797, -137234425, -91274700, 11095015,
    37309739, -109387127, 52808736, -216924082, -29980078,
    -119553637, -58638637, -109480911, -17782719, -12243039,
    -94742322, 46277876, 52794301, -24451193,
)
LAGUERRE_COEFFICIENTS_105 = (
    1060434144658, 96716923187, -137014151799, -138398723025, -53212631445,
    -40032632191, 1818812246, 16635885973, 3031304691, -6694780944,
    -94305983, -1613146807, 3568063939, -5002861149, -2443212415,
    1181431655, -754863002, 87655570, 1609637473, -1282164796,
    -1756629131, -2213306156, 232737992, -3160131904, -1500694723,
    -1252971975, -403705084, 918457349, -226826622, -172375300,
    794456754, -277469639, -504601972, -266649127, 303350461,
    -529775354, 628998467, -234939496, -31385986, -461204944,
    -81670851, 188007098, -564970806, -115204756, 306916858,
    -47264974, 122312249, -3137208, -92449460, -31459398,
    93333376, -392724795, 251605233, 44944841, 52297447,
    -493433210, 35535952, -43748355, -248507518, -16523415,
    -212603309, -85687027, 47813051, -12351735, 210954406,
    -32961834, -60226049, 68833630, 49828275, -246445572,
    84904644, -30860269, 51160986, -48163229, 25683302,
    -188754140, 25394045, -61992308, -53744223, -11398082,
    -54372264, -46738085, -157345495, -12052783, 35998217,
    -137729285, -3963306, 56907748, 7447840, 77537168,
    39157705, -51201922, -15618854, -40558218, -17807260,
    36600070, 8354369, -14766174, 34697886, -1927598,
    -56655744, 2437363, 37954777, 2982444, -12290616,
    -3813807,
)
LAGUERRE_COEFFICIENTS_251 = (
    1061672069083, 87804646914, -142940608043, -134646490090, -55467228205,
    -32978268243, 6311098667, 15237259306, 720555599, -6779247516,
    -518770208, -1576730404, -715695889, -7675162659, -3518601258,
    126624457, 294109861, 1918699485, 1018097063, -2896859981,
    -2434801128, -769384922, 139411970, -1786893898, -972938573,
    -68484341, 211243377, -366291414, -927376293, 185434438,
    972193058, 76874010, -390027014, -320149882, -32755296,
    -86001916, 560918903, -202325242, -365053927, -426725110,
    9786587, 124301874, -509787907, -263334003, 239821091,
    101833981, 166194999, -19927684, -72211923, -180244973,
    -58665818, -407221422, -8744046, -82205408, -232785607,
    -491598937, -146441906, -7511314, -72659767, 83592612,
    -46613908, -89939301, -27563410, -40878014, 88665700,
    -17381848, -51279999, 139832793, 113747621, -250524329,
    -51946401, -8718130, 95921836, -53269775, 73015998,
    -145277608, -53844477, -6954429, -124299384, -7651437,
    -36393706, -69850820, -121333359, -76292477, 154474584,
    2564281, -63204701, 18088317, 53891653, -37899105,
    101817733, -87812722, -5080222, -50746013, 43742451,
    -34005769, 56872503, -96176014, 55457622, 14361907,
    -89321520, -81934574, -10344117, 71694515, -93227868,
    -51601206, -10485736, -96023318, 22574956, -6071437,
    -31867258, 21557953, -2544970, -26949600, 78104555,
    -2702100, 59210651, -94421385, -23995424, 1784220,
    76285540, -119116207, 43283374, -12317530, 28873940,
    -33715075, -10958262, -60419358, -34321701, 40456610,
    -43410608, 13883028, -35213257, -45750282, 25896763,
    -48814432, -29678738, 1380259, 18338868, -1098027,
    -56079906, -3102694, 79002758, -27791233, 24314497,
    -14182821, -5608228, -16876756, 43533065, -55498005,
    26515654, -33695145, 8111570, -8393697, 33990087,
    -13799828, -14739957, -25382490, -15975697, 40094282,
    -38536520, -18117667, 14232451, 3664238, -16668064,
    -50538999, -4804262, -14381473, -15338840, 2234220,
    -46062942, -33232614, 4793777, -13685461, 29149293,
    3531495, 14029829, 11867760, 16939068, -26690129,
    28401800, -31338449, 20846486, -47926283, 11261211,
    -5008042, 48502196, -29301697, 9439655, -924666,
    -12061611, 16104591, -21429417, 2829626, -11659127,
    10399150, 5638387, -8082217, 5172118, -32359090,
    -6164393, 312392, -10723857, -12633, -17402592,
    -20069696, -1150784, -23928034, -3229987, -13227718,
    12284800, -636473, -637296, -7406017, 19846371,
    -2272544, 20076633, -7920286, -1421292, -16813251,
    9912386, -18409635, 14382619, -17153532, 13704229,
    -7653220, 3623781, 382840, -8427428, 82890,
    -18306572, 1113249, -7183892, 1196172, 4020647,
    -9696400, 2080352, -3654078, -1040149, -81864,
    -4628095, 1366758, -3630471, -4455034, -4424506,
    -9620568, -7392590, -6277394, -4488333, -2293988,
    -3754090, -2250610,
)


LAGUERRE_COEFFICIENTS_285 = (
    1061970258779, 101859791419, -135176133484, -139901964190, -55045247041,
    -41354026613, -224185812, 16135668833, 4084240120, -6326541376,
    -37182571, -1919406666, 4042098249, -3645735711, -2328417784,
    1287146056, -496008873, -519902083, 1313255066, -975142422,
    -1290091686, -2620522763, -238177848, -3105142463, -2022836512,
    -1376922420, -843236987, 731585627, 343172659, -50624288,
    621731852, -268951289, -444233052, -610849409, 558328890,
    -512874094, 547969586, -236674106, -134661259, -169158091,
    -230979404, 100686832, -422015153, -318819549, 279775563,
    73432060, 109115728, -27417756, 92703890, -208893335,
    223824077, -512958038, 318738784, 21894442, 128127885,
    -359828711, -190768246, 112413090, -238238334, -44058871,
    -86496668, -234675823, 1034442, 47956398, 192279885,
    -124149, -64596942, -32538062, 266816491, -335510458,
    67148586, -139506918, 211244657, -154225432, 79451063,
    -181920480, -98062008, 43199761, -201612965, -38401356,
    -6950596, -15718058, -127108734, -139537078, 177207914,
    -3293466, -94367179, 42498802, 71718803, -78331466,
    174439630, -143120242, 77528243, -153534235, 70339533,
    -55101702, 182409416, -180062511, 17267616, 118834035,
    -100085456, -89404977, 4542253, 107173425, -92998925,
    -48023724, -2207321, -141673761, 41057169, 3322480,
    -81710941, 1719753, 46944053, -25856253, 60336728,
    -58641402, 180598630, -126310253, -39412752, -41245149,
    171553371, -207902336, 97950631, -7176762, 26775089,
    -1345484, 3834463, -30287315, -52223941, 64348266,
    -55696257, 57821856, 3271612, -120395006, 44140458,
    -6554066, -49094076, -47441752, 27532581, 33148883,
    -87312599, -54347960, 138172447, -72623189, 65199588,
    -11149841, 7187274, -60519311, 113926339, -129571741,
    67986191, -70287541, 48765708, -21579324, 29368613,
    -15062994, 41210167, -36924900, -90893214, 110811766,
    -35204602, -43925456, 16126834, 5870115, -1123157,
    -60250728, 27870114, -31182274, -21816471, 51673851,
    -52335417, -26836121, 35101316, -77941328, 55813436,
    2255349, -3743589, -15201320, 49828740, -33787358,
    50200254, -80441598, 79568964, -43523663, -19992344,
    -24864853, 72024411, -50850812, 31395355, 12468428,
    -46271861, 33845775, -24691067, 4560591, -16946359,
    14457319, 3746476, -16500425, 25734270, -43163244,
    10865257, 458581, -42363488, 30812750, -5548259,
    -41967210, 11569625, -26473007, 18052402, -30492330,
    9668208, 2720823, 11703554, -21554540, 45657674,
    -45831247, 44381350, -17169457, 12371210, -29256988,
    29716317, -48847211, 40516395, -22687902, 13789700,
    695373, -5567896, 16907666, -18348799, 12757291,
    -23909707, 20293326, -6875911, -17296204, 31669061,
    -23050569, 9956638, -10813338, -12424073, 5999967,
    -13583706, -4090529, -3706028, -25906844, 9316852,
    -30220919, -134231, -16386483, -10108395, -6565751,
    5101350, -19043508, 19555771, -13005707, 14324396,
    -2529046, 11991160, -2780244, 7859131, -15701688,
    16262743, -18783523, 8597769, -12396914, 11147978,
    -6463179, 2400189, 5492772, -8467315, 14242822,
    -11902198, 5580119, -2564223, -5336224, 9048016,
    -8694946, 7300210, -1980676, -3219240, 4698571,
    -3881079, 1974626, -667194, -2898565, 4972133,
    -2941165,
)
LAGUERRE_COEFFICIENTS_205 = (
    1062390660721109, 73468534073569, -143592388617243, -118722423043092, -51094006139434,
    -13870543327209, 8294910238586, 6757735245987, -2659476049446, -7036060810556,
    -6091243236873, -8764007810266, -6216652817266, -6793188218528, -1294274744831,
    1884819813178, 939206045525, 736794447200, 283261868570, -1237506650723,
    -422915556680, 104417745376, 593838339650, -1410248378800, -973236920064,
    -837395020023, -738302543691, -318674074168, -209535965842, 429843507466,
    710466444641, -275357895839, -731551343345, -669403341191, -358114357086,
    -409759558027, -173940978152, -366408749445, -395018147988, -41628430064,
    290837955489, 64517318111, -334618931717, -255598855347, 3035386764,
    65147180475, 124944145734, 26437154515, 48686264495, -128408286918,
    -177811054249, -276737385572, 14300533683, -58249035955, -317042027758,
    -467279934561, -339209330410, -185661395954, -129771482276, -80878875794,
    -62424867369, -8932571281, 56472732625, 57745499068, 43156346021,
    -47134199735, -13442172641, 47318881981, 35008393334, -118804948594,
    -37631072410, -18843994813, 39682589664, 11004946080, 10003495875,
    -69670267522, -48574197513, -2289264079, -25221155436, -29220069982,
    -69124222219, -109302591018, -115165280091, -61340136119, 24087661142,
    -13341068887, -22243482295, 45778538700, 70717883014, 27680955635,
    19055755487, -50547637813, -42573912943, -46841165481, -6427572048,
    -12024360218, 22745645852, -36293495215, -33313273840, -57623402712,
    -100993333569, -69700731913, -19846050647, 15618334379, -33843632785,
    -50901771049, -15886492522, -17506437693, 10701196910, 10301595365,
    -31418540998, -28029490434, -15038699023, -6431395187, 35746876176,
    30637908795, 18415086283, -18874179621, -16533915076, -14542521189,
    12832545294, -43332900037, -5927589723, 16560268485, 24176459377,
    -130176899, -14727108378, -19364541914, -28593957333, 10492213494,
    4907962501, -13327226695, -15593443887, -35900588678, -27284322779,
    -30201047572, -32880756991, -10624470902, -1598884319, -10671523115,
    -23187334913, -19347195009, 27969013064, 20861147457, 12225722889,
    -2829526809, 8659147336, -16527213866, 15714599050, -24449505180,
    -509544293, -22194687216, 4113320578, -3755969989, 10167416266,
    1588742070, -23329510334, -17952579895, -30411201805, -3281458226,
    -10730616694, -25883563081, -5252928978, -3969672134, -1253576191,
    -15740813458, -12601963958, 593685937, -2579093121, 1119469707,
    -4734822736, -26536342473, -10830355638, -16390531305, -739468202,
    -2453799338, 7298526860, -6626641454, 23259513869, -9448531384,
    20154922279, -13961807577, 17305362109, -21436579535, 451953252,
    -17931734970, 12948604190, 1360322935, -3448040360, 8379933995,
    -8201006360, 6266936656, -6104278075, -3298755461, -2646500306,
    -5201532507, 4870682220, -4765508085, 171074026, -3769849418,
    -8402010959, -3033422373, -3835459732, -109715225, 2197918488,
    -5331238870,
)
LAGUERRE_COEFFICIENTS_149 = (
    1061802607235719, 87923678969666, -143254955819522, -134968289429950, -55586267199632,
    -33073729080258, 6804497081923, 15410110604189, 443443095311, -6993443184237,
    -582941323496, -1809705432397, -1389162905855, -8174980432067, -3732624292702,
    130896490887, 545466742802, 2151957670251, 943767593603, -2840877626805,
    -2266622778294, -398776603095, 317565699515, -1685597273443, -854984083899,
    -81518678842, 91429027512, -463439652622, -938373943680, 237692862179,
    1026022903450, 96513646416, -442665314187, -384593304038, 2239336383,
    -57755864772, 559590794965, -264362688039, -345537045706, -431215141703,
    -9513377373, 72547407814, -546255942523, -232021808027, 234450117951,
    82921056184, 196961151079, 3436092394, -85800008593, -176672786523,
    -80965679161, -399406905937, 49433899820, -56788060988, -207325789288,
    -483278094491, -100547543204, 5981335512, -72756930435, 77065869282,
    -83683451927, -124020409761, -32125234829, -22691261980, 86105316726,
    -29783781838, -33239149074, 154743159532, 84362828582, -244008706522,
    -51044701379, -3466687262, 94109787286, -43883491305, 70463309857,
    -126437917723, -18462727233, -33390641029, -108842000851, 13218459474,
    -36972930809, -92377982874, -159081417200, -75733588773, 97914723168,
    -32306029671, -61143400007, 37152455987, 36686638689, 40196004127,
    78512409622, -54508539974, -44825196089, -64302716425, 29830326151,
    -7700849423, 42117645243, -69640261750, 89919710041, -9310746601,
    -86164748307, -48132063788, 19302274690, 59829258404, -44719629469,
    -23806906345, -30116826982, -54282586492, 18782694267, -22154763392,
    -12940921814, 3136386026, -20633642122, -31847992509, 37531349239,
    23190504308, 36965275063, -63926027155, -387805624, 13225759252,
    12683647211, -64184789496, 12174823320, -33544603429, 27019958322,
    -26004226699, -2512472816, -52460860574, -22781125089, -1339733441,
    -20054238964, 25899256504, -19423435944, -187844028, 12915019954,
    -34422692484, -13170104839, -10834784648, -6648664706, -14518759205,
    -33032690962, -2938618172, 12186397468, 3359676865, 16214241499,
    4031912520, -6856235329, 3572706820, -2091926742, -5665529538,
)
SCALE = 10**110


def require(condition, message):
    if not condition:
        raise ValueError(message)


def laguerre_polynomials(n):
    """L_j^(-1/2)(2y), coefficients in increasing order."""
    basis = [[F(1)], [F(1, 2), F(-2)]]
    for j in range(1, n):
        out = [F(0)] * (j + 2)
        for i, a in enumerate(basis[j]):
            out[i] += (2*j + F(1, 2))*a
            out[i+1] -= 2*a
        for i, a in enumerate(basis[j-1]):
            out[i] -= (j - F(1, 2))*a
        basis.append([a/(j + 1) for a in out])
    return basis


def fourier_polynomials(coefficients):
    n = len(coefficients) - 1
    p = [F(0)] * (n + 1)
    q = [F(0)] * (n + 1)
    for j, basis in enumerate(laguerre_polynomials(n)):
        for i, a in enumerate(basis):
            p[i] += coefficients[j]*a
            q[i] += (-1)**j * coefficients[j]*a
    return p, q


def verify_fourier_pair(p, q):
    """Cross-check the cosine transform using ordinary Gaussian moments.

    The transform of (pi*x**2)**k times the Gaussian equals the Gaussian
    times k! L_k^(-1/2)(pi*u**2). Its j-th monomial coefficient has the
    form used below, independent of the Laguerre eigenbasis construction.
    """
    n = len(p) - 1
    odds = [1]
    for k in range(n):
        odds.append((2*k+1)*odds[-1])
    for j, target in enumerate(q):
        actual = sum(p[k]*comb(k,j)*F(odds[k]//odds[j], 2**(k-j))
                     for k in range(j, n+1))
        require((-1)**j * actual == target, "Fourier polynomial mismatch")


def verify_fourier_differential_recurrence(p, q):
    """The same denominator-free Horner transport used by the Lean modules."""
    common = 1
    for coefficient in (*p, *q):
        common = common * coefficient.denominator // gcd(common, coefficient.denominator)
    transported = []
    for coefficient in reversed(p):
        degree = len(transported)
        extended = [0, *transported, 0, 0]
        transported = [
            (4*j + 1)*extended[j+1] - 2*extended[j] - (j+1)*(2*j+1)*extended[j+2]
            for j in range(degree+1)
        ]
        transported[0] += int(common*coefficient) * 2**(degree+1)
    require(transported == [int(common*c) * 2**len(p) for c in q],
            "Gaussian differential Fourier recurrence failed")


def shifted_negative(q, t):
    """Monomial coefficients of -Q(t+y)."""
    return [-sum(q[j]*comb(j,i)*t**(j-i) for j in range(i, len(q)))
            for i in range(len(q))]


def positive_on_half_line(a):
    """Certify P(y)>0 on y>=0 via y=u/(1-u), 0<=u<=1."""
    n = len(a) - 1
    weights = [a[k]/comb(n,k) for k in range(n+1)]
    denom = lcm(*(v.denominator for v in weights))
    queue = [([int(v*denom) for v in weights], 0)]
    visited = 0
    deepest = 0
    while queue:
        row, depth = queue.pop()
        require(depth <= 80, "Bernstein sign proof failed to finish")
        visited += 1
        deepest = max(deepest, depth)
        if min(row) > 0:
            continue
        require(row[0] > 0 and row[-1] > 0, "nonpositive endpoint")
        # de Casteljau at 1/2. The common factor 2^n keeps the rows integral.
        left, right = [], []
        for level in range(n+1):
            left.append(row[0] << (n-level))
            right.append(row[-1] << (n-level))
            row = [row[k] + row[k+1] for k in range(len(row)-1)]
        for half in (left, right[::-1]):
            common = gcd(*half)
            queue.append(([v//common for v in half], depth+1))
    return visited, deepest


class Interval:
    """Outward-rounded interval, stored in integer units of 10^-110."""
    def __init__(self, lo, hi):
        require(lo <= hi, "invalid interval")
        self.lo, self.hi = lo, hi

    @classmethod
    def rational(cls, r):
        r = F(r) * SCALE
        return cls(r.numerator//r.denominator, -((-r.numerator)//r.denominator))

    def __add__(self, other):
        return Interval(self.lo+other.lo, self.hi+other.hi)

    def __sub__(self, other):
        return Interval(self.lo-other.hi, self.hi-other.lo)

    def __mul__(self, other):
        endpoints = [a*b for a in (self.lo, self.hi)
                     for b in (other.lo, other.hi)]
        return Interval(min(endpoints)//SCALE, -((-max(endpoints))//SCALE))

    def reciprocal(self):
        require(self.lo > 0, "positive denominator required")
        return Interval(SCALE**2//self.hi, -((-SCALE**2)//self.lo))

    def __truediv__(self, other):
        return self * other.reciprocal()

    def sqrt(self):
        require(self.lo >= 0, "positive square root required")
        lo = isqrt(self.lo*SCALE)
        hi = isqrt(self.hi*SCALE)
        return Interval(lo, hi + (hi*hi < self.hi*SCALE))


def arctan_reciprocal(k):
    """Adjacent alternating partial sums enclose arctan(1/k)."""
    a = sum(F((-1)**j, (2*j+1)*k**(2*j+1)) for j in range(96))
    b = a + F(1, 193*k**193)
    return Interval(Interval.rational(a).lo, Interval.rational(b).hi)


def exp_negative(z):
    """Taylor's theorem supplies adjacent alternating bounds for exp(-z)."""
    require(z.lo >= 0, "positive exponential argument required")
    term = Interval.rational(1)
    total = term
    for k in range(1, 151):
        term = term*z/Interval.rational(k)
        total = total-term if k%2 else total+term
    next_term = term*z/Interval.rational(151)
    return Interval((total-next_term).lo, total.hi)


def evaluate(poly, y):
    acc = Interval.rational(0)
    for coefficient in reversed(poly):
        acc = acc*y + Interval.rational(coefficient)
    return acc


def objective(p, q, gap=GAP, theta=THETA, t=T_SCALE, radius=MARK_RADIUS):
    # Machin's identity. The final objective uses no floating-point constants.
    pi = (Interval.rational(16)*arctan_reciprocal(5)
          - Interval.rational(4)*arctan_reciprocal(239))
    s = Interval.rational(theta)*pi.sqrt()/Interval.rational(radius)
    edge = s*Interval.rational(gap)
    require((pi*edge*edge).lo >= Interval.rational(t).hi,
            "the Fourier sign threshold is outside the certified ray")
    z = Interval.rational(radius**2)
    # H-H'=P, so integral_0^z exp(-y)P(y)dy = H(0)-exp(-z)H(z).
    h = list(p)
    for j in range(len(h)-2, -1, -1):
        h[j] += (j+1)*h[j+1]
    area = Interval.rational(h[0])-exp_negative(z)*evaluate(h,z)
    return (Interval.rational(p[0])/s + s*area/pi)/Interval.rational(q[0])


def decimal_endpoint(value, places=18, upper=False):
    step = SCALE//10**places
    scaled = -((-value)//step) if upper else value//step
    return f"{scaled//10**places}.{scaled%10**places:0{places}d}"


KERNELS = {
    83: (LAGUERRE_COEFFICIENTS, GAP, THETA, T_SCALE, MARK_RADIUS),
    105: (LAGUERRE_COEFFICIENTS_105, F(784905297, 10**9),
          F(4,7)-F(1,10**12), F(31,10), F(8002915605081,10**13)),
    285: (LAGUERRE_COEFFICIENTS_285, F(392391339,500000000), F(3999999999993,7000000000000),
          F(78,25), F(79759777828511,100000000000000)),
    205: (LAGUERRE_COEFFICIENTS_205, F(301890443,500000000), F(999999999999,1000000000000),
          F(77,25), F(108082125014603,100000000000000)),
    149: (LAGUERRE_COEFFICIENTS_149, F(18498927,25000000), F(199999997,300000000),
          F(77,25), F(44152955860237,50000000000000)),
}


KERNELS[251] = (LAGUERRE_COEFFICIENTS_251, F(739922533,1000000000), F(2,3)-F(1,10**8),
                F(77,25), F(88301788907929,100000000000000))


DENSITY_CAPS = {251: F(4,3), 83: F(8,7), 105: F(8,7), 285: F(8,7), 205: F(2), 149: F(4,3)}

SCALAR_ROWS = (
    (285, "rarity", F(4819,6250), F(3,5), F(8228122238427,10000000000000), F(19)),
    (285, "rarity", F(37963,50000), F(5,8), F(8440012962401,10000000000000), F(31)),
    (149, "rarity", F(37381,50000), F(13,20), F(8698989006629,10000000000000), F(79)),
    (149, "rarity", F(74301,100000), F(33,50), F(4389177186269,5000000000000), F(199)),
    (149, "density", F(70321,100000), F(749999999999,1000000000000), F(9441061264171,10000000000000), F(3,2)),
    (205, "density", F(65181,100000), F(874999999999,1000000000000), F(5104739574973,5000000000000), F(7,4)),
    (149, "rarity", F(37,50), F(141759999978733,212670000000000), F(88298577597583,100000000000000), F(14176)),
    (251, "rarity", F(37,50), F(15697999999976447,23553000000000000),
     F(220721345810057,250000000000000), F(7849)),
    (149, "height-ingham", F(7,10), F(757551,1000000), F(118657294910033,125000000000000), F(273,1000)),
    (205, "height-guth-maynard", F(13,20), F(439777,500000), F(1023411703370383,10**15), F(861,2000)),
    (205, "height-tty-bourgain", F(3019,5000), F(999949,1000000), F(270200085567723,250000000000000), F(9,16)),
    (205, "height-lewko", F(3019,5000), F(999949,1000000), F(270200085567723,250000000000000), F(1,2)),
    (205, "height-tty-bourgain", F(301890443,500000000), F(1)-F(1,10**12), F(108082125014603,10**14), F(9,16)),
    (205, "height-lewko", F(301890443,500000000), F(1)-F(1,10**12), F(108082125014603,10**14), F(1,2)),
)


def verify_degree285_formal_data(weights, p, q, theta, radius):
    """Check the integer representation and the 32-term scalar used in Lean."""
    n = len(weights) - 1
    fact = [factorial(j) for j in range(n + 1)]
    odd = [prod(range(1, 2*j, 2)) for j in range(n + 1)]
    joint = 2**n * fact[n]
    for k in range(n + 1):
        original = [weights[j] * (-4)**k * 2**(n-j) * (fact[n]//fact[j])
                    * comb(j,k) * (odd[j]//odd[k]) for j in range(k,n+1)]
        require(sum(original) == joint*p[k], "integer input coefficient mismatch")
        require(sum((-1)**j*w for j,w in enumerate(original,k)) == joint*q[k],
                "integer output coefficient mismatch")
    primitive = list(p)
    for j in reversed(range(n)):
        primitive[j] += (j+1)*primitive[j+1]
    z = radius**2
    at_radius = F(0)
    for coefficient in reversed(primitive):
        at_radius = at_radius*z + coefficient
    exp_lower = sum(z**j/factorial(j) for j in range(32))
    required = F(177245385090551603,10**17)*q[0]
    objective_lower = (radius/theta)*p[0]+(theta/radius)*(primitive[0]-at_radius/exp_lower)
    require(at_radius >= 0 and exp_lower > 0 and required < objective_lower,
            "degree-285 formal scalar failed")
    print("All 572 integer monomial coefficients and the 32-term scalar agree with Lean.")


def verify_kernel(degree):
    coefficients, gap, theta, t, radius = KERNELS[degree]
    cap = DENSITY_CAPS[degree]
    require(F(1,2) < theta < min(F(1),cap/2) and 0 < gap < 1,
            "invalid support or gap parameter")
    p, q = fourier_polynomials(coefficients)
    require(len(p) == degree + 1 and q[0] > 0, "invalid Fourier normalization")
    verify_fourier_pair(p, q)
    verify_fourier_differential_recurrence(p, q)
    if degree == 285:
        verify_degree285_formal_data(coefficients, p, q, theta, radius)
    print("Degree", degree)
    print("P on [0,infinity), Bernstein nodes and maximum depth", positive_on_half_line(p))
    print("-Q on [t,infinity), Bernstein nodes and maximum depth",
          positive_on_half_line(shifted_negative(q,t)))
    result = objective(p,q,gap,theta,t,radius)
    require(result.lo > SCALE, "the strict Lamzouri inequality failed")
    print("Certified objective in [" + decimal_endpoint(result.lo) + ", "
          + decimal_endpoint(result.hi, upper=True) + "]")
    premise = ("unconditional" if cap == F(8,7)
               else "conditional on one-log SelbergDensity(" + str(cap) + ")")
    print("Certified Fourier kernel at gap", gap, "and support cutoff", theta, premise)
    for owner, mode, g, th, rad, power in SCALAR_ROWS:
        if degree != owner:
            continue
        require(0 < g < 1 and F(1,2) < th < 1, "invalid auxiliary support or gap")
        if mode == "density":
            require(2*th < power, "insufficient one-log exponent")
        elif mode == "rarity":
            require(F(4,7) <= th < F(2,3) and power > 6*th/(2-3*th),
                    "insufficient deletion power")
        elif mode == "height-ingham":
            require(0 < power < 1 and power > 3*th-2, "insufficient Ingham height power")
        elif mode == "height-guth-maynard":
            c = 2*th
            require(0 < power/c < F(1,2) and
                    5*power**2 + (F(11,2)*c-20)*power + 2*c < 0,
                    "Guth–Maynard quadratic crossing failed")
        elif mode == "height-tty-bourgain":
            require(0 < power < 1 and power > F(9,16)*th, "insufficient published far-strip power")
        elif mode == "height-lewko":
            require(0 < power < 1 and power > th/2, "insufficient registered far-strip power")
        else:
            raise ValueError("unrecognized density profile")
        tested = objective(p,q,g,th,t,rad)
        require(tested.lo > SCALE, "auxiliary functional failed")
        print("Certified", mode, "row at gap", g, "support", th, "parameter", power,
              "with objective >=", decimal_endpoint(tested.lo))


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, choices=sorted(KERNELS),
                        help="verify one degree (the default verifies every kernel and scalar row)")
    options = parser.parse_args()
    for degree in ([options.degree] if options.degree is not None else sorted(KERNELS)):
        verify_kernel(degree)
```

### verify_conrey_endpoint.py

```python
"""Rational certificate for the nearly optimal exponential envelope of Conrey's profile.

Run with Python 3. The two exact inequalities enclose the least c such that
F(u) <= c exp(-8u/7) for every u >= 0.
"""
from fractions import Fraction
from math import comb, factorial

LOWER = Fraction(1067349992, 10**9)
UPPER = Fraction(10673499921, 10**10)


def bernstein_coefficients(constant, order):
    # With t = exp(-2u/7), F(u) = log((1-t^11)/(1-t^4)).
    # Subtract 1-t^11 from (1-t^4) times the exponential Taylor lower bound.
    power = [Fraction(0) for _ in range(4 * order + 5)]
    power[0] = -1
    power[11] = 1
    for index in range(order + 1):
        term = constant**index / factorial(index)
        power[4 * index] += term
        power[4 * index + 4] -= term
    assert power[:4] == [0] * 4 and sum(power) == 0

    # Divide the polynomial by t^4(1-t) and convert to Bernstein form on [0,1].
    quotient = [sum(power[4 : i + 5]) for i in range(len(power) - 5)]
    degree = len(quotient) - 1
    return [
        sum(quotient[j] * Fraction(comb(k, j), comb(degree, j)) for j in range(k + 1))
        for k in range(degree + 1)
    ]


def subdivide(coefficients, position=Fraction(1, 2)):
    left = [coefficients[0]]
    right = [coefficients[-1]]
    while len(coefficients) > 1:
        coefficients = [(1-position)*a + position*b for a, b in zip(coefficients, coefficients[1:])]
        left.append(coefficients[0])
        right.append(coefficients[-1])
    return left, right[::-1]


def lower_certificate():
    t = Fraction(789633783, 10**9)
    argument = LOWER * t**4
    order = 16
    partial = sum(argument**k / factorial(k) for k in range(order + 1))
    first_omitted = argument ** (order + 1) / factorial(order + 1)
    exponential_upper = partial + first_omitted / (1 - argument / (order + 2))
    assert argument < order + 2
    assert exponential_upper < (1 - t**11) / (1 - t**4)


def upper_certificate(constant=UPPER, endpoint=Fraction(1), order=17):
    coefficients = bernstein_coefficients(constant, order)
    if endpoint < 1:
        coefficients, _ = subdivide(coefficients, endpoint)
    stack = [(coefficients, 0)]
    cells = []
    while stack:
        coefficients, depth = stack.pop()
        minimum = min(coefficients)
        if minimum >= 0:
            cells.append((depth, minimum))
            continue
        assert depth < 20
        left, right = subdivide(coefficients)
        stack.extend([(left, depth + 1), (right, depth + 1)])
    return len(cells), max(depth for depth, _ in cells), min(value for _, value in cells)


def endpoint_monotonicity_certificate():
    # Lower bound twelve times (1-t^11) d/dz of F(v)/z,
    # where z=e^(-8v/7)=t^4. The positive terms n=2,3,4
    # are retained; the negative terms after n=1 form a geometric majorant.
    power = [Fraction(0) for _ in range(20)]
    for index, coefficient in ((0, 6), (3, -21), (4, 8), (8, 9)):
        power[index] += coefficient
        power[index+11] -= coefficient
    power[14] -= 33
    endpoint = Fraction(73, 100)
    degree = len(power)-1
    coefficients = [
        sum(power[j]*endpoint**j*Fraction(comb(k, j), comb(degree, j)) for j in range(k+1))
        for k in range(degree+1)
    ]
    assert min(coefficients) > Fraction(399, 1000)


def exponential_bounds(argument, order=20):
    assert 0 <= argument < order + 2
    partial = sum(argument**k / factorial(k) for k in range(order + 1))
    tail = (argument ** (order + 1) / factorial(order + 1) /
            (1 - argument / (order + 2)))
    return partial, partial + tail


def positive_log_bounds(argument, order=16):
    # The atanh series has positive terms for arguments > 1.
    z = (argument - 1) / (argument + 1)
    assert 0 < z < 1
    partial = 2 * sum(z ** (2*j+1) / (2*j+1) for j in range(order + 1))
    tail = 2 * z**(2*order+3) / ((2*order+3)*(1-z**2))
    return partial, partial + tail


def pi_bounds():
    # pi = 16 arctan(1/5) - 4 arctan(1/239), by Machin's formula.
    def arctan_bounds(x):
        partial = sum((-1)**k * x**(2*k+1) / (2*k+1) for k in range(16))
        return partial, partial + x**33 / 33

    lower_a, upper_a = arctan_bounds(Fraction(1, 5))
    lower_b, upper_b = arctan_bounds(Fraction(1, 239))
    return 16*lower_a - 4*upper_b, 16*upper_a - 4*lower_b


def polylog_bounds(power, argument, order=26):
    partial = sum(argument**j / j**power for j in range(1, order+1))
    tail = argument**(order+1) / ((order+1)**power * (1-argument))
    return partial, partial+tail


def moment_certificate(n, density, left, right, lower, upper, density_upper=None):
    # F_d is linear below v_d and equals F above it. Integrating the tail
    # term by term expresses each incomplete gamma integral in polylogs.
    a, b = Fraction(8, 7), Fraction(22, 7)
    v_lo = Fraction(7, 2) * positive_log_bounds(1/right)[0]
    v_hi = Fraction(7, 2) * positive_log_bounds(1/left)[1]
    f_lo = positive_log_bounds((1-left**11)/(1-left**4))[0]
    f_hi = positive_log_bounds((1-right**11)/(1-right**4))[1]
    k = n-2
    tail_lo, tail_hi = Fraction(0), Fraction(0)
    for j in range(k+1):
        power = k-j+2
        den_a, den_b = a**(power-1), b**(power-1)
        value_lo = (polylog_bounds(power, left**4)[0] / den_a -
                    polylog_bounds(power, right**11)[1] / den_b)
        value_hi = (polylog_bounds(power, right**4)[1] / den_a -
                    polylog_bounds(power, left**11)[0] / den_b)
        assert value_lo > 0
        coefficient = Fraction(factorial(k), factorial(j))
        tail_lo += coefficient * v_lo**j * value_lo
        tail_hi += coefficient * v_hi**j * value_hi
    moment_lo = n*v_lo**(n-1)*f_lo + density*v_lo**n + n*(n-1)*tail_lo
    if density_upper is None:
        density_upper = density
    moment_hi = n*v_hi**(n-1)*f_hi + density_upper*v_hi**n + n*(n-1)*tail_hi
    assert lower < moment_lo and moment_hi < upper
    print(f"Its order-{n} microscopic moment cap lies between {lower} and {upper}.")


def capped_endpoint(density, threshold, shift, envelope, lower, upper, mean_lower, mean_upper, moment_ranges):
    # The low-threshold region uses the off-line mass. In the high region,
    # the shift bounds the tail by F(s-shift)/shift for all s >= v0+shift.
    a = Fraction(8, 7)
    b = Fraction(22, 7)
    _, _, minimum = upper_certificate(envelope, threshold, 14)
    assert minimum > 0
    exp_upper = exponential_bounds(a*shift)[1]
    assert exp_upper * max(density / threshold**4, envelope / shift) <= upper

    # A law with mass d at s_d = min_v(v+F(v)/d) and the rest at zero
    # meets every stop-loss constraint. F is strictly convex as explained
    # in the note, hence the equation F'(v_d)=-d locates this minimum.
    def derivative_plus_density(t):
        return b*t**11/(1-t**11) - a*t**4/(1-t**4) + density

    left, right = Fraction(7, 10), Fraction(73, 100)
    assert derivative_plus_density(left) > 0 > derivative_plus_density(right)
    for _ in range(42):
        middle = (left + right) / 2
        if derivative_plus_density(middle) >= 0:
            left = middle
        else:
            right = middle
    profile_lower = positive_log_bounds((1-left**11) / (1-left**4))[0]
    extremal_lower = density / right**4 * exponential_bounds(a*profile_lower/density)[0]
    assert lower < extremal_lower
    # d*s_d/(4*pi) is the optimized right displacement bound per unit height.
    profile_upper = positive_log_bounds((1-threshold**11) / (1-threshold**4))[1]
    strike_lower = Fraction(7, 2) * positive_log_bounds(1/right)[0]
    strike_upper = Fraction(7, 2) * positive_log_bounds(1/threshold)[1]
    pi_lower, pi_upper = pi_bounds()
    assert mean_lower < (density * strike_lower + profile_lower) / (4*pi_upper)
    assert (density * strike_upper + profile_upper) / (4*pi_lower) < mean_upper
    print(f"Off-line fraction {density} gives optimal prefactor between {lower} and {upper}.")
    print(f"Its normalized displacement cap lies between {mean_lower} and {mean_upper}.")
    for n, lower_bound, upper_bound in moment_ranges:
        moment_certificate(n, density, left, right, lower_bound, upper_bound)



def sampled_mean_certificate():
    mean = Fraction(64266, 100000)
    a, b = Fraction(8, 7), Fraction(22, 7)
    left, right = Fraction(70775425032680, 10**14), Fraction(70775425032681, 10**14)

    def slope(t):
        return a*t**4/(1-t**4) - b*t**11/(1-t**11)

    def tangent_mean(t):
        low, high = positive_log_bounds((1-t**11)/(1-t**4))
        vlow, vhigh = positive_log_bounds(1/t)
        return low + slope(t)*Fraction(7, 2)*vlow, high + slope(t)*Fraction(7, 2)*vhigh

    assert tangent_mean(left)[1] < mean < tangent_mean(right)[0]
    dlo, dhi = slope(left), slope(right)
    assert 0 < dlo < dhi < Fraction(32614389, 10**8)
    assert mean/Fraction(1, 3) > 1/a
    low = dlo*exponential_bounds(a*mean/dhi, 30)[0]
    high = dhi*exponential_bounds(a*mean/dlo, 30)[1]
    assert Fraction(3298233008, 10**9) < low <= high < Fraction(3298233009, 10**9)
    pi_low, pi_high = pi_bounds()
    assert Fraction(5114125786, 10**11) < mean/(4*pi_high) <= mean/(4*pi_low) < Fraction(5114125787, 10**11)
    print("The sampled-moment manuscript input gives endpoint prefactor in (3.298233008, 3.298233009).")
    moment_certificate(2, dlo, left, right, Fraction(1555657147, 10**9), Fraction(1555657148, 10**9), dhi)
    moment_certificate(3, dlo, left, right, Fraction(4553304063, 10**9), Fraction(4553304064, 10**9), dhi)
    moment_certificate(4, dlo, left, right, Fraction(16342166485, 10**9), Fraction(16342166486, 10**9), dhi)


if __name__ == "__main__":
    lower_certificate()
    endpoint_monotonicity_certificate()
    cells, depth, minimum = upper_certificate()
    assert minimum > Fraction(9, 10**11)
    print(f"{LOWER} < sup exp(8u/7) F(u) <= {UPPER}")
    print(f"Certified on {cells} dyadic cells of maximum depth {depth}.")

    capped_endpoint(
        Fraction(1, 3), Fraction(7202190107, 10**10), Fraction(8580382279, 10**10),
        Fraction(10629848130, 10**10), Fraction(3302905566, 10**9),
        Fraction(3302905567, 10**9), Fraction(5323037840, 10**11), Fraction(5323037841, 10**11),
        [(2, Fraction(1586614444, 10**9), Fraction(1586614445, 10**9)),
         (4, Fraction(16385242327, 10**9), Fraction(16385242328, 10**9))],
    )
    ten_point_fraction = Fraction(
        66732501992025865314318003264831248651423598405947,
        99062663304046530894651923264741897583007812500000,
    )
    capped_endpoint(
        1 - ten_point_fraction, Fraction(7163736600, 10**10), Fraction(8574334200, 10**10),
        Fraction(10625266759, 10**10), Fraction(3301527974, 10**9),
        Fraction(3301527976, 10**9), Fraction(5258782449, 10**11), Fraction(5258782450, 10**11),
        [(2, Fraction(1577263569, 10**9), Fraction(1577263570, 10**9)),
         (4, Fraction(16372700918, 10**9), Fraction(16372700919, 10**9))],
    )
    # rStation paper 179, Theorem 1. The fraction is a separately assumed
    # manuscript bound, independent of the preceding ten-point certificate.
    capped_endpoint(
        Fraction(32614389, 10**8), Fraction(716253268375, 10**12),
        Fraction(857415000929, 10**12), Fraction(1062512033489, 10**12),
        Fraction(3301483902, 10**9), Fraction(3301483903, 10**9),
        Fraction(5256767630, 10**11), Fraction(5256767631, 10**11),
        [(2, Fraction(1576967912, 10**9), Fraction(1576967913, 10**9)),
         (4, Fraction(16372297761, 10**9), Fraction(16372297762, 10**9))],
    )
    sampled_mean_certificate()
```

### verify_isolation_profile.py

```python
#!/usr/bin/env python3
"""Replay the Montgomery–Taylor isolation majorant and Conrey-profile evaluation.

Requires mpmath. Every comparison uses its interval context; the argument
cover and the chosen constants are exact rational numbers.
"""
from fractions import Fraction
from functools import cache

from mpmath import iv


iv.dps = 65
A = Fraction(303, 250)
SLOPE = Fraction(7061, 10000)
RIGHT = Fraction(3)


def real(q: Fraction):
    return iv.mpf(q.numerator) / q.denominator


pi = iv.pi
sqrt_two = iv.sqrt(2)
cot = iv.cot(1 / sqrt_two)
mt = iv.mpf(3) / 2 - cot / sqrt_two


@cache
def transform(q: Fraction):
    y = real(q)
    t = pi * y
    e = iv.exp(t)
    e_inv = 1 / e
    cosh = (e + e_inv) / 2
    sinh = (e - e_inv) / 2
    return (cosh + sqrt_two * t * cot * sinh) / (1 + 2 * t**2)


def kim_upper(left, right):
    return 1 - 4 * transform(left)**2 / (1 + transform(2 * right))


def verify_cover(left, right, threshold, slope, penalty_upper, depth=0):
    upper_defect = penalty_upper(left, right)
    lower_majorant = real(slope * max(Fraction(0), left - threshold))
    if upper_defect < lower_majorant:
        return 1, depth
    if depth >= 32:
        raise ArithmeticError(f"uncertified interval [{left}, {right}]")
    mid = (left + right) / 2
    n_left, depth_left = verify_cover(left, mid, threshold, slope, penalty_upper, depth + 1)
    n_right, depth_right = verify_cover(mid, right, threshold, slope, penalty_upper, depth + 1)
    return n_left + n_right, max(depth_left, depth_right)


def cover(threshold, slope, penalty_upper):
    left, dl = verify_cover(Fraction(0), threshold, threshold, slope, penalty_upper)
    right, dr = verify_cover(threshold, RIGHT, threshold, slope, penalty_upper)
    assert slope * (RIGHT - threshold) > 1
    return left + right, max(dl, dr)


def lower_bound(threshold: Fraction, slope: Fraction):
    u = 2 * pi * real(threshold)
    profile = iv.log((1 - iv.exp(-22 * u / 7)) / (1 - iv.exp(-8 * u / 7)))
    return mt - real(slope) * profile / (4 * pi) - 6 * pi**2 / 10**10


# Knausgård's eight-point cosine window and the pinned ten-point AM window.
EIGHT = (122290, -45012, 16241, 1887, 2711, 3731, -5307, 2982, -5153, 5358)
TEN = (14540341, -17051850, 6940151, 5482678, -200220, 3939293, -5615406,
       3367926, -4987106, 5017749, -4274153, 5029336, -4508275, 744709,
       541564, -371255)
TEN_DENOM = 8388608000000000000000000000000


@cache
def window_transform(kind, q):
    if q == 0:
        return iv.mpf(1)
    y = real(q)
    t = pi * y
    e = iv.exp(t)
    sinh = (e - 1 / e) / 2
    if kind == "eight":
        coeffs, scale, base = EIGHT, iv.mpf(1) / 10**6, sinh / t
    else:
        coeffs = TEN
        scale = 1 / (10**9 * sqrt_two * iv.sin(1 / sqrt_two))
        base = transform(q)
    # Integral of cos(2πju)cosh(2πyu) on [-1/2,1/2].
    # Evaluate the rational coefficient sum exactly before interval conversion.
    correction = sum(Fraction(c * (-1)**j) * q / (q*q + j*j)
                     for j, c in enumerate(coeffs, 1))
    return base + scale * sinh * real(correction) / pi


def eigen_penalty_upper(kind, left, right):
    # The least eigenvalue of [[A,sqrt(2)M],[sqrt(2)M,1]] increases
    # with A and decreases with M. Both Laplace transforms increase with y.
    A_right = 1 + window_transform(kind, 2 * right)
    M_left = window_transform(kind, left)
    w_upper = (A_right + 1 - iv.sqrt((A_right - 1)**2 + 8*M_left**2)) / 2
    assert w_upper < 2
    return 4 * w_upper - w_upper**2 - 2


def check_energy_bounds():
    # The weight |u−v| has second derivative 2δ. Orthogonality therefore
    # gives the quadratic coefficient 1/2−1/(4π²j²) of each cosine mode.
    def quadratic(j):
        return iv.mpf(1)/2 - 1/(4*pi**2*j*j)

    c8 = iv.mpf(4)/3
    for j, w in enumerate(EIGHT, 1):
        aj = iv.mpf(w)/10**6
        c8 += aj*(-1)**j/(pi**2*j*j) + aj**2*quadratic(j)
    assert c8 < iv.mpf("1.327947272845")
    # Montgomery–Taylor is stationary under any zero-integral perturbation.
    ten_core = mt - sum((iv.mpf(w)/10**9)**2 * quadratic(j)
                        for j, w in enumerate(TEN, 1)) / (2*iv.sin(1/sqrt_two)**2)
    ten_floor = real(Fraction(67206299948881203266318003264831248651423598405947, 10**50))
    assert ten_floor < ten_core
    return Fraction(2) - Fraction(1327947272845, 10**12)


def replay_window(kind, threshold, slope, core, reward, charge):
    count, depth = cover(threshold, slope, lambda l, r: eigen_penalty_upper(kind, l, r))
    u = 2 * pi * real(threshold)
    F = iv.log((1 - iv.exp(-22*u/7)) / (1 - iv.exp(-8*u/7)))
    result = (real(core-charge) - real(slope)*F/(4*pi) - 4*pi**2/10**10) / real(1-reward)
    print(kind, "strict eigenvalue majorant", count, "intervals, depth", depth)
    print(kind, "full-array isolation bound", result)
    return result


def main():
    count, depth = cover(A, SLOPE, kim_upper)
    original = lower_bound(Fraction(6, 5), Fraction(663, 1000))
    improved = lower_bound(A, SLOPE)
    assert iv.mpf("0.6724911466") < original < iv.mpf("0.6724911467")
    assert iv.mpf("0.6724913656") < improved < iv.mpf("0.6724913657")
    print("MT strict majorant", count, "intervals, depth", depth)
    print("Kim parameters with Conrey profile", original)
    print("Reoptimized MT parameters with Conrey profile", improved)
    eight = replay_window("eight", Fraction(1439, 1000), Fraction(7358, 10000),
                          check_energy_bounds(), Fraction(8722, 10**6),
                          Fraction(4389, 10**6))
    ten = replay_window("ten", Fraction(36, 25), Fraction(7348, 10000),
                        Fraction(67206299948881203266318003264831248651423598405947, 10**50),
                        Fraction(78629501063688385648757192860, TEN_DENOM),
                        Fraction(39745053312603427868508160000, TEN_DENOM))
    assert iv.mpf("0.6735364025") < eight < iv.mpf("0.6735364026")
    assert iv.mpf("0.6736373773") < ten < iv.mpf("0.6736373774")


if __name__ == "__main__":
    main()
```

### verify_distinct_ordinates.py

```python
#!/usr/bin/env python3
"""Directed one- and two-variable certificates for distinct ordinate counts."""
from fractions import Fraction
from functools import cache
from mpmath import iv

from verify_isolation_profile import (
    TEN_DENOM, mt, pi, real, transform, verify_cover, window_transform,
)


def price(s):
    """Monotone upper bound on the clipped quadratic g_2."""
    ub=min(iv.mpf(2),max(iv.mpf(0),s.b))
    return 4*ub-ub*ub


def weak(A,B,Q):
    return (A+B-iv.sqrt((A-B)**2+4*Q**2))/2


def verify_triangle(M,z,a,l,max_y):
    @cache
    def Ay(y):
        return 1+M(2*y)
    count=0
    longest=0

    def rec(x0,x1,y0,y1,depth):
        nonlocal count,longest
        if x0>y1:
            return
        # Only x≤y is needed. Dropping the empty corner at x>y improves
        # the lower bound for the right side of the price majorant.
        yl=max(y0,x0)
        xl=x0
        xu=min(x1,y1)
        cross=M(xl+yl)+M(max(Fraction(0),yl-xu))
        cap=price(weak(Ay(xu),Ay(y1),cross))-2
        if cap<real(l*max(Fraction(0),yl-a)):
            count+=1
            longest=max(longest,depth)
            return
        if depth>=55:
            raise ArithmeticError((x0,x1,y0,y1))
        if xu-xl>=y1-yl:
            m=(xl+xu)/2
            rec(xl,m,yl,y1,depth+1)
            rec(m,xu,yl,y1,depth+1)
        else:
            m=(yl+y1)/2
            rec(xl,xu,yl,m,depth+1)
            rec(xl,xu,m,y1,depth+1)
    rec(Fraction(0),max_y,Fraction(0),a,0)
    rec(Fraction(0),max_y,a,max_y,0)
    return count,longest


def replay(kind,z,a,l,floor):
    max_y=Fraction(2)
    @cache
    def M(y):
        y=abs(y)
        if not y:
            return iv.mpf(1)
        return transform(y) if kind=='mt' else window_transform('ten',y)
    Az=1+M(2*z)
    vz=M(z)
    g0=price(1-2*vz*vz/Az)
    assert g0<1
    credit=min((iv.mpf(4)/3).a,(1+(1-g0)/2).a)
    assert l*(max_y-a)>3

    def compact(u,v):
        A=1+M(2*v)
        B=M(u+z)+M(u-z)
        residual=A-B*B/Az
        ub=(price(residual)-credit).b
        for n in (1,2,3):
            w=weak(A,iv.mpf(n),iv.sqrt(2*n)*M(u))
            w=min(iv.mpf(n),w.b)
            ub=max(ub,(price(w)-n).b)
        return ub
    n0,d0=verify_cover(Fraction(0),a,a,l,compact)
    n1,d1=verify_cover(a,max_y,a,l,compact)
    nt,dt=verify_triangle(M,z,a,l,max_y)
    u=2*pi*real(a)
    F=iv.log((1-iv.exp(-22*u/7))/(1-iv.exp(-8*u/7)))
    if kind=='mt':
        H,x,b=mt,iv.mpf(0),iv.mpf(0)
    else:
        H=real(Fraction(67206299948881203266318003264831248651423598405947,10**50))
        x=real(Fraction(78629501063688385648757192860,TEN_DENOM))
        b=real(Fraction(39745053312603427868508160000,TEN_DENOM))
    final=(1+H-x-b-real(l)*F/(4*pi))/(2*(1-x))
    assert real(floor)<final
    print(f"{kind}: {n0+n1} compact intervals, depth {max(d0,d1)}; "
          f"{nt} triangle boxes, depth {dt}; lower proportion {floor}",flush=True)
    print(final,flush=True)


if __name__=='__main__':
    replay('mt',Fraction(64,100),Fraction(795,1000),Fraction(1762,100),Fraction(83392118,10**8))
    replay('ten',Fraction(641,1000),Fraction(797,1000),Fraction(1769,100),Fraction(83449280,10**8))
```

### verify_variational_isolation.py

```python
#!/usr/bin/env python3
"""Replay the optimal two-frequency, zero-horizontal-cost isolation windows.

Requires mpmath. Every input cutoff and every subdivision endpoint is rational.
No outside interaction certificate, numerical optimizer or zero sample is used.
"""
from fractions import Fraction
from mpmath import iv

iv.dps = 75
pi = iv.pi
sqrt2 = iv.sqrt(2)
theta = 1/sqrt2
cot = iv.cot(theta)
C_MT = iv.mpf(1)/2 + cot/sqrt2
e = C_MT-1
r2 = 1/(2*pi*pi)


def real(q):
    return iv.mpf(q.numerator)/q.denominator


def sinc(q):
    if q == 0:
        return iv.mpf(1)
    t = pi*real(q)
    return iv.sin(t)/t


def mt_kernel(q):
    t = pi*real(q)
    return (iv.cos(t)-sqrt2*t*cot*iv.sin(t))/(1-2*t*t)


def cross_kernel(a,b):
    return (sinc(a-b)+sinc(a+b))/2


def witness(c):
    s = sinc(c)
    b = e*real(c)**2/(mt_kernel(c)*(real(c)**2-r2))
    a = 1-b*s
    def K(q):
        return a*mt_kernel(q)+b*cross_kernel(c,q)
    k = K(c)
    proportion = 1-e/(mt_kernel(c)*k)
    return a,b,K,k,proportion


def replay(c, lower):
    a,b,K,k,proportion=witness(c)
    assert 0<c<1 and 0<a and 0<b
    assert 0 < a*cot/sqrt2+b*iv.cos(pi*real(c))
    d=K(2*c)
    p=1-k*k
    assert 0<k and 0<d and 0<p<1
    assert 1<3*p and 1-d*d<2*p
    t=2-(d+iv.sqrt(d*d+8*k*k))/2
    assert 0<t<2 and 4*t-t*t/2<2+3*p
    if 2*c > 1:
        h=(2*c-1)/128
        for i in range(128):
            u=1+i*h
            assert (K(u+h)-K(u))/real(h)+pi**2*real(h)/2<0
    # Independently evaluate the physical pair-energy coefficient from its
    # kernel integrals. The test at the optimal f has a Rayleigh identity.
    q2=real(c)**2
    s=sinc(c)
    D=s/2+iv.cos(pi*real(c))/(2*pi*pi*q2)
    Q=cross_kernel(c,c)*(1-r2/q2)+D*s
    energy=C_MT+b*b*(Q-C_MT*s*s)
    directly=1-(energy-1)/(k*k)
    assert not(directly>proportion or directly<proportion)
    assert real(lower) < directly and real(lower) < proportion
    print(f"c≤{c}, zero horizontal charge, lower bound {lower}", flush=True)
    print(proportion, flush=True)


def main():
    extra=Fraction(1,10**8)
    rows=(
        (Fraction(49,100)+extra,Fraction(32175415,10**8)),
        (Fraction(1,2)+extra,Fraction(30187816,10**8)),
        (Fraction(11,20)+extra,Fraction(18901531,10**8)),
        (Fraction(3,5)+extra,Fraction(5214801,10**8)),
        (Fraction(61,100)+extra,Fraction(2184040,10**8)),
        (Fraction(61701890,10**8),Fraction(1,10**8)),
    )
    for c,floor in rows:
        replay(c,floor)
    upper=Fraction(61701891,10**8)
    assert witness(upper)[4] < 0
    print("Upper endpoint certificate",upper,witness(upper)[4])


if __name__ == "__main__":
    main()
```

### verify_fixed_gap_isolation.py

```python
#!/usr/bin/env python3
"""Replay the two-assignment spectral bounds at the specified fixed gaps.

Run next to verify_isolation_profile.py. Both use outward-rounded mpmath
interval arithmetic. All parameters and all subdivision endpoints are rational.
"""
from fractions import Fraction
from functools import cache

from mpmath import iv

from verify_isolation_profile import (
    EIGHT, TEN, TEN_DENOM, check_energy_bounds, cot, mt, pi,
    real, sqrt_two, verify_cover, window_transform,
)


@cache
def mixed_transform(kind, y: Fraction, c: Fraction):
    """Integral f(u) cosh(2πyu) cos(2πcu) du = Re M(y+ic)."""
    if y == 0 and c == 0:
        return iv.mpf(1)
    if y == 0 and c == 1:
        if isinstance(kind, tuple):
            return 1/(2*pi*pi-1) + iv.mpf(kind[0])/20000
        if kind == 'eight':
            return iv.mpf(EIGHT[0]) / (2*10**6)
        return 1/(2*pi*pi-1) + iv.mpf(TEN[0])/(2*10**9*sqrt_two*iv.sin(1/sqrt_two))
    z = iv.mpc(real(y), real(c))
    t = pi*z
    exp_t = iv.exp(t)
    sinh = (exp_t - 1/exp_t)/2
    cosh = (exp_t + 1/exp_t)/2
    if kind == "eight":
        base, coefficients, scale = sinh/t, EIGHT, iv.mpf(1)/10**6
    else:
        base = (cosh + sqrt_two*t*cot*sinh)/(1+2*t*t)
        if isinstance(kind, tuple):
            coefficients, scale = kind, iv.mpf(1)/10000
        else:
            coefficients = TEN
            scale = 1/(10**9*sqrt_two*iv.sin(1/sqrt_two))
    # Real and imaginary parts of the rational correction before conversion.
    re_corr = Fraction(0)
    im_corr = Fraction(0)
    for j, coeff in enumerate(coefficients, 1):
        sign = coeff*(-1)**j
        norm = (y*y-c*c+j*j)**2 + (2*y*c)**2
        re_corr += sign*y*(y*y+c*c+j*j)/norm
        im_corr += sign*c*(j*j-y*y-c*c)/norm
    return (base + (scale*sinh/pi)*iv.mpc(real(re_corr), real(im_corr))).real


def g(w):
    return 4*w-w*w


def replay(kind, C, a, slope, lower):
    tuned = isinstance(kind, tuple)
    name = 'tuned' if tuned else kind
    if tuned:
        # The whole specified density is positive, hence has unit total variation.
        assert cot/sqrt_two > sum(abs(w) for w in kind)/iv.mpf(10**4)
    def M(y):
        return mixed_transform(kind, y, Fraction(0)) if tuned else window_transform(kind,y)
    A_one = mixed_transform(kind, Fraction(0), C)
    A_two = mixed_transform(kind, Fraction(0), 2*C)
    penalty = 1-A_one**2
    weak_pair = 1-A_two
    assert Fraction(0) < C <= Fraction(1)
    # K decreases automatically on [0,1]. Above one, the second derivative
    # bound |K''| ≤ π² controls slopes on each interval of a rational mesh.
    if 2*C > 1:
        bins = 128
        h = (2*C-1)/bins
        for i in range(bins):
            left = 1+i*h
            slope_K = (mixed_transform(kind, 0, left+h)-mixed_transform(kind, 0, left))/real(h)
            assert slope_K + pi**2*real(h)/2 < 0
    assert 0 < A_two and 0 < A_one
    assert 0 <= penalty < 1
    t = 2 - (A_two + iv.sqrt(A_two**2 + 8*A_one**2))/2
    assert 0 <= t <= 2
    assert 4*t - t*t/2 < 2 + 3*penalty
    endpoint = Fraction(4)
    assert 1-3*penalty < real(slope*(endpoint-a))
    assert g(weak_pair)-4*penalty < real(slope*(endpoint-a))

    def compact_bound(left, right):
        # The entry increases with the height variable because the integrand
        # f(u)cos(2πCu)cosh(2πyu) increases while 0<C<1/2.
        A = 1+M(2*right)
        J = mixed_transform(kind, left, C)
        if C > Fraction(1,2):
            # cos(2πCt)≥cos(πC) throughout the support. The difference of
            # the two cosh factors is positive and has integral M(v)-M(u).
            J += iv.cos(pi*real(C))*(M(right)-M(left))
        J = iv.mpf([max(iv.mpf(0), J.a), max(iv.mpf(0), J.b)])
        w1 = (A+1-iv.sqrt((A-1)**2+8*J**2))/2
        w2 = (A+2-iv.sqrt((A-2)**2+16*J**2))/2
        # g increases up to 2. Both genuine two-by-two weak eigenvalues
        # are bounded by their respective smaller diagonal entries.
        w1 = min(iv.mpf(1), max(iv.mpf(0), w1.b))
        w2 = min(iv.mpf(2), max(iv.mpf(0), w2.b))
        s1 = g(w1)-2-3*penalty
        s2 = g(w2)+g(weak_pair)-4-4*penalty
        return iv.mpf([max(s1.a, s2.a), max(s1.b, s2.b)])

    left, dl = verify_cover(Fraction(0), a, a, slope, compact_bound)
    right, dr = verify_cover(a, endpoint, a, slope, compact_bound)
    count, depth = left+right, max(dl,dr)
    if tuned:
        # Stationarity at the Montgomery–Taylor density and orthogonality
        # of its mean-zero cosine perturbations give this exact energy.
        h = mt - sum((iv.mpf(w)/10**4)**2 * (iv.mpf(1)/2 - 1/(4*pi*pi*j*j))
                     for j,w in enumerate(kind,1))
        x, b = Fraction(0), Fraction(0)
    elif kind == "eight":
        h, x, b = check_energy_bounds(), Fraction(8722,10**6), Fraction(4389,10**6)
    else:
        h = Fraction(67206299948881203266318003264831248651423598405947,10**50)
        x = Fraction(78629501063688385648757192860,TEN_DENOM)
        b = Fraction(39745053312603427868508160000,TEN_DENOM)
    u = 2*pi*real(a)
    F = iv.log((1-iv.exp(-22*u/7))/(1-iv.exp(-8*u/7)))
    denominator = real(1-x)-penalty
    assert 0 < denominator
    numerator = h if tuned else real(h-b)
    proportion = (numerator-real(slope)*F/(4*pi)-penalty)/denominator
    assert real(lower) < proportion
    print(f"{name} c≤{C} a={a} slope={slope}: {count} intervals, depth {depth}")
    print("Isolated lower bound", proportion)


def main():
    tiny = Fraction(1,100000)
    extra = Fraction(1,10**8)
    rows = (
        ("eight", tiny, Fraction(1439,1000), Fraction(7358,10000), Fraction(673536406,10**9)),
        ("ten", tiny, Fraction(36,25), Fraction(7348,10000), Fraction(673637381,10**9)),
        ("ten", Fraction(831944,10**7), Fraction(1455,1000), Fraction(6912,10000), Fraction(2,3)),
        ("ten", Fraction(1,6)+extra, Fraction(1519,1000), Fraction(5529,10000),
         Fraction(64455851,10**8)),
        ("ten", Fraction(1,4)+extra, Fraction(1148,1000), Fraction(8426,10000),
         Fraction(60369938,10**8)),
        ("ten", Fraction(1,3)+extra, Fraction(819,1000), Fraction(14876,10000),
         Fraction(53615692,10**8)),
        ("ten", Fraction(2,5)+extra, Fraction(652,1000), Fraction(18596,10000),
         Fraction(45248405,10**8)),
        ('ten', Fraction(9,20)+extra, Fraction(561,1000), Fraction(19813,10000),
         Fraction(36348337,10**8)),
        ('ten', Fraction(1,2), Fraction(491,1000), Fraction(19211,10000),
         Fraction(24214815,10**8)),
    )
    tuned_rows = (
        ((859,-189,82,-46,29,-20,15,-11), Fraction(1,3)+extra, 841, 14688, 53929888),
        ((1322,-278,120,-67,43,-29,22,-17), Fraction(2,5)+extra, 695, 18296, 46427262),
        ((1772,-358,153,-85,54,-38,28,-21), Fraction(9,20)+extra, 622, 19507, 38986860),
        ((2320,-446,190,-105,67,-46,34,-26), Fraction(1,2)+extra, 574, 19559, 29675518),
        ((2978,-540,228,-126,80,-55,41,-31), Fraction(11,20)+extra, 546, 18460, 18242429),
        ((3776,-638,267,-147,93,-64,47,-36), Fraction(3,5)+extra, 539, 16910, 4520996),
        ((3994,-662,276,-152,96,-67,49,-37), Fraction(153,250), 540, 16469, 884144),
        ((4048,-668,279,-153,97,-67,49,-38), Fraction(61485,100000), 540, 16314, 1338),
    )
    for row in rows:
        replay(*row)
    for w, C, a, slope, low in tuned_rows:
        replay(w, C, Fraction(a,1000), Fraction(slope,10000), Fraction(low,10**8))


if __name__ == "__main__":
    main()
```
