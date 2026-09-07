import RiemannResearch.RH.ArithmeticFiniteIntegerCertificate

/-!
# Fifth-level integer shear certificate

The denominator-10000 shears, shifted entry intervals, all dense congruence
intervals, and strict diagonal-dominance margins are checked by kernel reduction.
The exact margins are 7500436/10^15 and 12178181/10^15.

Source: user-provided FifthLevel_Paper_Recon_v47.md and the RH continuation
program support the certificate architecture and candidate rational data.
All identities and inequalities below are formally proved. These fixed-level
results do not establish all-level positivity, completed-Weil positivity, or RH.
-/


open scoped BigOperators
namespace RiemannResearch.RH

def fifthLevelOddShearNumerator : Matrix (Fin 16) (Fin 16) ℤ :=
  !![10000,-2496,818,-1460,111,-47,194,-738,24,2,1,-2,7,-27,98,-366;
    0,10000,-2146,-86,328,-668,-1234,677,33,-25,97,-354,-555,-38,-106,365;
    0,0,10000,2406,-2016,-1376,883,52,305,-684,-1193,225,530,63,8,1;
    0,0,0,10000,-442,1245,-893,-53,-8,24,-84,305,729,-597,-1262,634;
    0,0,0,0,10000,3217,242,15,-2171,-1462,843,100,14,2,0,0;
    0,0,0,0,0,10000,3387,199,-443,1162,-527,-1359,855,102,13,2;
    0,0,0,0,0,0,10000,2589,-34,89,-317,1158,-530,-1351,839,79;
    0,0,0,0,0,0,0,10000,-2,7,-26,96,-340,1247,-853,-81;
    0,0,0,0,0,0,0,0,10000,3507,409,49,7,1,0,0;
    0,0,0,0,0,0,0,0,0,10000,3907,465,63,8,1,0;
    0,0,0,0,0,0,0,0,0,0,10000,3931,469,56,7,1;
    0,0,0,0,0,0,0,0,0,0,0,10000,3911,465,61,9;
    0,0,0,0,0,0,0,0,0,0,0,0,10000,3925,460,46;
    0,0,0,0,0,0,0,0,0,0,0,0,0,10000,3840,357;
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,10000,2947;
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10000]

def fifthLevelOddShiftedLowerNumerator : Matrix (Fin 16) (Fin 16) ℤ :=
  !![30453883906426,7602683403310,-859914537704,4719019809934,-551771921280,122939343460,816560915966,1549071738552,-179931231936,-95961633832,-11738581666,73355857022,159941632196,248642359150,340086978858,434911436758;
    7602683403310,8200551953642,1137637399956,907155957422,-83579894462,654264250700,625507804890,-170135898118,-66624961704,24871964330,116982863260,210345739888,206752861210,106195282364,6862815892,-91900555986;
    -859914537704,1137637399956,1600720169900,-500867602966,272833954232,266856805660,-126050197262,-124569423280,19636887170,116850442922,116103631834,17394680494,-31657501748,-31379296578,-31194308256,-31101958420;
    4719019809934,907155957422,-500867602966,1485193028706,-117398166964,-133221453582,245271616172,236619585886,-28411762228,-30298319040,-32275285798,-34347697944,12903584060,109800454106,108719476572,9657844544;
    -551771921280,-83579894462,272833954232,-117398166964,230778634556,-30251969008,-29546744708,-29196312700,41841947814,41671221710,-7619730652,-7509091000,-7420989352,-7355151612,-7311373128,-7289517812;
    122939343460,654264250700,266856805660,-133221453582,-30251969008,227788287192,-33525134166,-33134600920,-7322498970,-7806322682,41111002652,40906771284,-8419513240,-8346139694,-8297351804,-8272996124;
    816560915966,625507804890,-126050197262,245271616172,-29546744708,-33525134166,224200430980,-37463422386,-7150920244,-7625220720,-8122281558,-8643371376,40234640200,39988926760,-9381136248,-9353973662;
    1549071738552,-170135898118,-124569423280,236619585886,-29196312700,-33134600920,-37463422386,219871609514,-7065659684,-7535231260,-8027282692,-8543065240,-9083904562,-9651205352,39178018332,38880786658;
    -179931231936,-66624961704,19636887170,-28411762228,41841947814,-7322498970,-7150920244,-7065659684,29040041628,-1876913386,-1844428844,-1817510902,-1796076020,-1780057732,-1769406344,-1764088876;
    -95961633832,24871964330,116850442922,-30298319040,41671221710,-7806322682,-7625220720,-7535231260,-1876913386,28954666204,-1966151360,-1937738678,-1915114168,-1898207220,-1886965112,-1881352808;
    -11738581666,116982863260,116103631834,-32275285798,-7619730652,41111002652,-8122281558,-8027282692,-1844428844,-1966151360,28861356370,-2063754626,-2039869878,-2022021548,-2010153684,-2004229044;
    73355857022,210345739888,17394680494,-34347697944,-7509091000,40906771284,-8643371376,-8543065240,-1817510902,-1937738678,-2063754626,28759225170,-2170662006,-2151816342,-2139285480,-2133029920;
    159941632196,206752861210,-31657501748,12903584060,-7420989352,-8419513240,40234640200,-9083904562,-1796076020,-1915114168,-2039869878,-2170662006,28647278706,-2287925938,-2274692578,-2268086356;
    248642359150,106195282364,-31379296578,109800454106,-7355151612,-8346139694,39988926760,-9651205352,-1780057732,-1898207220,-2022021548,-2151816342,-2287925938,28524402470,-2416726814,-2409749014;
    340086978858,6862815892,-31194308256,108719476572,-7311373128,-8297351804,-9381136248,39178018332,-1769406344,-1886965112,-2010153684,-2139285480,-2274692578,-2416726814,28389346034,-2558389472;
    434911436758,-91900555986,-31101958420,9657844544,-7289517812,-8272996124,-9353973662,38880786658,-1764088876,-1881352808,-2004229044,-2133029920,-2268086356,-2409749014,-2558389472,28240705576]

def fifthLevelOddShiftedUpperNumerator : Matrix (Fin 16) (Fin 16) ℤ :=
  !![30453883906436,7602683403320,-859914537678,4719019809958,-551771921250,122939343488,816560915994,1549071738580,-179931231906,-95961633800,-11738581634,73355857050,159941632224,248642359182,340086978890,434911436786;
    7602683403320,8200551953692,1137637399986,907155957434,-83579894404,654264250756,625507804938,-170135898070,-66624961642,24871964390,116982863320,210345739948,206752861270,106195282416,6862815944,-91900555926;
    -859914537678,1137637399986,1600720169952,-500867602904,272833954266,266856805694,-126050197216,-124569423256,19636887228,116850442978,116103631890,17394680552,-31657501686,-31379296514,-31194308200,-31101958364;
    4719019809958,907155957434,-500867602904,1485193028756,-117398166924,-133221453544,245271616202,236619585898,-28411762164,-30298318976,-32275285734,-34347697882,12903584118,109800454162,108719476620,9657844592;
    -551771921250,-83579894404,272833954266,-117398166924,230778634608,-30251968946,-29546744644,-29196312636,41841947848,41671221744,-7619730606,-7509090952,-7420989304,-7355151564,-7311373080,-7289517788;
    122939343488,654264250756,266856805694,-133221453544,-30251968946,227788287244,-33525134104,-33134600856,-7322498922,-7806322636,41111002686,40906771318,-8419513194,-8346139646,-8297351756,-8272996100;
    816560915994,625507804938,-126050197216,245271616202,-29546744644,-33525134104,224200431032,-37463422324,-7150920196,-7625220672,-8122281510,-8643371330,40234640234,39988926794,-9381136202,-9353973638;
    1549071738580,-170135898070,-124569423256,236619585898,-29196312636,-33134600856,-37463422324,219871609564,-7065659644,-7535231220,-8027282652,-8543065200,-9083904522,-9651205314,39178018362,38880786670;
    -179931231906,-66624961642,19636887228,-28411762164,41841947848,-7322498922,-7150920196,-7065659644,29040041680,-1876913324,-1844428780,-1817510838,-1796075956,-1780057668,-1769406280,-1764088812;
    -95961633800,24871964390,116850442978,-30298318976,41671221744,-7806322636,-7625220672,-7535231220,-1876913324,28954666256,-1966151298,-1937738614,-1915114104,-1898207156,-1886965048,-1881352744;
    -11738581634,116982863320,116103631890,-32275285734,-7619730606,41111002686,-8122281510,-8027282652,-1844428780,-1966151298,28861356422,-2063754564,-2039869814,-2022021484,-2010153620,-2004228980;
    73355857050,210345739948,17394680552,-34347697882,-7509090952,40906771318,-8643371330,-8543065200,-1817510838,-1937738614,-2063754564,28759225222,-2170661944,-2151816278,-2139285416,-2133029856;
    159941632224,206752861270,-31657501686,12903584118,-7420989304,-8419513194,40234640234,-9083904522,-1796075956,-1915114104,-2039869814,-2170661944,28647278758,-2287925876,-2274692514,-2268086292;
    248642359182,106195282416,-31379296514,109800454162,-7355151564,-8346139646,39988926794,-9651205314,-1780057668,-1898207156,-2022021484,-2151816278,-2287925876,28524402522,-2416726752,-2409748950;
    340086978890,6862815944,-31194308200,108719476620,-7311373080,-8297351756,-9381136202,39178018362,-1769406280,-1886965048,-2010153620,-2139285416,-2274692514,-2416726752,28389346086,-2558389410;
    434911436786,-91900555926,-31101958364,9657844592,-7289517788,-8272996100,-9353973638,38880786670,-1764088812,-1881352744,-2004228980,-2133029856,-2268086292,-2409748950,-2558389410,28240705626]

def fifthLevelOddShearedLowerNumerator : Matrix (Fin 16) (Fin 16) ℤ :=
  !![30453883906,1393980,-322693,474244,412300,284017,142884,-179132,-498315,1470702,243632,-42534,-1047413,406863,1517466,725775;
    1393980,6302574238,-221003,236620,241091,178235,37111,-45608,-151516,214246,-31817,-332386,-49949,-51067,-8125,23856;
    -322693,-221003,1286280490,-7878,-3526,27566,-62875,-21301,-32124,-63379,20638,-55706,20216,29218,-55525,-49858;
    474244,236620,-7878,667840657,12689,30356,24397,-11368,13448,35327,-26050,-27762,-7785,-20193,12383,19747;
    412300,241091,-3526,12689,172103743,4976,-10765,3257,-544,-2957,7062,-3297,4094,4397,-1807,-1366;
    284017,178235,27566,30356,4976,120452102,5953,-5189,-3271,-4313,-3871,-1083,3093,4664,-4938,-1071;
    142884,37111,-62875,24397,-10765,5953,117734932,4034,-6992,985,-791,-5462,-4635,138,-5181,4489;
    -179132,-45608,-21301,-11368,3257,-5189,4034,81734486,3483,-3365,2350,-659,3049,-3887,645,-161;
    -498315,-151516,-32124,13448,-544,-3271,-6992,3483,20273459,867,-177,193,540,-108,-455,-237;
    1470702,214246,-63379,35327,-2957,-4313,985,-3365,867,13084855,-370,216,-465,515,185,-133;
    243632,-31817,20638,-26050,7062,-3871,-791,2350,-177,-370,13041125,-610,-135,233,-207,-104;
    -42534,-332386,-55706,-27762,-3297,-1083,-5462,-659,193,216,-610,13021279,451,291,-714,3;
    -1047413,-49949,20216,-7785,4094,3093,-4635,3049,540,-465,-135,451,13043932,-210,670,-47;
    406863,-51067,29218,-20193,4397,4664,138,-3887,-108,515,233,291,-210,12992190,-619,176;
    1517466,-8125,-55525,12383,-1807,-4938,-5181,645,-455,185,-207,-714,670,-619,12697835,341;
    725775,23856,-49858,19747,-1366,-1071,4489,-161,-237,-133,-104,3,-47,176,341,8327808]

def fifthLevelOddShearedUpperNumerator : Matrix (Fin 16) (Fin 16) ℤ :=
  !![30453883907,1393981,-322692,474245,412301,284018,142885,-179131,-498314,1470703,243633,-42533,-1047412,406864,1517467,725776;
    1393981,6302574239,-221002,236621,241092,178236,37112,-45607,-151515,214247,-31816,-332385,-49948,-51065,-8124,23858;
    -322692,-221002,1286280491,-7877,-3525,27567,-62874,-21300,-32123,-63378,20639,-55705,20217,29219,-55524,-49857;
    474245,236621,-7877,667840658,12690,30357,24398,-11367,13449,35328,-26049,-27761,-7784,-20192,12384,19748;
    412301,241092,-3525,12690,172103744,4977,-10764,3258,-543,-2955,7063,-3296,4095,4398,-1806,-1365;
    284018,178236,27567,30357,4977,120452103,5955,-5188,-3270,-4312,-3870,-1081,3094,4665,-4937,-1070;
    142885,37112,-62874,24398,-10764,5955,117734933,4035,-6991,986,-789,-5461,-4634,139,-5179,4490;
    -179131,-45607,-21300,-11367,3258,-5188,4035,81734487,3484,-3364,2351,-658,3050,-3886,646,-160;
    -498314,-151515,-32123,13449,-543,-3270,-6991,3484,20273460,869,-175,194,541,-106,-454,-236;
    1470703,214247,-63378,35328,-2955,-4312,986,-3364,869,13084857,-369,218,-463,517,186,-131;
    243633,-31816,20639,-26049,7063,-3870,-789,2351,-175,-369,13041127,-609,-133,234,-206,-103;
    -42533,-332385,-55705,-27761,-3296,-1081,-5461,-658,194,218,-609,13021280,453,292,-713,4;
    -1047412,-49948,20217,-7784,4095,3094,-4634,3050,541,-463,-133,453,13043934,-209,671,-46;
    406864,-51065,29219,-20192,4398,4665,139,-3886,-106,517,234,292,-209,12992191,-618,177;
    1517467,-8124,-55524,12384,-1806,-4937,-5179,646,-454,186,-206,-713,671,-618,12697836,342;
    725776,23858,-49857,19748,-1365,-1070,4490,-160,-236,-131,-103,4,-46,177,342,8327809]

def fifthLevelEvenShearNumerator : Matrix (Fin 15) (Fin 15) ℤ :=
  !![10000,-1754,-2591,285,-716,-1078,-100,15,-27,97,-356,-548,-65,-9,-1;
    0,10000,3909,-2218,-1396,914,85,276,-686,-1193,225,530,63,9,1;
    0,0,10000,-399,1077,-257,-2525,-9,23,-83,302,742,-643,-1108,-158;
    0,0,0,10000,3202,249,23,-2280,-1466,842,100,14,2,0,0;
    0,0,0,0,10000,3508,327,-451,1162,-527,-1359,855,102,14,2;
    0,0,0,0,0,10000,4272,-34,89,-317,1157,-526,-1366,872,124;
    0,0,0,0,0,0,10000,-2,6,-22,82,-293,1070,-201,-2566;
    0,0,0,0,0,0,0,10000,3489,407,48,7,1,0,0;
    0,0,0,0,0,0,0,0,10000,3907,465,63,8,1,0;
    0,0,0,0,0,0,0,0,0,10000,3932,469,56,8,1;
    0,0,0,0,0,0,0,0,0,0,10000,3912,466,65,9;
    0,0,0,0,0,0,0,0,0,0,0,10000,3936,478,68;
    0,0,0,0,0,0,0,0,0,0,0,0,10000,3987,569;
    0,0,0,0,0,0,0,0,0,0,0,0,0,10000,4862;
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,10000]

def fifthLevelEvenShiftedLowerNumerator : Matrix (Fin 15) (Fin 15) ℤ :=
  !![15247517099788,2674226452534,2904707895074,274633005478,1064943385912,1093699831724,361189009142,19813732620,117575112394,216241299644,316466252788,320059131466,227028880542,135584260834,45089326908;
    2674226452534,1933626269628,-63092779202,350150278172,356127426744,-23694863436,-7871576818,38255717654,136897708818,137644519906,40497924330,-6919414060,-4929902088,-2952935330,-983478336;
    2904707895074,-63092779202,2049153410836,-15042833140,-16523607110,377712616238,386364646530,-3673674532,-3848924544,-4033912862,-4229217856,44989020772,143947697642,145028675178,48234760296;
    274633005478,350150278172,-15042833140,248695352388,-9478798972,-5649332148,-1876812336,46151341386,46322067490,-2611985300,-2128161588,-1649705456,-1175404980,-704062598,-234491022;
    1064943385912,356127426744,-16523607110,-9478798972,251685699752,-6205633814,-2061475924,-2314753618,-2425393270,46882286548,47086517916,-1812202712,-1291112894,-773343002,-257560454;
    1093699831724,-23694863436,377712616238,-5649332148,-6205633814,255273555964,-2267345582,-1379636348,-1445474088,-1514971030,-1588344576,47758649000,48004362440,-850579702,-283278912;
    361189009142,-7871576818,386364646530,-1876812336,-2061475924,-2267345582,259602377444,-458349156,-480204460,-503273892,-527629560,-553348018,-580510592,48815270874,49112502554;
    19813732620,38255717654,-3673674532,46151341386,-2314753618,-1379636348,-458349156,30075871436,-757588590,-637848188,-519710158,-402875696,-287050456,-171943620,-57266828;
    117575112394,136897708818,-3848924544,46322067490,-2425393270,-1445474088,-480204460,-757588590,30161246860,-668350616,-544538354,-422106892,-300744496,-180143076,-59997144;
    216241299644,137644519906,-4033912862,-2611985300,46882286548,-1514971030,-503273892,-637848188,-668350616,30254556694,-570747350,-442407154,-315199512,-188798032,-62879132;
    316466252788,40497924330,-4229217856,-2128161588,47086517916,-1588344576,-527629560,-519710158,-544538354,-570747350,30356687894,-463839970,-330460690,-197935580,-65921784;
    320059131466,-6919414060,44989020772,-1649705456,-1812202712,47758649000,-553348018,-402875696,-422106892,-442407154,-463839970,30468634358,-346576038,-207584454,-69134692;
    227028880542,-4929902088,143947697642,-1175404980,-1291112894,48004362440,-580510592,-287050456,-300744496,-315199512,-330460690,-346576038,30591510594,-217775162,-72528006;
    135584260834,-2952935330,145028675178,-704062598,-773343002,-850579702,48815270874,-171943620,-180143076,-188798032,-197935580,-207584454,-217775162,30726567030,-76112492;
    45089326908,-983478336,48234760296,-234491022,-257560454,-283278912,49112502554,-57266828,-59997144,-62879132,-65921784,-69134692,-72528006,-76112492,30875207502]

def fifthLevelEvenShiftedUpperNumerator : Matrix (Fin 15) (Fin 15) ℤ :=
  !![15247517099814,2674226452560,2904707895106,274633005520,1064943385952,1093699831768,361189009178,19813732666,117575112438,216241299688,316466252832,320059131510,227028880590,135584260882,45089326944;
    2674226452560,1933626269680,-63092779164,350150278206,356127426778,-23694863394,-7871576774,38255717712,136897708874,137644519962,40497924388,-6919413998,-4929902028,-2952935270,-983478288;
    2904707895106,-63092779164,2049153410862,-15042833100,-16523607072,377712616264,386364646562,-3673674484,-3848924496,-4033912814,-4229217810,44989020814,143947697682,145028675222,48234760332;
    274633005520,350150278206,-15042833100,248695352440,-9478798910,-5649332084,-1876812296,46151341420,46322067524,-2611985254,-2128161540,-1649705408,-1175404932,-704062554,-234490978;
    1064943385952,356127426778,-16523607072,-9478798910,251685699804,-6205633752,-2061475884,-2314753570,-2425393224,46882286582,47086517950,-1812202666,-1291112846,-773342958,-257560410;
    1093699831768,-23694863394,377712616264,-5649332084,-6205633752,255273556016,-2267345544,-1379636300,-1445474040,-1514970982,-1588344530,47758649034,48004362474,-850579660,-283278868;
    361189009178,-7871576774,386364646562,-1876812296,-2061475884,-2267345544,259602377470,-458349116,-480204420,-503273852,-527629520,-553347978,-580510554,48815270900,49112502586;
    19813732666,38255717712,-3673674484,46151341420,-2314753570,-1379636300,-458349116,30075871488,-757588528,-637848124,-519710094,-402875632,-287050392,-171943556,-57266788;
    117575112438,136897708874,-3848924496,46322067524,-2425393224,-1445474040,-480204420,-757588528,30161246912,-668350554,-544538290,-422106828,-300744432,-180143012,-59997104;
    216241299688,137644519962,-4033912814,-2611985254,46882286582,-1514970982,-503273852,-637848124,-668350554,30254556746,-570747288,-442407090,-315199448,-188797968,-62879092;
    316466252832,40497924388,-4229217810,-2128161540,47086517950,-1588344530,-527629520,-519710094,-544538290,-570747288,30356687946,-463839908,-330460626,-197935516,-65921744;
    320059131510,-6919413998,44989020814,-1649705408,-1812202666,47758649034,-553347978,-402875632,-422106828,-442407090,-463839908,30468634410,-346575976,-207584390,-69134652;
    227028880590,-4929902028,143947697682,-1175404932,-1291112846,48004362474,-580510554,-287050392,-300744432,-315199448,-330460626,-346575976,30591510646,-217775100,-72527966;
    135584260882,-2952935270,145028675222,-704062554,-773342958,-850579660,48815270900,-171943556,-180143012,-188797968,-197935516,-207584390,-217775100,30726567082,-76112454;
    45089326944,-983478288,48234760332,-234490978,-257560410,-283278868,49112502586,-57266788,-59997104,-62879092,-65921744,-69134652,-72527966,-76112454,30875207528]

def fifthLevelEvenShearedLowerNumerator : Matrix (Fin 15) (Fin 15) ℤ :=
  !![15247517099,-188047,-568666,145970,673677,211294,689892,-556668,-15415,-722379,-341311,-217874,189698,85333,353236;
    -188047,1464599933,-30601,-20776,-76551,-10368,-39832,-23909,69914,79402,-74544,-24458,37928,37583,-38443;
    -568666,-30601,1271977017,-61835,25883,-60178,6932,7993,-23200,-43172,45845,53769,-53786,-31314,23469;
    145970,-20776,-61835,179463393,-8741,3651,-4388,148,3060,1524,-6747,7990,6075,-4337,-1581;
    673677,-76551,25883,-8741,120867812,3864,1542,933,-6528,-2604,649,-526,4390,-1327,2384;
    211294,-10368,-60178,3651,3864,123170568,3871,3630,2450,-5673,-5125,-40,-7692,1889,-7444;
    689892,-39832,6932,-4388,1542,3871,157307682,6755,-4579,6305,2068,-2775,5043,1302,6129;
    -556668,-23909,7993,148,933,3630,6755,20752613,375,790,-795,978,100,-180,46;
    -15415,69914,-23200,3060,-6528,2450,-4579,375,13087542,1,-194,-326,559,-132,-168;
    -722379,79402,-43172,1524,-2604,-5673,6305,790,1,13041241,619,-314,72,121,-73;
    -341311,-74544,45845,-6747,649,-5125,2068,-795,-194,619,13021616,609,271,524,-188;
    -217874,-24458,53769,7990,-526,-40,-2775,978,-326,-314,609,13047747,-201,67,-246;
    189698,37928,-53786,6075,4390,-7692,5043,100,559,72,271,-201,13045740,-497,-184;
    85333,37583,-31314,-4337,-1327,1889,1302,-180,-132,121,524,67,-497,13380702,-487;
    353236,-38443,23469,-1581,2384,-7444,6129,46,-168,-73,-188,-246,-184,-487,17456986]

def fifthLevelEvenShearedUpperNumerator : Matrix (Fin 15) (Fin 15) ℤ :=
  !![15247517100,-188046,-568665,145971,673678,211295,689893,-556667,-15414,-722378,-341310,-217873,189699,85334,353237;
    -188046,1464599934,-30600,-20775,-76550,-10367,-39831,-23908,69915,79404,-74543,-24457,37929,37584,-38442;
    -568665,-30600,1271977018,-61834,25884,-60177,6933,7994,-23199,-43171,45847,53770,-53785,-31312,23470;
    145971,-20775,-61834,179463394,-8740,3653,-4387,149,3061,1525,-6746,7992,6076,-4336,-1580;
    673678,-76550,25884,-8740,120867813,3865,1543,934,-6526,-2603,650,-525,4391,-1326,2386;
    211295,-10367,-60177,3653,3865,123170570,3872,3631,2451,-5672,-5124,-39,-7691,1890,-7443;
    689893,-39831,6933,-4387,1543,3872,157307683,6756,-4578,6306,2069,-2774,5044,1303,6131;
    -556667,-23908,7994,149,934,3631,6756,20752614,376,791,-794,979,101,-179,47;
    -15414,69915,-23199,3061,-6526,2451,-4578,376,13087543,3,-193,-325,560,-131,-167;
    -722378,79404,-43171,1525,-2603,-5672,6306,791,3,13041242,620,-312,74,122,-72;
    -341310,-74543,45847,-6746,650,-5124,2069,-794,-193,620,13021617,610,272,525,-187;
    -217873,-24457,53770,7992,-525,-39,-2774,979,-325,-312,610,13047748,-200,68,-245;
    189699,37929,-53785,6076,4391,-7691,5044,101,560,74,272,-200,13045741,-496,-183;
    85334,37584,-31312,-4336,-1326,1890,1303,-179,-131,122,525,68,-496,13380703,-486;
    353237,-38442,23470,-1580,2386,-7443,6131,47,-167,-72,-187,-245,-183,-486,17456987]

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

theorem fifthLevelOddIntegerIntervals_row0 (j : Fin 16) (hij : (0:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 0 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 0 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 0 j ≤
      fifthLevelOddShearedUpperNumerator 0 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row1 (j : Fin 16) (hij : (1:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 1 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 1 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 1 j ≤
      fifthLevelOddShearedUpperNumerator 1 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row2 (j : Fin 16) (hij : (2:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 2 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 2 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 2 j ≤
      fifthLevelOddShearedUpperNumerator 2 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row3 (j : Fin 16) (hij : (3:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 3 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 3 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 3 j ≤
      fifthLevelOddShearedUpperNumerator 3 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row4 (j : Fin 16) (hij : (4:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 4 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 4 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 4 j ≤
      fifthLevelOddShearedUpperNumerator 4 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row5 (j : Fin 16) (hij : (5:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 5 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 5 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 5 j ≤
      fifthLevelOddShearedUpperNumerator 5 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row6 (j : Fin 16) (hij : (6:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 6 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 6 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 6 j ≤
      fifthLevelOddShearedUpperNumerator 6 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row7 (j : Fin 16) (hij : (7:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 7 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 7 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 7 j ≤
      fifthLevelOddShearedUpperNumerator 7 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row8 (j : Fin 16) (hij : (8:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 8 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 8 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 8 j ≤
      fifthLevelOddShearedUpperNumerator 8 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row9 (j : Fin 16) (hij : (9:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 9 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 9 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 9 j ≤
      fifthLevelOddShearedUpperNumerator 9 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row10 (j : Fin 16) (hij : (10:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 10 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 10 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 10 j ≤
      fifthLevelOddShearedUpperNumerator 10 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row11 (j : Fin 16) (hij : (11:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 11 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 11 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 11 j ≤
      fifthLevelOddShearedUpperNumerator 11 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row12 (j : Fin 16) (hij : (12:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 12 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 12 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 12 j ≤
      fifthLevelOddShearedUpperNumerator 12 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row13 (j : Fin 16) (hij : (13:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 13 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 13 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 13 j ≤
      fifthLevelOddShearedUpperNumerator 13 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row14 (j : Fin 16) (hij : (14:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 14 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 14 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 14 j ≤
      fifthLevelOddShearedUpperNumerator 14 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddIntegerIntervals_row15 (j : Fin 16) (hij : (15:Fin 16) ≤ j) :
    fifthLevelOddShearedLowerNumerator 15 j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 15 j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator 15 j ≤
      fifthLevelOddShearedUpperNumerator 15 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelOddShiftedNumerator_symm (i j : Fin 16) :
    fifthLevelOddShiftedLowerNumerator i j = fifthLevelOddShiftedLowerNumerator j i ∧
    fifthLevelOddShiftedUpperNumerator i j = fifthLevelOddShiftedUpperNumerator j i := by
  fin_cases i <;> fin_cases j <;> constructor <;> rfl

theorem fifthLevelOddShearedNumerator_symm (i j : Fin 16) :
    fifthLevelOddShearedLowerNumerator i j = fifthLevelOddShearedLowerNumerator j i ∧
    fifthLevelOddShearedUpperNumerator i j = fifthLevelOddShearedUpperNumerator j i := by
  fin_cases i <;> fin_cases j <;> constructor <;> rfl

theorem fifthLevelOddIntegerIntervals (i j : Fin 16) :
    fifthLevelOddShearedLowerNumerator i j * 100000000000 ≤
      integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator i j ∧
    integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
        fifthLevelOddShiftedUpperNumerator i j ≤
      fifthLevelOddShearedUpperNumerator i j * 100000000000 := by
  have hu (a b : Fin 16) (hab : a ≤ b) :
      fifthLevelOddShearedLowerNumerator a b * 100000000000 ≤
        integerCongruenceLower fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
          fifthLevelOddShiftedUpperNumerator a b ∧
      integerCongruenceUpper fifthLevelOddShearNumerator fifthLevelOddShiftedLowerNumerator
          fifthLevelOddShiftedUpperNumerator a b ≤
        fifthLevelOddShearedUpperNumerator a b * 100000000000 := by
    fin_cases a
    · exact fifthLevelOddIntegerIntervals_row0 b hab
    · exact fifthLevelOddIntegerIntervals_row1 b hab
    · exact fifthLevelOddIntegerIntervals_row2 b hab
    · exact fifthLevelOddIntegerIntervals_row3 b hab
    · exact fifthLevelOddIntegerIntervals_row4 b hab
    · exact fifthLevelOddIntegerIntervals_row5 b hab
    · exact fifthLevelOddIntegerIntervals_row6 b hab
    · exact fifthLevelOddIntegerIntervals_row7 b hab
    · exact fifthLevelOddIntegerIntervals_row8 b hab
    · exact fifthLevelOddIntegerIntervals_row9 b hab
    · exact fifthLevelOddIntegerIntervals_row10 b hab
    · exact fifthLevelOddIntegerIntervals_row11 b hab
    · exact fifthLevelOddIntegerIntervals_row12 b hab
    · exact fifthLevelOddIntegerIntervals_row13 b hab
    · exact fifthLevelOddIntegerIntervals_row14 b hab
    · exact fifthLevelOddIntegerIntervals_row15 b hab
  rcases le_total i j with hij | hji
  · exact hu i j hij
  · have hs := integerCongruence_symm fifthLevelOddShearNumerator
      fifthLevelOddShiftedLowerNumerator fifthLevelOddShiftedUpperNumerator
      (fun a b => (fifthLevelOddShiftedNumerator_symm a b).1)
      (fun a b => (fifthLevelOddShiftedNumerator_symm a b).2) i j
    rw [(fifthLevelOddShearedNumerator_symm i j).1,
      (fifthLevelOddShearedNumerator_symm i j).2, hs.1, hs.2]
    exact hu j i hji

theorem fifthLevelOddShearNumerator_unitUpper :
    (∀ i j : Fin 16, j < i → fifthLevelOddShearNumerator i j = 0) ∧
      (∀ i : Fin 16, fifthLevelOddShearNumerator i i = 10000) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i
    fin_cases i <;> rfl

theorem fifthLevelOddIntegerMargin (i : Fin 16) :
    (∑ j ∈ Finset.univ.erase i, max |fifthLevelOddShearedLowerNumerator i j|
      |fifthLevelOddShearedUpperNumerator i j|) + 7500436 ≤
        fifthLevelOddShearedLowerNumerator i i := by
  revert i
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row0 (j : Fin 15) (hij : (0:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 0 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 0 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 0 j ≤
      fifthLevelEvenShearedUpperNumerator 0 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row1 (j : Fin 15) (hij : (1:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 1 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 1 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 1 j ≤
      fifthLevelEvenShearedUpperNumerator 1 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row2 (j : Fin 15) (hij : (2:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 2 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 2 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 2 j ≤
      fifthLevelEvenShearedUpperNumerator 2 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row3 (j : Fin 15) (hij : (3:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 3 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 3 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 3 j ≤
      fifthLevelEvenShearedUpperNumerator 3 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row4 (j : Fin 15) (hij : (4:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 4 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 4 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 4 j ≤
      fifthLevelEvenShearedUpperNumerator 4 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row5 (j : Fin 15) (hij : (5:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 5 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 5 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 5 j ≤
      fifthLevelEvenShearedUpperNumerator 5 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row6 (j : Fin 15) (hij : (6:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 6 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 6 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 6 j ≤
      fifthLevelEvenShearedUpperNumerator 6 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row7 (j : Fin 15) (hij : (7:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 7 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 7 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 7 j ≤
      fifthLevelEvenShearedUpperNumerator 7 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row8 (j : Fin 15) (hij : (8:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 8 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 8 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 8 j ≤
      fifthLevelEvenShearedUpperNumerator 8 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row9 (j : Fin 15) (hij : (9:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 9 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 9 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 9 j ≤
      fifthLevelEvenShearedUpperNumerator 9 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row10 (j : Fin 15) (hij : (10:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 10 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 10 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 10 j ≤
      fifthLevelEvenShearedUpperNumerator 10 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row11 (j : Fin 15) (hij : (11:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 11 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 11 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 11 j ≤
      fifthLevelEvenShearedUpperNumerator 11 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row12 (j : Fin 15) (hij : (12:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 12 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 12 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 12 j ≤
      fifthLevelEvenShearedUpperNumerator 12 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row13 (j : Fin 15) (hij : (13:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 13 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 13 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 13 j ≤
      fifthLevelEvenShearedUpperNumerator 13 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenIntegerIntervals_row14 (j : Fin 15) (hij : (14:Fin 15) ≤ j) :
    fifthLevelEvenShearedLowerNumerator 14 j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 14 j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator 14 j ≤
      fifthLevelEvenShearedUpperNumerator 14 j * 100000000000 := by
  revert j
  decide +kernel

theorem fifthLevelEvenShiftedNumerator_symm (i j : Fin 15) :
    fifthLevelEvenShiftedLowerNumerator i j = fifthLevelEvenShiftedLowerNumerator j i ∧
    fifthLevelEvenShiftedUpperNumerator i j = fifthLevelEvenShiftedUpperNumerator j i := by
  fin_cases i <;> fin_cases j <;> constructor <;> rfl

theorem fifthLevelEvenShearedNumerator_symm (i j : Fin 15) :
    fifthLevelEvenShearedLowerNumerator i j = fifthLevelEvenShearedLowerNumerator j i ∧
    fifthLevelEvenShearedUpperNumerator i j = fifthLevelEvenShearedUpperNumerator j i := by
  fin_cases i <;> fin_cases j <;> constructor <;> rfl

theorem fifthLevelEvenIntegerIntervals (i j : Fin 15) :
    fifthLevelEvenShearedLowerNumerator i j * 100000000000 ≤
      integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator i j ∧
    integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
        fifthLevelEvenShiftedUpperNumerator i j ≤
      fifthLevelEvenShearedUpperNumerator i j * 100000000000 := by
  have hu (a b : Fin 15) (hab : a ≤ b) :
      fifthLevelEvenShearedLowerNumerator a b * 100000000000 ≤
        integerCongruenceLower fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
          fifthLevelEvenShiftedUpperNumerator a b ∧
      integerCongruenceUpper fifthLevelEvenShearNumerator fifthLevelEvenShiftedLowerNumerator
          fifthLevelEvenShiftedUpperNumerator a b ≤
        fifthLevelEvenShearedUpperNumerator a b * 100000000000 := by
    fin_cases a
    · exact fifthLevelEvenIntegerIntervals_row0 b hab
    · exact fifthLevelEvenIntegerIntervals_row1 b hab
    · exact fifthLevelEvenIntegerIntervals_row2 b hab
    · exact fifthLevelEvenIntegerIntervals_row3 b hab
    · exact fifthLevelEvenIntegerIntervals_row4 b hab
    · exact fifthLevelEvenIntegerIntervals_row5 b hab
    · exact fifthLevelEvenIntegerIntervals_row6 b hab
    · exact fifthLevelEvenIntegerIntervals_row7 b hab
    · exact fifthLevelEvenIntegerIntervals_row8 b hab
    · exact fifthLevelEvenIntegerIntervals_row9 b hab
    · exact fifthLevelEvenIntegerIntervals_row10 b hab
    · exact fifthLevelEvenIntegerIntervals_row11 b hab
    · exact fifthLevelEvenIntegerIntervals_row12 b hab
    · exact fifthLevelEvenIntegerIntervals_row13 b hab
    · exact fifthLevelEvenIntegerIntervals_row14 b hab
  rcases le_total i j with hij | hji
  · exact hu i j hij
  · have hs := integerCongruence_symm fifthLevelEvenShearNumerator
      fifthLevelEvenShiftedLowerNumerator fifthLevelEvenShiftedUpperNumerator
      (fun a b => (fifthLevelEvenShiftedNumerator_symm a b).1)
      (fun a b => (fifthLevelEvenShiftedNumerator_symm a b).2) i j
    rw [(fifthLevelEvenShearedNumerator_symm i j).1,
      (fifthLevelEvenShearedNumerator_symm i j).2, hs.1, hs.2]
    exact hu j i hji

theorem fifthLevelEvenShearNumerator_unitUpper :
    (∀ i j : Fin 15, j < i → fifthLevelEvenShearNumerator i j = 0) ∧
      (∀ i : Fin 15, fifthLevelEvenShearNumerator i i = 10000) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i
    fin_cases i <;> rfl

theorem fifthLevelEvenIntegerMargin (i : Fin 15) :
    (∑ j ∈ Finset.univ.erase i, max |fifthLevelEvenShearedLowerNumerator i j|
      |fifthLevelEvenShearedUpperNumerator i j|) + 12178181 ≤
        fifthLevelEvenShearedLowerNumerator i i := by
  revert i
  decide +kernel

end RiemannResearch.RH
