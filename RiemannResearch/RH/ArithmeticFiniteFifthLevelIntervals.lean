import RiemannResearch.RH.ArithmeticFiniteFifthLevelStructure

/-!
# Exact fifth-level unsheared reflection intervals

Sparse upper-triangle checks and symmetry prove all entries of both native
reflection blocks from the 33 proved primitive intervals.

Source: user-provided FifthLevel_Paper_Recon_v47.md and the RH continuation
program support the certificate architecture and candidate rational data.
All identities and inequalities below are formally proved. These fixed-level
results do not establish all-level positivity, completed-Weil positivity, or RH.
-/

open scoped BigOperators
namespace RiemannResearch.RH
noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

def fifthLevelOddLower : Matrix (Fin 16) (Fin 16) ℚ :=
  fun i j => (!![30454883906426,7602683403310,-859914537704,4719019809934,-551771921280,122939343460,816560915966,1549071738552,-179931231936,-95961633832,-11738581666,73355857022,159941632196,248642359150,340086978858,434911436758;
    7602683403310,8202551953642,1137637399956,907155957422,-83579894462,654264250700,625507804890,-170135898118,-66624961704,24871964330,116982863260,210345739888,206752861210,106195282364,6862815892,-91900555986;
    -859914537704,1137637399956,1602720169900,-500867602966,272833954232,266856805660,-126050197262,-124569423280,19636887170,116850442922,116103631834,17394680494,-31657501748,-31379296578,-31194308256,-31101958420;
    4719019809934,907155957422,-500867602966,1487193028706,-117398166964,-133221453582,245271616172,236619585886,-28411762228,-30298319040,-32275285798,-34347697944,12903584060,109800454106,108719476572,9657844544;
    -551771921280,-83579894462,272833954232,-117398166964,232778634556,-30251969008,-29546744708,-29196312700,41841947814,41671221710,-7619730652,-7509091000,-7420989352,-7355151612,-7311373128,-7289517812;
    122939343460,654264250700,266856805660,-133221453582,-30251969008,229788287192,-33525134166,-33134600920,-7322498970,-7806322682,41111002652,40906771284,-8419513240,-8346139694,-8297351804,-8272996124;
    816560915966,625507804890,-126050197262,245271616172,-29546744708,-33525134166,226200430980,-37463422386,-7150920244,-7625220720,-8122281558,-8643371376,40234640200,39988926760,-9381136248,-9353973662;
    1549071738552,-170135898118,-124569423280,236619585886,-29196312700,-33134600920,-37463422386,221871609514,-7065659684,-7535231260,-8027282692,-8543065240,-9083904562,-9651205352,39178018332,38880786658;
    -179931231936,-66624961704,19636887170,-28411762228,41841947814,-7322498970,-7150920244,-7065659684,31040041628,-1876913386,-1844428844,-1817510902,-1796076020,-1780057732,-1769406344,-1764088876;
    -95961633832,24871964330,116850442922,-30298319040,41671221710,-7806322682,-7625220720,-7535231260,-1876913386,30954666204,-1966151360,-1937738678,-1915114168,-1898207220,-1886965112,-1881352808;
    -11738581666,116982863260,116103631834,-32275285798,-7619730652,41111002652,-8122281558,-8027282692,-1844428844,-1966151360,30861356370,-2063754626,-2039869878,-2022021548,-2010153684,-2004229044;
    73355857022,210345739888,17394680494,-34347697944,-7509091000,40906771284,-8643371376,-8543065240,-1817510902,-1937738678,-2063754626,30759225170,-2170662006,-2151816342,-2139285480,-2133029920;
    159941632196,206752861210,-31657501748,12903584060,-7420989352,-8419513240,40234640200,-9083904562,-1796076020,-1915114168,-2039869878,-2170662006,30647278706,-2287925938,-2274692578,-2268086356;
    248642359150,106195282364,-31379296578,109800454106,-7355151612,-8346139694,39988926760,-9651205352,-1780057732,-1898207220,-2022021548,-2151816342,-2287925938,30524402470,-2416726814,-2409749014;
    340086978858,6862815892,-31194308256,108719476572,-7311373128,-8297351804,-9381136248,39178018332,-1769406344,-1886965112,-2010153684,-2139285480,-2274692578,-2416726814,30389346034,-2558389472;
    434911436758,-91900555986,-31101958420,9657844544,-7289517812,-8272996124,-9353973662,38880786658,-1764088876,-1881352808,-2004229044,-2133029920,-2268086356,-2409749014,-2558389472,30240705576] : Matrix (Fin 16) (Fin 16) ℚ) i j / 1000000000000000000

def fifthLevelOddUpper : Matrix (Fin 16) (Fin 16) ℚ :=
  fun i j => (!![30454883906436,7602683403320,-859914537678,4719019809958,-551771921250,122939343488,816560915994,1549071738580,-179931231906,-95961633800,-11738581634,73355857050,159941632224,248642359182,340086978890,434911436786;
    7602683403320,8202551953692,1137637399986,907155957434,-83579894404,654264250756,625507804938,-170135898070,-66624961642,24871964390,116982863320,210345739948,206752861270,106195282416,6862815944,-91900555926;
    -859914537678,1137637399986,1602720169952,-500867602904,272833954266,266856805694,-126050197216,-124569423256,19636887228,116850442978,116103631890,17394680552,-31657501686,-31379296514,-31194308200,-31101958364;
    4719019809958,907155957434,-500867602904,1487193028756,-117398166924,-133221453544,245271616202,236619585898,-28411762164,-30298318976,-32275285734,-34347697882,12903584118,109800454162,108719476620,9657844592;
    -551771921250,-83579894404,272833954266,-117398166924,232778634608,-30251968946,-29546744644,-29196312636,41841947848,41671221744,-7619730606,-7509090952,-7420989304,-7355151564,-7311373080,-7289517788;
    122939343488,654264250756,266856805694,-133221453544,-30251968946,229788287244,-33525134104,-33134600856,-7322498922,-7806322636,41111002686,40906771318,-8419513194,-8346139646,-8297351756,-8272996100;
    816560915994,625507804938,-126050197216,245271616202,-29546744644,-33525134104,226200431032,-37463422324,-7150920196,-7625220672,-8122281510,-8643371330,40234640234,39988926794,-9381136202,-9353973638;
    1549071738580,-170135898070,-124569423256,236619585898,-29196312636,-33134600856,-37463422324,221871609564,-7065659644,-7535231220,-8027282652,-8543065200,-9083904522,-9651205314,39178018362,38880786670;
    -179931231906,-66624961642,19636887228,-28411762164,41841947848,-7322498922,-7150920196,-7065659644,31040041680,-1876913324,-1844428780,-1817510838,-1796075956,-1780057668,-1769406280,-1764088812;
    -95961633800,24871964390,116850442978,-30298318976,41671221744,-7806322636,-7625220672,-7535231220,-1876913324,30954666256,-1966151298,-1937738614,-1915114104,-1898207156,-1886965048,-1881352744;
    -11738581634,116982863320,116103631890,-32275285734,-7619730606,41111002686,-8122281510,-8027282652,-1844428780,-1966151298,30861356422,-2063754564,-2039869814,-2022021484,-2010153620,-2004228980;
    73355857050,210345739948,17394680552,-34347697882,-7509090952,40906771318,-8643371330,-8543065200,-1817510838,-1937738614,-2063754564,30759225222,-2170661944,-2151816278,-2139285416,-2133029856;
    159941632224,206752861270,-31657501686,12903584118,-7420989304,-8419513194,40234640234,-9083904522,-1796075956,-1915114104,-2039869814,-2170661944,30647278758,-2287925876,-2274692514,-2268086292;
    248642359182,106195282416,-31379296514,109800454162,-7355151564,-8346139646,39988926794,-9651205314,-1780057668,-1898207156,-2022021484,-2151816278,-2287925876,30524402522,-2416726752,-2409748950;
    340086978890,6862815944,-31194308200,108719476620,-7311373080,-8297351756,-9381136202,39178018362,-1769406280,-1886965048,-2010153620,-2139285416,-2274692514,-2416726752,30389346086,-2558389410;
    434911436786,-91900555926,-31101958364,9657844592,-7289517788,-8272996100,-9353973638,38880786670,-1764088812,-1881352744,-2004228980,-2133029856,-2268086292,-2409748950,-2558389410,30240705626] : Matrix (Fin 16) (Fin 16) ℚ) i j / 1000000000000000000

def fifthLevelEvenLower : Matrix (Fin 15) (Fin 15) ℚ :=
  fun i j => (!![15249517099788,2674226452534,2904707895074,274633005478,1064943385912,1093699831724,361189009142,19813732620,117575112394,216241299644,316466252788,320059131466,227028880542,135584260834,45089326908;
    2674226452534,1935626269628,-63092779202,350150278172,356127426744,-23694863436,-7871576818,38255717654,136897708818,137644519906,40497924330,-6919414060,-4929902088,-2952935330,-983478336;
    2904707895074,-63092779202,2051153410836,-15042833140,-16523607110,377712616238,386364646530,-3673674532,-3848924544,-4033912862,-4229217856,44989020772,143947697642,145028675178,48234760296;
    274633005478,350150278172,-15042833140,250695352388,-9478798972,-5649332148,-1876812336,46151341386,46322067490,-2611985300,-2128161588,-1649705456,-1175404980,-704062598,-234491022;
    1064943385912,356127426744,-16523607110,-9478798972,253685699752,-6205633814,-2061475924,-2314753618,-2425393270,46882286548,47086517916,-1812202712,-1291112894,-773343002,-257560454;
    1093699831724,-23694863436,377712616238,-5649332148,-6205633814,257273555964,-2267345582,-1379636348,-1445474088,-1514971030,-1588344576,47758649000,48004362440,-850579702,-283278912;
    361189009142,-7871576818,386364646530,-1876812336,-2061475924,-2267345582,261602377444,-458349156,-480204460,-503273892,-527629560,-553348018,-580510592,48815270874,49112502554;
    19813732620,38255717654,-3673674532,46151341386,-2314753618,-1379636348,-458349156,32075871436,-757588590,-637848188,-519710158,-402875696,-287050456,-171943620,-57266828;
    117575112394,136897708818,-3848924544,46322067490,-2425393270,-1445474088,-480204460,-757588590,32161246860,-668350616,-544538354,-422106892,-300744496,-180143076,-59997144;
    216241299644,137644519906,-4033912862,-2611985300,46882286548,-1514971030,-503273892,-637848188,-668350616,32254556694,-570747350,-442407154,-315199512,-188798032,-62879132;
    316466252788,40497924330,-4229217856,-2128161588,47086517916,-1588344576,-527629560,-519710158,-544538354,-570747350,32356687894,-463839970,-330460690,-197935580,-65921784;
    320059131466,-6919414060,44989020772,-1649705456,-1812202712,47758649000,-553348018,-402875696,-422106892,-442407154,-463839970,32468634358,-346576038,-207584454,-69134692;
    227028880542,-4929902088,143947697642,-1175404980,-1291112894,48004362440,-580510592,-287050456,-300744496,-315199512,-330460690,-346576038,32591510594,-217775162,-72528006;
    135584260834,-2952935330,145028675178,-704062598,-773343002,-850579702,48815270874,-171943620,-180143076,-188798032,-197935580,-207584454,-217775162,32726567030,-76112492;
    45089326908,-983478336,48234760296,-234491022,-257560454,-283278912,49112502554,-57266828,-59997144,-62879132,-65921784,-69134692,-72528006,-76112492,32875207502] : Matrix (Fin 15) (Fin 15) ℚ) i j / 1000000000000000000

def fifthLevelEvenUpper : Matrix (Fin 15) (Fin 15) ℚ :=
  fun i j => (!![15249517099814,2674226452560,2904707895106,274633005520,1064943385952,1093699831768,361189009178,19813732666,117575112438,216241299688,316466252832,320059131510,227028880590,135584260882,45089326944;
    2674226452560,1935626269680,-63092779164,350150278206,356127426778,-23694863394,-7871576774,38255717712,136897708874,137644519962,40497924388,-6919413998,-4929902028,-2952935270,-983478288;
    2904707895106,-63092779164,2051153410862,-15042833100,-16523607072,377712616264,386364646562,-3673674484,-3848924496,-4033912814,-4229217810,44989020814,143947697682,145028675222,48234760332;
    274633005520,350150278206,-15042833100,250695352440,-9478798910,-5649332084,-1876812296,46151341420,46322067524,-2611985254,-2128161540,-1649705408,-1175404932,-704062554,-234490978;
    1064943385952,356127426778,-16523607072,-9478798910,253685699804,-6205633752,-2061475884,-2314753570,-2425393224,46882286582,47086517950,-1812202666,-1291112846,-773342958,-257560410;
    1093699831768,-23694863394,377712616264,-5649332084,-6205633752,257273556016,-2267345544,-1379636300,-1445474040,-1514970982,-1588344530,47758649034,48004362474,-850579660,-283278868;
    361189009178,-7871576774,386364646562,-1876812296,-2061475884,-2267345544,261602377470,-458349116,-480204420,-503273852,-527629520,-553347978,-580510554,48815270900,49112502586;
    19813732666,38255717712,-3673674484,46151341420,-2314753570,-1379636300,-458349116,32075871488,-757588528,-637848124,-519710094,-402875632,-287050392,-171943556,-57266788;
    117575112438,136897708874,-3848924496,46322067524,-2425393224,-1445474040,-480204420,-757588528,32161246912,-668350554,-544538290,-422106828,-300744432,-180143012,-59997104;
    216241299688,137644519962,-4033912814,-2611985254,46882286582,-1514970982,-503273852,-637848124,-668350554,32254556746,-570747288,-442407090,-315199448,-188797968,-62879092;
    316466252832,40497924388,-4229217810,-2128161540,47086517950,-1588344530,-527629520,-519710094,-544538290,-570747288,32356687946,-463839908,-330460626,-197935516,-65921744;
    320059131510,-6919413998,44989020814,-1649705408,-1812202666,47758649034,-553347978,-402875632,-422106828,-442407090,-463839908,32468634410,-346575976,-207584390,-69134652;
    227028880590,-4929902028,143947697682,-1175404932,-1291112846,48004362474,-580510554,-287050392,-300744432,-315199448,-330460626,-346575976,32591510646,-217775100,-72527966;
    135584260882,-2952935270,145028675222,-704062554,-773342958,-850579660,48815270900,-171943556,-180143012,-188797968,-197935516,-207584390,-217775100,32726567082,-76112454;
    45089326944,-983478288,48234760332,-234490978,-257560410,-283278868,49112502586,-57266788,-59997104,-62879092,-65921744,-69134652,-72527966,-76112454,32875207528] : Matrix (Fin 15) (Fin 15) ℚ) i j / 1000000000000000000

structure FifthLevelIntervalHypotheses (p : Fin 33 → ℝ) : Prop where
  h0 : (0/1000000000000000000 : ℝ) ≤ p 0 ∧ p 0 ≤ (0/1000000000000000000 : ℝ)
  h1 : (-2029566407/1000000000000000000 : ℝ) ≤ p 1 ∧ p 1 ≤ (-2029566406/1000000000000000000 : ℝ)
  h2 : (-16007754766/1000000000000000000 : ℝ) ≤ p ⟨2,by decide⟩ ∧ p ⟨2,by decide⟩ ≤ (-16007754765/1000000000000000000 : ℝ)
  h3 : (-53263038971/1000000000000000000 : ℝ) ≤ p ⟨3,by decide⟩ ∧ p ⟨3,by decide⟩ ≤ (-53263038970/1000000000000000000 : ℝ)
  h4 : (-124465267437/1000000000000000000 : ℝ) ≤ p ⟨4,by decide⟩ ∧ p ⟨4,by decide⟩ ≤ (-124465267436/1000000000000000000 : ℝ)
  h5 : (-239644921451/1000000000000000000 : ℝ) ≤ p ⟨5,by decide⟩ ∧ p ⟨5,by decide⟩ ≤ (-239644921450/1000000000000000000 : ℝ)
  h6 : (-408211913058/1000000000000000000 : ℝ) ≤ p ⟨6,by decide⟩ ∧ p ⟨6,by decide⟩ ≤ (-408211913057/1000000000000000000 : ℝ)
  h7 : (-638973934981/1000000000000000000 : ℝ) ≤ p ⟨7,by decide⟩ ∧ p ⟨7,by decide⟩ ≤ (-638973934980/1000000000000000000 : ℝ)
  h8 : (-940154374694/1000000000000000000 : ℝ) ≤ p ⟨8,by decide⟩ ∧ p ⟨8,by decide⟩ ≤ (-940154374693/1000000000000000000 : ℝ)
  h9 : (-1319409804407/1000000000000000000 : ℝ) ≤ p ⟨9,by decide⟩ ∧ p ⟨9,by decide⟩ ≤ (-1319409804406/1000000000000000000 : ℝ)
  h10 : (-1783847058417/1000000000000000000 : ℝ) ≤ p ⟨10,by decide⟩ ∧ p ⟨10,by decide⟩ ≤ (-1783847058416/1000000000000000000 : ℝ)
  h11 : (-2340039908925/1000000000000000000 : ℝ) ≤ p ⟨11,by decide⟩ ∧ p ⟨11,by decide⟩ ≤ (-2340039908924/1000000000000000000 : ℝ)
  h12 : (-2994045351101/1000000000000000000 : ℝ) ≤ p ⟨12,by decide⟩ ∧ p ⟨12,by decide⟩ ≤ (-2994045351100/1000000000000000000 : ℝ)
  h13 : (-3751419507908/1000000000000000000 : ℝ) ≤ p ⟨13,by decide⟩ ∧ p ⟨13,by decide⟩ ≤ (-3751419507907/1000000000000000000 : ℝ)
  h14 : (-4617233164834/1000000000000000000 : ℝ) ≤ p ⟨14,by decide⟩ ∧ p ⟨14,by decide⟩ ≤ (-4617233164833/1000000000000000000 : ℝ)
  h15 : (-5596086944461/1000000000000000000 : ℝ) ≤ p ⟨15,by decide⟩ ∧ p ⟨15,by decide⟩ ≤ (-5596086944460/1000000000000000000 : ℝ)
  h16 : (-6692126130458/1000000000000000000 : ℝ) ≤ p ⟨16,by decide⟩ ∧ p ⟨16,by decide⟩ ≤ (-6692126130457/1000000000000000000 : ℝ)
  h17 : (-7909055150355/1000000000000000000 : ℝ) ≤ p ⟨17,by decide⟩ ∧ p ⟨17,by decide⟩ ≤ (-7909055150354/1000000000000000000 : ℝ)
  h18 : (-9250151726173/1000000000000000000 : ℝ) ≤ p ⟨18,by decide⟩ ∧ p ⟨18,by decide⟩ ≤ (-9250151726172/1000000000000000000 : ℝ)
  h19 : (-10718280701712/1000000000000000000 : ℝ) ≤ p ⟨19,by decide⟩ ∧ p ⟨19,by decide⟩ ≤ (-10718280701711/1000000000000000000 : ℝ)
  h20 : (-12315907555091/1000000000000000000 : ℝ) ≤ p ⟨20,by decide⟩ ∧ p ⟨20,by decide⟩ ≤ (-12315907555090/1000000000000000000 : ℝ)
  h21 : (-14045111604850/1000000000000000000 : ℝ) ≤ p ⟨21,by decide⟩ ∧ p ⟨21,by decide⟩ ≤ (-14045111604849/1000000000000000000 : ℝ)
  h22 : (-15907598917710/1000000000000000000 : ℝ) ≤ p ⟨22,by decide⟩ ∧ p ⟨22,by decide⟩ ≤ (-15907598917709/1000000000000000000 : ℝ)
  h23 : (-17904714925855/1000000000000000000 : ℝ) ≤ p ⟨23,by decide⟩ ∧ p ⟨23,by decide⟩ ≤ (-17904714925854/1000000000000000000 : ℝ)
  h24 : (-20037456761388/1000000000000000000 : ℝ) ≤ p ⟨24,by decide⟩ ∧ p ⟨24,by decide⟩ ≤ (-20037456761387/1000000000000000000 : ℝ)
  h25 : (-22306485315369/1000000000000000000 : ℝ) ≤ p ⟨25,by decide⟩ ∧ p ⟨25,by decide⟩ ≤ (-22306485315368/1000000000000000000 : ℝ)
  h26 : (-24712137028672/1000000000000000000 : ℝ) ≤ p ⟨26,by decide⟩ ∧ p ⟨26,by decide⟩ ≤ (-24712137028671/1000000000000000000 : ℝ)
  h27 : (-27254435421677/1000000000000000000 : ℝ) ≤ p ⟨27,by decide⟩ ∧ p ⟨27,by decide⟩ ≤ (-27254435421676/1000000000000000000 : ℝ)
  h28 : (-29933102369600/1000000000000000000 : ℝ) ≤ p ⟨28,by decide⟩ ∧ p ⟨28,by decide⟩ ≤ (-29933102369599/1000000000000000000 : ℝ)
  h29 : (-32747569130116/1000000000000000000 : ℝ) ≤ p ⟨29,by decide⟩ ∧ p ⟨29,by decide⟩ ≤ (-32747569130115/1000000000000000000 : ℝ)
  h30 : (-35696987129701/1000000000000000000 : ℝ) ≤ p ⟨30,by decide⟩ ∧ p ⟨30,by decide⟩ ≤ (-35696987129700/1000000000000000000 : ℝ)
  h31 : (-38780238514960/1000000000000000000 : ℝ) ≤ p ⟨31,by decide⟩ ∧ p ⟨31,by decide⟩ ≤ (-38780238514959/1000000000000000000 : ℝ)
  h32 : (-41995946475046/1000000000000000000 : ℝ) ≤ p ⟨32,by decide⟩ ∧ p ⟨32,by decide⟩ ≤ (-41995946475045/1000000000000000000 : ℝ)

theorem fifthLevelIntervalHypotheses_of_bounds (p : Fin 33 → ℝ)
    (hp : ∀ k, (fifthLevelSamplesLower k : ℝ) ≤ p k ∧ p k ≤ (fifthLevelSamplesUpper k : ℝ)) :
    FifthLevelIntervalHypotheses p := by
  constructor
  · convert hp 0 using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp 1 using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨2,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨3,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨4,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨5,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨6,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨7,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨8,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨9,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨10,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨11,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨12,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨13,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨14,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨15,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨16,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨17,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨18,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨19,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨20,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨21,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨22,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨23,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨24,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨25,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨26,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨27,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨28,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨29,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨30,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨31,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert hp ⟨32,by decide⟩ using 1 <;> norm_num [fifthLevelSamplesLower, fifthLevelSamplesUpper]


theorem fifthLevelOddBlock_bounds_upper_row0 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨0,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨0,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨0,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨0,by decide⟩ j ≤ (fifthLevelOddUpper ⟨0,by decide⟩ j : ℝ) := by
  change 0 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h16.1, hp.h16.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h8.1, hp.h8.2, hp.h24.1, hp.h24.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2, hp.h24.1, hp.h24.2, hp.h28.1, hp.h28.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2, hp.h20.1, hp.h20.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h28.1, hp.h28.2, hp.h30.1, hp.h30.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h30.1, hp.h30.2, hp.h31.1, hp.h31.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]

theorem fifthLevelOddBlock_bounds_upper_row1 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨1,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨1,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨1,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨1,by decide⟩ j ≤ (fifthLevelOddUpper ⟨1,by decide⟩ j : ℝ) := by
  change 1 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h24.1, hp.h24.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h20.1, hp.h20.2, hp.h24.1, hp.h24.2, hp.h28.1, hp.h28.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h20.1, hp.h20.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h28.1, hp.h28.2, hp.h30.1, hp.h30.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h30.1, hp.h30.2, hp.h31.1, hp.h31.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]

theorem fifthLevelOddBlock_bounds_upper_row2 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨2,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨2,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨2,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨2,by decide⟩ j ≤ (fifthLevelOddUpper ⟨2,by decide⟩ j : ℝ) := by
  change 2 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h20.1, hp.h20.2, hp.h24.1, hp.h24.2, hp.h28.1, hp.h28.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2, hp.h20.1, hp.h20.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2, hp.h30.1, hp.h30.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2, hp.h30.1, hp.h30.2, hp.h31.1, hp.h31.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]

theorem fifthLevelOddBlock_bounds_upper_row3 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨3,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨3,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨3,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨3,by decide⟩ j ≤ (fifthLevelOddUpper ⟨3,by decide⟩ j : ℝ) := by
  change 3 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h14.1, hp.h14.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h10.1, hp.h10.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2]

theorem fifthLevelOddBlock_bounds_upper_row4 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨4,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨4,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨4,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨4,by decide⟩ j ≤ (fifthLevelOddUpper ⟨4,by decide⟩ j : ℝ) := by
  change 4 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2, hp.h30.1, hp.h30.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2, hp.h31.1, hp.h31.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]

theorem fifthLevelOddBlock_bounds_upper_row5 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨5,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨5,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨5,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨5,by decide⟩ j ≤ (fifthLevelOddUpper ⟨5,by decide⟩ j : ℝ) := by
  change 5 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]

theorem fifthLevelOddBlock_bounds_upper_row6 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨6,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨6,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨6,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨6,by decide⟩ j ≤ (fifthLevelOddUpper ⟨6,by decide⟩ j : ℝ) := by
  change 6 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2]

theorem fifthLevelOddBlock_bounds_upper_row7 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨7,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨7,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨7,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨7,by decide⟩ j ≤ (fifthLevelOddUpper ⟨7,by decide⟩ j : ℝ) := by
  change 7 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h15.1, hp.h15.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h13.1, hp.h13.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h11.1, hp.h11.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h9.1, hp.h9.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h7.1, hp.h7.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h5.1, hp.h5.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2]

theorem fifthLevelOddBlock_bounds_upper_row8 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨8,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨8,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨8,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨8,by decide⟩ j ≤ (fifthLevelOddUpper ⟨8,by decide⟩ j : ℝ) := by
  change 8 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2, hp.h31.1, hp.h31.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]

theorem fifthLevelOddBlock_bounds_upper_row9 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨9,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨9,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨9,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨9,by decide⟩ j ≤ (fifthLevelOddUpper ⟨9,by decide⟩ j : ℝ) := by
  change 9 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]

theorem fifthLevelOddBlock_bounds_upper_row10 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨10,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨10,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨10,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨10,by decide⟩ j ≤ (fifthLevelOddUpper ⟨10,by decide⟩ j : ℝ) := by
  change 10 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]

theorem fifthLevelOddBlock_bounds_upper_row11 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨11,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨11,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨11,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨11,by decide⟩ j ≤ (fifthLevelOddUpper ⟨11,by decide⟩ j : ℝ) := by
  change 11 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]

theorem fifthLevelOddBlock_bounds_upper_row12 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨12,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨12,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨12,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨12,by decide⟩ j ≤ (fifthLevelOddUpper ⟨12,by decide⟩ j : ℝ) := by
  change 12 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2]

theorem fifthLevelOddBlock_bounds_upper_row13 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨13,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨13,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨13,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨13,by decide⟩ j ≤ (fifthLevelOddUpper ⟨13,by decide⟩ j : ℝ) := by
  change 13 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2]

theorem fifthLevelOddBlock_bounds_upper_row14 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨14,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨14,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨14,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨14,by decide⟩ j ≤ (fifthLevelOddUpper ⟨14,by decide⟩ j : ℝ) := by
  change 14 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2]
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2]

theorem fifthLevelOddBlock_bounds_upper_row15 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 16) (hij : (⟨15,by decide⟩:Fin 16) ≤ j) :
    (fifthLevelOddLower ⟨15,by decide⟩ j : ℝ) ≤ fifthLevelOddBlock p ⟨15,by decide⟩ j ∧
      fifthLevelOddBlock p ⟨15,by decide⟩ j ≤ (fifthLevelOddUpper ⟨15,by decide⟩ j : ℝ) := by
  change 15 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelOddBlock_entry]
    norm_num [fifthLevelOddWeight, fifthLevelOddLeft, fifthLevelOddMid, fifthLevelOddRight,
      fifthLevelJumpEntry, fifthLevelDistance, Fin.rev, fifthLevelOddLower, fifthLevelOddUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2]

theorem fifthLevelEvenBlock_bounds_upper_row0 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨0,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨0,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨0,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨0,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ j : ℝ) := by
  change 0 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨0,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨0,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h24.1, hp.h24.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨1,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨28,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨28,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨1,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h20.1, hp.h20.2, hp.h24.1, hp.h24.2, hp.h28.1, hp.h28.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨2,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨2,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2, hp.h20.1, hp.h20.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨3,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨28,by decide⟩ ⟨30,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨28,by decide⟩ ⟨30,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨3,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h28.1, hp.h28.2, hp.h30.1, hp.h30.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨4,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨26,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨26,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨4,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨5,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨5,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨6,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨6,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨7,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨7,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h30.1, hp.h30.2, hp.h31.1, hp.h31.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨8,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨8,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨9,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨9,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨10,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨10,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨0,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨0,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]

theorem fifthLevelEvenBlock_bounds_upper_row1 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨1,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨1,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨1,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨1,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ j : ℝ) := by
  change 1 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨1,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨28,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨28,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨1,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h20.1, hp.h20.2, hp.h24.1, hp.h24.2, hp.h28.1, hp.h28.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨2,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨2,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h20.1, hp.h20.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨3,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨28,by decide⟩ ⟨30,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨28,by decide⟩ ⟨30,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨3,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2, hp.h30.1, hp.h30.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨4,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨26,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨26,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨4,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨5,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨5,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨6,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨6,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨7,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨7,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2, hp.h30.1, hp.h30.2, hp.h31.1, hp.h31.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨8,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨8,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨9,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨9,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨10,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨10,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨1,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨1,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]

theorem fifthLevelEvenBlock_bounds_upper_row2 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨2,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨2,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨2,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨2,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ j : ℝ) := by
  change 2 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨2,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨2,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨3,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨28,by decide⟩ ⟨30,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨28,by decide⟩ ⟨30,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨3,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨4,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨26,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨26,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨4,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨5,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨5,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨6,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨6,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨7,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨7,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨8,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨8,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨9,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨9,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨10,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨10,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨2,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨2,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2]

theorem fifthLevelEvenBlock_bounds_upper_row3 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨3,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨3,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨3,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨3,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ j : ℝ) := by
  change 3 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨3,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨28,by decide⟩ ⟨30,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨28,by decide⟩ ⟨30,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨3,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2, hp.h30.1, hp.h30.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨4,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨24,by decide⟩ ⟨26,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨24,by decide⟩ ⟨26,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨4,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2, hp.h26.1, hp.h26.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨5,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨5,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨6,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨6,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨7,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨7,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2, hp.h31.1, hp.h31.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨8,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨8,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨9,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨9,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨10,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨10,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨3,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨3,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]

theorem fifthLevelEvenBlock_bounds_upper_row4 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨4,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨4,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨4,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨4,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ j : ℝ) := by
  change 4 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨4,by decide⟩ ⟨4,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨26,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨26,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ ⟨4,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2, hp.h22.1, hp.h22.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨4,by decide⟩ ⟨5,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ ⟨5,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h18.1, hp.h18.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨4,by decide⟩ ⟨6,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ ⟨6,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨4,by decide⟩ ⟨7,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ ⟨7,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨4,by decide⟩ ⟨8,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ ⟨8,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨4,by decide⟩ ⟨9,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ ⟨9,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨4,by decide⟩ ⟨10,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ ⟨10,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨4,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨4,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨4,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨4,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨4,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]

theorem fifthLevelEvenBlock_bounds_upper_row5 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨5,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨5,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨5,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨5,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨5,by decide⟩ j : ℝ) := by
  change 5 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨5,by decide⟩ ⟨5,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨20,by decide⟩ ⟨22,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨5,by decide⟩ ⟨5,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨5,by decide⟩ ⟨6,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨5,by decide⟩ ⟨6,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨5,by decide⟩ ⟨7,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨5,by decide⟩ ⟨7,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨5,by decide⟩ ⟨8,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ≤ (fifthLevelEvenUpper ⟨5,by decide⟩ ⟨8,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨5,by decide⟩ ⟨9,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨5,by decide⟩ ⟨9,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨5,by decide⟩ ⟨10,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ≤ (fifthLevelEvenUpper ⟨5,by decide⟩ ⟨10,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨5,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨5,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨5,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨5,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨5,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨5,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨5,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨5,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2]

theorem fifthLevelEvenBlock_bounds_upper_row6 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨6,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨6,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨6,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨6,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨6,by decide⟩ j : ℝ) := by
  change 6 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨6,by decide⟩ ⟨6,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨6,by decide⟩ ⟨6,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨6,by decide⟩ ⟨7,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨6,by decide⟩ ⟨7,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨6,by decide⟩ ⟨8,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ≤ (fifthLevelEvenUpper ⟨6,by decide⟩ ⟨8,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨6,by decide⟩ ⟨9,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨6,by decide⟩ ⟨9,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨6,by decide⟩ ⟨10,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ≤ (fifthLevelEvenUpper ⟨6,by decide⟩ ⟨10,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨6,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨6,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨6,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨6,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨6,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨6,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨6,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨6,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2]

theorem fifthLevelEvenBlock_bounds_upper_row7 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨7,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨7,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨7,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨7,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨7,by decide⟩ j : ℝ) := by
  change 7 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨7,by decide⟩ ⟨7,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨30,by decide⟩ ⟨31,by decide⟩ ⟨32,by decide⟩) ≤ (fifthLevelEvenUpper ⟨7,by decide⟩ ⟨7,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2, hp.h31.1, hp.h31.2, hp.h32.1, hp.h32.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨7,by decide⟩ ⟨8,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ≤ (fifthLevelEvenUpper ⟨7,by decide⟩ ⟨8,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2, hp.h29.1, hp.h29.2, hp.h30.1, hp.h30.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨7,by decide⟩ ⟨9,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨7,by decide⟩ ⟨9,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨7,by decide⟩ ⟨10,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ≤ (fifthLevelEvenUpper ⟨7,by decide⟩ ⟨10,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨7,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨7,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨7,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨7,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨7,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨7,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨7,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨0,by decide⟩ ⟨1,by decide⟩ ⟨2,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨7,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]

theorem fifthLevelEvenBlock_bounds_upper_row8 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨8,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨8,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨8,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨8,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨8,by decide⟩ j : ℝ) := by
  change 8 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨8,by decide⟩ ⟨8,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨28,by decide⟩ ⟨29,by decide⟩ ⟨30,by decide⟩) ≤ (fifthLevelEvenUpper ⟨8,by decide⟩ ⟨8,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2, hp.h27.1, hp.h27.2, hp.h28.1, hp.h28.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨8,by decide⟩ ⟨9,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨8,by decide⟩ ⟨9,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2, hp.h25.1, hp.h25.2, hp.h26.1, hp.h26.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨8,by decide⟩ ⟨10,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ≤ (fifthLevelEvenUpper ⟨8,by decide⟩ ⟨10,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨8,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨8,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨8,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨8,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨8,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨8,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨8,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨2,by decide⟩ ⟨3,by decide⟩ ⟨4,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨8,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]

theorem fifthLevelEvenBlock_bounds_upper_row9 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨9,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨9,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨9,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨9,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨9,by decide⟩ j : ℝ) := by
  change 9 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨9,by decide⟩ ⟨9,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨26,by decide⟩ ⟨27,by decide⟩ ⟨28,by decide⟩) ≤ (fifthLevelEvenUpper ⟨9,by decide⟩ ⟨9,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2, hp.h23.1, hp.h23.2, hp.h24.1, hp.h24.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨9,by decide⟩ ⟨10,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ≤ (fifthLevelEvenUpper ⟨9,by decide⟩ ⟨10,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2, hp.h21.1, hp.h21.2, hp.h22.1, hp.h22.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨9,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨9,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨9,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨9,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨9,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨9,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨9,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨4,by decide⟩ ⟨5,by decide⟩ ⟨6,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨9,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]

theorem fifthLevelEvenBlock_bounds_upper_row10 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨10,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨10,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨10,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨10,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨10,by decide⟩ j : ℝ) := by
  change 10 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨10,by decide⟩ ⟨10,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ - fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨24,by decide⟩ ⟨25,by decide⟩ ⟨26,by decide⟩) ≤ (fifthLevelEvenUpper ⟨10,by decide⟩ ⟨10,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2, hp.h19.1, hp.h19.2, hp.h20.1, hp.h20.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨10,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨10,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2, hp.h17.1, hp.h17.2, hp.h18.1, hp.h18.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨10,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨10,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨10,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨10,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨10,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨6,by decide⟩ ⟨7,by decide⟩ ⟨8,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨10,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]

theorem fifthLevelEvenBlock_bounds_upper_row11 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨11,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨11,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨11,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨11,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨11,by decide⟩ j : ℝ) := by
  change 11 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨11,by decide⟩ ⟨11,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨22,by decide⟩ ⟨23,by decide⟩ ⟨24,by decide⟩) ≤ (fifthLevelEvenUpper ⟨11,by decide⟩ ⟨11,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2, hp.h15.1, hp.h15.2, hp.h16.1, hp.h16.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨11,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨11,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2, hp.h13.1, hp.h13.2, hp.h14.1, hp.h14.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨11,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨11,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨11,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨8,by decide⟩ ⟨9,by decide⟩ ⟨10,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨11,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2]

theorem fifthLevelEvenBlock_bounds_upper_row12 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨12,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨12,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨12,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨12,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨12,by decide⟩ j : ℝ) := by
  change 12 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨12,by decide⟩ ⟨12,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ - fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨20,by decide⟩ ⟨21,by decide⟩ ⟨22,by decide⟩) ≤ (fifthLevelEvenUpper ⟨12,by decide⟩ ⟨12,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2, hp.h11.1, hp.h11.2, hp.h12.1, hp.h12.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨12,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨12,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2, hp.h9.1, hp.h9.2, hp.h10.1, hp.h10.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨12,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨10,by decide⟩ ⟨11,by decide⟩ ⟨12,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨12,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2]

theorem fifthLevelEvenBlock_bounds_upper_row13 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨13,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨13,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨13,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨13,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨13,by decide⟩ j : ℝ) := by
  change 13 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨13,by decide⟩ ⟨13,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ ⟨18,by decide⟩ ⟨19,by decide⟩ ⟨20,by decide⟩) ≤ (fifthLevelEvenUpper ⟨13,by decide⟩ ⟨13,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2, hp.h7.1, hp.h7.2, hp.h8.1, hp.h8.2]
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨13,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨12,by decide⟩ ⟨13,by decide⟩ ⟨14,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨13,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h4.1, hp.h4.2, hp.h5.1, hp.h5.2, hp.h6.1, hp.h6.2]

theorem fifthLevelEvenBlock_bounds_upper_row14 (p : Fin 33 → ℝ)
    (hp : FifthLevelIntervalHypotheses p) (j : Fin 15) (hij : (⟨14,by decide⟩:Fin 15) ≤ j) :
    (fifthLevelEvenLower ⟨14,by decide⟩ j : ℝ) ≤ fifthLevelEvenBlock p ⟨14,by decide⟩ j ∧
      fifthLevelEvenBlock p ⟨14,by decide⟩ j ≤ (fifthLevelEvenUpper ⟨14,by decide⟩ j : ℝ) := by
  change 14 ≤ j.val at hij
  fin_cases j <;> norm_num at hij
  · rw [fifthLevelEvenBlock_entry]
    change (fifthLevelEvenLower ⟨14,by decide⟩ ⟨14,by decide⟩ : ℝ) ≤ 2 * (fifthLevelJumpEntry p ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ∧
      2 * (fifthLevelJumpEntry p ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ - fifthLevelJumpEntry p ⟨14,by decide⟩ ⟨15,by decide⟩ ⟨16,by decide⟩ ⟨16,by decide⟩ ⟨17,by decide⟩ ⟨18,by decide⟩) ≤ (fifthLevelEvenUpper ⟨14,by decide⟩ ⟨14,by decide⟩ : ℝ)
    norm_num [fifthLevelJumpEntry, fifthLevelDistance, fifthLevelEvenLower, fifthLevelEvenUpper]
    constructor <;> linarith only [hp.h0.1, hp.h0.2, hp.h1.1, hp.h1.2, hp.h2.1, hp.h2.2, hp.h3.1, hp.h3.2, hp.h4.1, hp.h4.2]

theorem fifthLevelOddLower_symm (i j : Fin 16) :
    fifthLevelOddLower i j = fifthLevelOddLower j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem fifthLevelOddUpper_symm (i j : Fin 16) :
    fifthLevelOddUpper i j = fifthLevelOddUpper j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem fifthLevelOddBlock_bounds (p : Fin 33 → ℝ)
    (hp : ∀ k, (fifthLevelSamplesLower k : ℝ) ≤ p k ∧ p k ≤ (fifthLevelSamplesUpper k : ℝ))
    (i j : Fin 16) : (fifthLevelOddLower i j : ℝ) ≤ fifthLevelOddBlock p i j ∧
      fifthLevelOddBlock p i j ≤ (fifthLevelOddUpper i j : ℝ) := by
  have hh := fifthLevelIntervalHypotheses_of_bounds p hp
  have hu (a b : Fin 16) (hab : a ≤ b) :
      (fifthLevelOddLower a b : ℝ) ≤ fifthLevelOddBlock p a b ∧
        fifthLevelOddBlock p a b ≤ (fifthLevelOddUpper a b : ℝ) := by
    fin_cases a
    · exact fifthLevelOddBlock_bounds_upper_row0 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row1 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row2 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row3 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row4 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row5 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row6 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row7 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row8 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row9 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row10 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row11 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row12 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row13 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row14 p hh b hab
    · exact fifthLevelOddBlock_bounds_upper_row15 p hh b hab
  rcases le_total i j with hij | hji
  · exact hu i j hij
  · rw [fifthLevelOddLower_symm i j, fifthLevelOddUpper_symm i j, fifthLevelOddBlock_symm p i j]
    exact hu j i hji

theorem fifthLevelEvenLower_symm (i j : Fin 15) :
    fifthLevelEvenLower i j = fifthLevelEvenLower j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem fifthLevelEvenUpper_symm (i j : Fin 15) :
    fifthLevelEvenUpper i j = fifthLevelEvenUpper j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem fifthLevelEvenBlock_bounds (p : Fin 33 → ℝ)
    (hp : ∀ k, (fifthLevelSamplesLower k : ℝ) ≤ p k ∧ p k ≤ (fifthLevelSamplesUpper k : ℝ))
    (i j : Fin 15) : (fifthLevelEvenLower i j : ℝ) ≤ fifthLevelEvenBlock p i j ∧
      fifthLevelEvenBlock p i j ≤ (fifthLevelEvenUpper i j : ℝ) := by
  have hh := fifthLevelIntervalHypotheses_of_bounds p hp
  have hu (a b : Fin 15) (hab : a ≤ b) :
      (fifthLevelEvenLower a b : ℝ) ≤ fifthLevelEvenBlock p a b ∧
        fifthLevelEvenBlock p a b ≤ (fifthLevelEvenUpper a b : ℝ) := by
    fin_cases a
    · exact fifthLevelEvenBlock_bounds_upper_row0 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row1 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row2 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row3 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row4 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row5 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row6 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row7 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row8 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row9 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row10 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row11 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row12 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row13 p hh b hab
    · exact fifthLevelEvenBlock_bounds_upper_row14 p hh b hab
  rcases le_total i j with hij | hji
  · exact hu i j hij
  · rw [fifthLevelEvenLower_symm i j, fifthLevelEvenUpper_symm i j, fifthLevelEvenBlock_symm p i j]
    exact hu j i hji

end
end RiemannResearch.RH
