// !!! Pri kopirovani celeho kodu do jinych agentu je potreba prepsat:       !!!
// !!!  1) pocatecni znalosti range(X)                                       !!!
// !!!  2) commander agent obsahuje akce pro zadavani prikazu                !!!
// !!!                                                                       !!!
// !!!  Fast a Middle jsou temer totozni agenti z pohledu kodu. Slow agent   !!!
// !!!  navic odesila prikazy ostatnim.                                      !!!
/* =========================== POCATECNI ZNALOSTI =========================== */

range(3). // Ulozeni vzdalenosti, protoze implicitne neni ulozena.
commander(aSlow).

intention(scout). // Pocatecni zamer

/* ============================== INICIALIZACE ============================== */
!init.

// Inicializace baze znalosti
@init[atomic] +!init <-
    !initUnknown;
    !lookAround;
    !sendAchieveToAll(intentionScout). //? Ukazkove zadani prikazu

// Inicializace nenavstivenych bunek
+!initUnknown : grid_size(GX,GY) & depot(DX,DY) <-
    for (.range(X, 0, GX - 1))
    {
        for (.range(Y, 0, GY - 1))
        {
            +unknown(X,Y);
        }
    }.

// Pridani skutecnosti zda se agent nachazi v depu do baze znalosti. Slouzi
// jen pro proholdnejsi detekci. Slo by to kontroloval primo, kde je to 
// potreba bez ukladani do baze znalosti.
+!onDepotInit : pos(PX,PY) & depot(DX,DY) & PX == DX & PY == DY <- -onDepot(_); +onDepot(true).
+!onDepotInit : true                                            <- -onDepot(_); +onDepot(false).

/* =========================== KONEC INICIALIZACE =========================== */
+step(X) <- +subStepDone(x).

// Zkousel jsem ruzna zpracovani hlavni smycky a tahle jedina mi funguje.
// Dokud ma agent pohybove body tak bude neco delat.
+subStepDone(x) : moves_left(0) <- -subStepDone(x).
+subStepDone(x) : true          <- -subStepDone(x); !doMacroStep; +subStepDone(x).

// Macro, protoze doStep uz byl a potrebuju k nemu pribalit !lookAround.
@macroStep[atomic] +!doMacroStep <- !lookAround; !giveCommands; !doIntention.

// Provadeni akci na zaklade aktualniho zameru
+!doIntention : intention(scout)    <- !scout.
+!doIntention : intention(goTo,X,Y) <- !goTo(X,Y).
+!doIntention : intention(pick,X,Y) <- !pick(X,Y).
+!doIntention : intention(unload)   <- !onDepotInit; !unload.
+!doIntention : intention(idle)     <- do(skip).
+!doIntention : true                <- !chooseNextIntention.

+!chooseNextIntention : unknown(X,Y) <- +intention(scout). // Kdyz nic, tak scout
+!chooseNextIntention : true         <- +intention(idle);.print("idle").


/* ============================= DAVANI PRIKAZU ============================= */

// Tuhle akci agenti volaji az dokonci aktualni ukol.
+!commandDone(Agent) <- -pendingCommand(Agent).
        
// Velice jednoduche davani prikazu. Agent ceka dokud vsichni agenti splnili
// svuj ukol a pote jim zada co maji jit zvednout (verze davani prikazu hned
// jak ukol dokonci nefunguje, protoze se muze stat ze agenty posle na ruzna
// mista).
+!giveCommands : pendingCommand(_). // Cekame na dokonceni vsech prikazu
+!giveCommands : obj(wood,X,Y) <- // Vime o nejakem dreve
    !sendAchieveToAll(intentionPick(X,Y));
    for (friend(F)) // Ulozime nedokoncene prikazy pro vsechny agenty
    { 
        +pendingCommand(F); 
    } 
    !giveCommands.
+!giveCommands : obj(gold,X,Y) <- // Vime o nejakem zlate
    !sendAchieveToAll(intentionPick(X,Y));
    for (friend(F)) // Ulozime nedokoncene prikazy pro vsechny agenty
    { 
        +pendingCommand(F); 
    } 
    !giveCommands.
+!giveCommands.

/* ========================== IMPLEMENTACE PRIKAZU ========================== */

// Agent pujde k prvni neprozkoumane bunce, kterou vytahne z baze znalosti.
+!scout : unknown(_,_) <- // Porad existuji neprozkoumane bunky
    !getRandomUnknown(X,Y);
    -intention(scout); 
    +intention(goTo,X,Y).
+!scout : true <- -intention(scout).// Vsechny bunky byly prozkoumany

+!getRandomUnknown(X,Y) <- 
    .findall(unknown(A,B), unknown(A,B), Unknowns);  // Nacteni vsech neprozkoumanych bunek
    .length(Unknowns, Length);                       // Pocet bunek
    RandIndex = math.round(math.random(Length - 1)); // Nahodne zvolime bunku
    .nth(RandIndex, Unknowns, unknown(X,Y)).         // Nacteni bunky ze seznamu

// Prikaz k presunu na pozici [X,Y]
+!goTo(X,Y) : pos(X,Y) <- -intention(goTo,X,Y). // Uz jsme na miste
+!goTo(X,Y) : true     <- !moveTo(X,Y).         // Porad tam nejsme

// Zvednuti zdroje ze zeme (agent musi mit plny pocet pohybovych bodu).
+!pick(X,Y) : pos(X,Y) & ally(X,Y) & moves_left(ML) & moves_per_round(ML) <- 
    do(pick); 
    -intention(pick,X,Y); 
    +intention(unload).
+!pick(X,Y) : pos(X,Y) <- do(skip). // Cekani na jineho agenta
+!pick(X,Y) : true     <- !moveTo(X,Y).

// Vyprazdneni agenta (agent musi mit plny pocet pohybovych bodu).
+!unload : onDepot(true) & moves_left(ML) & moves_per_round(ML) & commander(C) & .my_name(MN) <- 
    do(drop); 
    -intention(unload);
    .send(C, achieve, commandDone(MN)).
+!unload : onDepot(true)  <- do(skip).
+!unload : onDepot(false) <- !moveToDepot.

/* ============================ PRIJMUTI PRIKAZU ============================ */

@intScout[atomic]  +!intentionScout     <- !clearIntention; +intention(scout).
@intGoTo[atomic]   +!intentionGoTo(X,Y) <- !clearIntention; +intention(goTo,X,Y).
@intPick[atomic]   +!intentionPick(X,Y) <- !clearIntention; +intention(pick,X,Y).
@intUnload[atomic] +!intentionUnload    <- !clearIntention; +intention(unload).
@intIdle[atomic]   +!intentionIdle      <- !clearIntention; +intention(idle).

// Odstraneni aktualniho zameru
// !!! Pokud pribudou nove zamery s vetsi aritou je treba dopsat !!!
+!clearIntention <- -intention(_); -intention(_,_); -intention(_,_,_).

/* ===================== PROHLEDAVANI VIDITELNEHO OKOLI ===================== */

// Prohledavani okoli a ulozeni/odstraneni zaznamu o okolnich zdrojich.
+!lookAround : pos(PosX,PosY) & range(R) <- 
    for (.range(X, PosX - R, PosX + R)) // Cyklus pres viditelne bunky
    {
        for (.range(Y, PosY - R, PosY + R))
        {
            !checkUnknown(X,Y);
            !checkObstacle(X,Y);
            !checkGold(X,Y);
            !checkWood(X,Y);
        }
    }.

// Kontrola zda byla bunka objevena
+!checkUnknown(X,Y) : unknown(X,Y) <- -unknown(X,Y); !sendDiscoverInfo(X,Y).
+!checkUnknown(X,Y). // O prazdnem miste uz vime

// Aktualizace znalosti o prekazkach
+!checkObstacle(X,Y) : obstacle(X,Y) & not obj(obs,X,Y) <- // Nova prekazka
    +obj(obs,X,Y); 
    !sendObjectInfo(obs,X,Y,add). 
+!checkObstacle(X,Y). // Prekazka tady neni

// Aktualizace znalosti o zlate
+!checkGold(X,Y) : gold(X,Y) & not obj(gold,X,Y) <- // Prvni nalez zlata
    +obj(gold,X,Y); 
    !sendObjectInfo(gold,X,Y,add). 
+!checkGold(X,Y) : not gold(X,Y) & obj(gold,X,Y) <- // Zlato nekdo vzal
    -obj(gold,X,Y); 
    !sendObjectInfo(gold,X,Y,remove). 
+!checkGold(X,Y). // Zlato tady neni

// Aktualizace znalosti o dreve
+!checkWood(X,Y) : wood(X,Y) & not obj(wood,X,Y) <- // Prvni nalez dreva
    +obj(wood,X,Y); 
    !sendObjectInfo(wood,X,Y,add).
+!checkWood(X,Y) : not wood(X,Y) & obj(wood,X,Y) <- // Drevo nekdo vzal
    -obj(wood,X,Y); 
    !sendObjectInfo(wood,X,Y,remove). 
+!checkWood(X,Y). // Drevo taky neni


/* ============= AKCE PRO ODESLANI/PRIJMUNI INFOMACI O PROSTORU ============= */

// Nacteni vsech friendu z baze znalosti
+!sendAchieveToAll(Action) <-
    for (friend(Agent)) 
    {
        .send(Agent, achieve, Action);
    }.

// Temer zbytecne akce, rovnou by slo psat sendAchieveToAll
+!sendDiscoverInfo(X,Y) <- !sendAchieveToAll(recvDiscoverInfo(X,Y)).
+!sendObjectInfo(O,X,Y,AddRemove) <- !sendAchieveToAll(recvObjectInfo(O,X,Y,AddRemove)).

// Reakce na objeveni bunky
+!recvDiscoverInfo(X,Y) <- -unknown(X,Y).

// Reakce na objeveni zdroje
+!recvObjectInfo(O,X,Y,AddRemove) : AddRemove == add    <- +obj(O,X,Y).
+!recvObjectInfo(O,X,Y,AddRemove) : AddRemove == remove <- -obj(O,X,Y).

/* ================================= POHYB ================================== */

// Pohyb k depu
+!moveToDepot : depot(DX, DY) <- !moveTo(DX,DY).

// Pohyb na [X,Y] bunku
// Kdyz obchazim prekazku doleva tak doprava urcite muzu, ale nemela 
// bych se vracet - doprava znovu muzu az se priblizim k cili ve smeru nahoru/dolu
+!moveTo(TarX,TarY) : pos(PosX,PosY) <- !moveTo(PosX,PosY,TarX,TarY).
+!moveTo(PosX,PosY,TarX,TarY) : PosX < TarX & not obj(obs,PosX + 1, PosY)
	& not rounding("L") <- do(right); 
	if(rounding("D")){-rounding("D")}
	else{if(rounding("U")){-rounding("U")}}.
+!moveTo(PosX,PosY,TarX,TarY) : PosX > TarX & not obj(obs,PosX - 1, PosY)
	& not rounding("R") <- do(left);
	if(rounding("D")){-rounding("D")}
	else{if(rounding("U")){-rounding("U")}}.
+!moveTo(PosX,PosY,TarX,TarY) : PosY < TarY & not obj(obs,PosX, PosY + 1)
	& not rounding("U") <- do(down);
	if(rounding("R")){-rounding("R")}
	else{if(rounding("L")){-rounding("L")}}.
+!moveTo(PosX,PosY,TarX,TarY) : PosY > TarY & not obj(obs,PosX, PosY-1)
	& not rounding("D") <- do(up);
	if(rounding("R")){-rounding("R")}
	else{if(rounding("L")){-rounding("L")}}.
+!moveTo(PosX,PosY,TarX,TarY) : PosX == TarX & PosY == TarY. //Jsme na miste
+!moveTo(PosX,PosY,TarX,TarY) : true <- !roundBar(PosX, PosY, TarX, TarY). 
/*======================= OBCHAZENI PREKAZKY ================================ */
// Obchazime zleva, pokracujeme doleva, pokud muzeme
+!roundBar(PosX, PosY, TarX, TarY): rounding("L") &  
	not obj(obs,PosX - 1, PosY) <- do(left) ;
	if(rounding("D")){-rounding("D")}
	else{if(rounding("U")){-rounding("U")}}.

// Obchazime zprava, pokracujeme doprava, pokud muzeme
+!roundBar(PosX, PosY, TarX, TarY): rounding("R") & 
	not obj(obs,PosX + 1, PosY) <- do(right); 
	if(rounding("D")){-rounding("D")}
	else{if(rounding("U")){-rounding("U")}}.
	
// Obchazime prekazku zleva/zprava, cil lezi vpravo-vlevo dole, ale nemuzeme jit 
// ani doleva-doprava ani dolu - zkusime nahoru
+!roundBar(PosX, PosY, TarX, TarY): PosY < TarY & (rounding("L") | rounding("R")) &
	not obj(obs,PosX, PosY-1) <- do(up); +rounding("U").

// Obchazime prekazku zleva-zprava, cil lezi vpravo/vlevo nahore, ale nemuzeme 
// jit ani doleva-doprava ani dolu - zkusime nahoru
+!roundBar(PosX, PosY, TarX, TarY): PosY > TarY & (rounding("L") | rounding("R")) &
	not obj(obs,PosX, PosY+1) <- do(down); +rounding("D").
	
// Obchazime prekazku zleva, cil lezi vpravo, ale nemuzeme jit ani doleva
// ani dolu ani nahoru - jdeme doprava
+!roundBar(PosX, PosY, TarX, TarY): rounding("L") &
	not obj(obs,PosX+1, PosY) <- do(right);
	?rounding(X); -rounding(X).
	
// Obchazime prekazku zprava, cil lezi vlevo, ale nemuzeme jit ani doprava
// ani dolu ani nahoru - jdeme doleva
+!roundBar(PosX, PosY, TarX, TarY): rounding("R") &
	not obj(obs,PosX-1, PosY) <- do(left); 
	?rounding(X); -rounding(X).


/***************** Narazili jsme poprve prekazku ******************************/
// Cil vpravo
+!roundBar(PosX, PosY, TarX, TarY): PosX < TarX & 
	not obj(obs,PosX - 1, PosY) <- +rounding("L"); do(left).
									
+!roundBar(PosX, PosY, TarX, TarY): PosX < TarX <- +rounding("L"); 
	!roundBar(PosX, PosY, TarX, TarY).
	
// Cil vlevo
+!roundBar(PosX, PosY, TarX, TarY): PosX > TarX &
	not obj(obs,PosX + 1, PosY) <- +rounding("R"); do(right).
									
+!roundBar(PosX, PosY, TarX, TarY): PosX > TarX <- +rounding("R"); 
	!roundBar(PosX, PosY, TarX, TarY).

+!roundBar(PosX, PosY, TarX, TarY) <- .print("Dostali jsme se do slepe ulicky.").
/*============================================================================*/
