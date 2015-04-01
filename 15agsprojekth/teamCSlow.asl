// !!! Pri kopirovani celeho kodu do jinych agentu je potreba prepsat:       !!!
// !!!  1) spratelene agenty v pocatecni znalosti friendA(), friendB()       !!!
// !!!  2) pocatecni znalosti range(X)                                       !!!
// !!!  3) commander agent obsahuje akce pro zadavani prikazu                !!!
/* =========================== POCATECNY ZNALOSTI =========================== */

range(3). // Ulozeni vzdalenosti, protoze implicitne neni ulozena.
friendA(aFast). // Sprateleni agenti, kterym se budou odesilat informace o okoli
friendB(aMiddle).

commander(aSlow).

// Agent nic nedela, ale aSlow mu na zacatku posle prikaz scout.
intention(scout). // Pocatecni zamer

/* ============================== INICIALIZACE ============================== */
!init.

// Inicializace baze znalosti
@init[atomic] +!init <-
    !onDepotInit;
    !initUnknown;
    !lookAround;
    .send(aFast, achieve, intentionScout); // Ukazkove zadani prikazu
    .send(aMiddle, achieve, intentionScout).

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
+!doIntention : intention(pick,X,Y) <- !pick(X,Y). // !!! ZATIM JEN NASTIN !!!
+!doIntention : intention(unload)   <- !unload.
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
+!giveCommands : pendingCommand(_). 
+!giveCommands : obj(wood,X,Y) & friendA(AgentA) & friendB(AgentB) <- // Vime o nejakem dreve
    .send(AgentA, achieve, intentionPick(X,Y)); 
    .send(AgentB, achieve, intentionPick(X,Y));
    +pendingCommand(AgentA);
    +pendingCommand(AgentB);
    !giveCommands.
+!giveCommands : obj(gold,X,Y) & friendA(AgentA) & friendB(AgentB) <- // Vime o nejakem zlate
    .send(AgentA, achieve, intentionPick(X,Y)); 
    .send(AgentB, achieve, intentionPick(X,Y));
    +pendingCommand(AgentA);
    +pendingCommand(AgentB);
    !giveCommands.
+!giveCommands.


/* ========================== IMPLEMENTACE PRIKAZU ========================== */

// Agent pujde k prvni neprozkoumane bunce, kterou vytahne z baze znalosti.
+!scout : unknown(X,Y) <- !moveTo(X,Y).     // Porad existuji neprozkoumane bunky
+!scout : true         <- -intention(scout).// Vsechny bunky byly prozkoumany

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
+!checkUnknown(X,Y) : unknown(X,Y) <- -unknown(X,Y); !sendDiscoverInfo(X,Y); .
+!checkUnknown(X,Y). // O prazdnem miste uz vime

// Aktualizace znalosti o prekazkach
+!checkObstacle(X,Y) : obsticle(X,Y) & not obj(obsticle,X,Y) <- // Nova prekazka
    +obs(X,Y); 
    !sendObjectInfo(obsticle,X,Y,add). 
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

+!sendDiscoverInfo(X,Y) : friendA(FA) & friendB(FB) <- 
    .send(FA, achieve, recvDiscoverInfo(X,Y));
    .send(FB, achieve, recvDiscoverInfo(X,Y)).

+!sendObjectInfo(O,X,Y,AddRemove) : friendA(FA) & friendB(FB) <- 
    .send(FA, achieve, recvObjectInfo(O,X,Y,AddRemove));
    .send(FB, achieve, recvObjectInfo(O,X,Y,AddRemove)).

+!recvDiscoverInfo(X,Y) <- -unknown(X,Y).

+!recvObjectInfo(O,X,Y,AddRemove) : AddRemove == add    <- +obj(O,X,Y).
+!recvObjectInfo(O,X,Y,AddRemove) : AddRemove == remove <- -obj(O,X,Y).

/* ================================= POHYB ================================== */

// Pohyb k depu
+!moveToDepot : depot(DX, DY) <- !moveTo(DX,DY).

// Pohyb na [X,Y] bunku
+!moveTo(TarX,TarY) : pos(PosX,PosY) <- !moveTo(PosX,PosY,TarX,TarY).
+!moveTo(PosX,PosY,TarX,TarY) : PosX < TarX <- do(right); !onDepotInit.
+!moveTo(PosX,PosY,TarX,TarY) : PosX > TarX <- do(left); !onDepotInit.
+!moveTo(PosX,PosY,TarX,TarY) : PosY < TarY <- do(down); !onDepotInit.
+!moveTo(PosX,PosY,TarX,TarY) : PosY > TarY <- do(up); !onDepotInit.
+!moveTo(PosX,PosY,TarX,TarY). // Uz jsem na miste: PosX == TarX & PosY == TarY

