// !!! Pri kopirovani celeho kodu do jinych agentu je potreba prepsat:       !!!
// !!!  1) pocet kroku v +step(X)                                            !!!
// !!!  2) jmena cilovych agentu v odesilani informaci v sendObjectInfo      !!!
// !!!     a sendDiscoverInfo                                                !!!
// !!!  3) pocatecni znalosti range(X)                                       !!!
/* =========================== POCATECNY ZNALOSTI =========================== */

range(1). // Ulozeni vzdalenosti, protoze implicitne neni ulozena.

// Agent nic nedela, ale aSlow mu na zacatku posle prikaz scout.
intention(idle). // Pocatecni zamer

/* ============================== INICIALIZACE ============================== */
!init.

// Inicializace baze znalosti
@init[atomic] +!init <-
    !onDepotInit;
    !initUnknown;
    !lookAround.

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

// Byl pokus (pod komentarem) o takovouto smycku pri ktere by se v krocich 
// nemuselo kontrolovat zda se se neco provedlo (do(_)), ale "!doStep" by 
// se volal dokud by move_left(X) bylo vetsi jak 0. Nicmene to nefunguje
// (nefunguje nize popsana smycka).
//
// Bez atomic se provadi prilis mnoho kroku (vsechny akce se totiz nejspis 
// vykonavaji zaraz tj. "!lookAround; !doStep; !work." se spusti paralelne 
// (!work znovu spusti "!lookAround; !doStep;", takze se nekolikrat spusti 
// "!doStep" bez ohledu na moves_left). Jak je to ted s @w1[atomic] to castecne
// funguje, ale problem je v agentovy aFast (asi i ostatnich jen se to 
// neprojevuje), ze nezpracovava udalosti. 
//
// Pokud nekdo vi jak udelat tu smycku, aby se v krokich nemuselo kontrolovat
// zda se neco udela at napise.
/*
+step(X) <- !work.
@w1[atomic] +!work : moves_left(0).
@w2[atomic] +!work <- 
    !lookAround; 
    !doStep; 
    !work.
*/

// Pri takto pevnem poctu kroku, jen nutne v kazdem kroku neco udelat jinak
// se program zasekne resp. se ceka az agent vycerpa svoje pohyby, coz se ale 
// nikdy nestane. Pozor: to byva pricina zastaveni vsech agentu.
+step(X) <- !doMacroStep; !doMacroStep; !doMacroStep.

// Macro, protoze doStep uz byl a potrebuju k nemu pribalit !lookAround.
+!doMacroStep <- !lookAround; !doStep.

// Provadeni akci na zaklade aktualniho zameru
+!doStep : intention(scout)    <- !scout.
+!doStep : intention(goTo,X,Y) <- !goTo(X,Y).
+!doStep : intention(pick,X,Y) <- !pick(X,Y). // !!! ZATIM JEN NASTIN !!!
+!doStep : intention(unload)   <- !unload.
+!doStep : intention(idle)     <- do(skip).
+!doStep : true                <- !chooseNextIntention.

//? V budoucnu by tu mohlo byt rozhodnuti na uplnem pocatku.
+!chooseNextIntention <- +intention(idle); !doStep.

/* ========================== IMPLEMENTACE PRIKAZU ========================== */

// Agent pujde k prvni neprozkoumane bunce, kterou vytahne z baze znalosti.
+!scout : unknown(X,Y) <- !moveTo(X,Y). // Porad existuji neprozkoumane bunky
+!scout : true         <- -intention(scout); !doStep.// Vsechny bunky byly prozkoumany

// Prikaz k presunu na pozici [X,Y]
+!goTo(X,Y) : pos(X,Y) <- -intention(goTo,X,Y); !doStep. // Uz jsme na miste
+!goTo(X,Y) : true     <- !moveTo(X,Y). // Porad tam nejsme

// Zvednuti zdroje ze zeme
+!pick(X,Y) : pos(X,Y) <- do(pick); -intention(pick,X,Y). // !!! ZATIM JEN NASTIN !!!
+!pick(X,Y) : true     <- !moveTo(X,Y).

// Vyprazdneni agenta
+!unload : onDepot(true)  <- do(drop); -intention(unload).
+!unload : onDepot(false) <- !moveToDepot.

/* ============================ PRIJMUTI PRIKAZU ============================ */

+!intentionScout     <- !clearIntention; +intention(scout).
+!intentionGoTo(X,Y) <- !clearIntention; +intention(goTo,X,Y).
+!intentionPick(X,Y) <- !clearIntention; +intention(pick,X,Y).
+!intentionUnload    <- !clearIntention; +intention(unload).
+!intentionIdle      <- !clearIntention; +intention(idle).

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

//? Prepsat cilove agenty u ostatni agentu. Asi to pujde ejak pres friend(X), 
//  ale nevim jak vytahnout oboje hodnoty z baze znalosti
+!sendDiscoverInfo(X,Y) <- 
    .send(aMiddle, achieve, recvDiscoverInfo(X,Y));
    .send(aSlow,   achieve, recvDiscoverInfo(X,Y)).

+!sendObjectInfo(O,X,Y,AddRemove) <-
    .send(aMiddle, achieve, recvObjectInfo(O,X,Y,AddRemove));
    .send(aSlow,   achieve, recvObjectInfo(O,X,Y,AddRemove)).

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
+!moveTo(PosX,PosY,TarX,TarY) <- !doStep. // Uz jsem na miste: PosX == TarX & PosY == TarY

