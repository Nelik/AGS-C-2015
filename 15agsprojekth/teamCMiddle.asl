/* =========================== POCATECNY ZNALOSTI =========================== */

range(1). // Ulozeni vzdalenosti, protoze implicitne neni ulozena.

intention(scout). // Pocatecni zamer

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

+step(X) <- !work.

// Hlavni smycka vykonani kroku
// !!! Je potreba prepsat, nechce se mi psat jaky, opravim co nejdriv !!!
@w1[atomic] +!work : moves_left(0).
@w2[atomic] +!work <- !lookAround; !doStep; !work.

// Provadeni akci na zaklade aktualniho zameru
+!doStep : intention(scout)    <- !scout.
+!doStep : intention(goTo,X,Y) <- !goTo(X,Y).
+!doStep : intention(pick,X,Y) <- !pick(X,Y). // !!! ZATIM JEN NASTIN !!!
+!doStep : intention(unload)   <- !unload.
+!doStep : intention(idle)     <- do(skip).
+!doStep : true                <- !chooseNextIntention.

//? V budoucnu by tu mohlo byt rozhodnuti na uplnem pocatku.
+!chooseNextIntention <- +intention(idle).

/* ========================== IMPLEMENTACE PRIKAZU ========================== */

// Agent pujde k prvni neprozkoumane bunce, kterou vytahne z baze znalosti.
+!scout : unknown(X,Y) <- !moveTo(X,Y).      // Porad existuji neprozkoumane bunky
+!scout : true         <- -intention(scout). // Vsechny bunky byly prozkoumany

// Prikaz k presunu na pozici [X,Y]
+!goTo(X,Y) : pos(X,Y) <- -intention(goTo,X,Y). // Uz jsme na miste
+!goTo(X,Y) : true     <- !moveTo(X,Y).         // Porad tam nejsme

// Zvednuti zdroje ze zeme
+!pick(X,Y) : pos(X,Y) <- do(pick); -intention(pick,X,Y). // !!! ZATIM JEN NASTIN !!!
+!pick(X,Y) : true     <- !moveTo(X,Y).

// Vyprazdneni agenta
+!unload : onDepot(true)  <- do(drop); -intention(unload).
+!unload : onDepot(false) <- !moveToDepot.

/* ============================ PRIJMUTI PRIKAZU ============================ */

+!intentionScout(X,Y) <- !clearCommand; +intention(pick).
+!intentionGoTo(X,Y)  <- !clearCommand; +intention(goTo,X,Y).
+!intentionPick(X,Y)  <- !clearCommand; +intention(pick,X,Y).
+!intentionUnload     <- !clearCommand; +intention(unload).
+!intentionIdle       <- !clearCommand; +intention(idle).

// Odstraneni aktualniho zameru
// !!! Pokud pribudou nove zamery s vetsi aritou je treba dopsat !!!
+!clearCommand <- -intention(_); -intention(_,_); -intention(_,_,_).

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
+!checkObstacle(X,Y) : obsticle(X,Y) & not obs(X,Y) <- // Nova prekazka
    +obs(X,Y); 
    !sendObsticleInfor(X,Y). 
+!checkObstacle(X,Y). // Prekazka tady neni

// Aktualizace znalosti o zlate
+!checkGold(X,Y) : gold(X,Y) & not res(X,Y,gold) <- // Prvni nalez zlata
    +res(X,Y,gold); 
    !sendResourceInfo(gold,X,Y,add). 
+!checkGold(X,Y) : not gold(X,Y) & res(X,Y,gold) <- // Zlato nekdo vzal
    -res(X,Y,gold); 
    !sendResourceInfo(gold,X,Y,remove). 
+!checkGold(X,Y). // Zlato tady neni

// Aktualizace znalosti o dreve
+!checkWood(X,Y) : wood(X,Y) & not res(X,Y,wood) <- // Prvni nalez dreva
    +res(X,Y,wood); 
    !sendResourceInfo(wood,X,Y,add).
+!checkWood(X,Y) : not wood(X,Y) & res(X,Y,wood) <- // Drevo nekdo vzal
    -res(X,Y,wood); 
    !sendResourceInfo(wood,X,Y,remove). 
+!checkWood(X,Y). // Drevo taky neni


/* ============= AKCE PRO ODESLANI/PRIJMUNI INFOMACI O PROSTORU ============= */

//? Prepsat cilove agenty u ostatni agentu. Nejak pres friend, ale nevim jak 
//  vytahnout oboje hodnoty z baze znalosti
+!sendObsticleInfo(X,Y) <-
    .send(aSlow, achieve, recvObsticleInfo(X,Y));
    .send(aFast, achieve, recvObsticleInfo(X,Y)).

+!sendDiscoverInfo(X,Y) <- 
    .send(aSlow, achieve, recvDiscoverInfo(X,Y));
    .send(aFast, achieve, recvDiscoverInfo(X,Y)).

+!sendResourceInfo(R,X,Y,AddRemove) <-
    .send(aSlow, achieve, recvResourceInfo(R,X,Y,AddRemove));
    .send(aFast, achieve, recvResourceInfo(R,X,Y,AddRemove)).

+!revcObsticleInfo(X,Y) <- +obs(X,Y).

+!recvDiscoverInfo(X,Y) <- -unknown(X,Y).

+!recvResourceInfo(R,X,Y,AddRemove) : AddRemove == add    <- +res(R,X,Y).
+!recvResourceInfo(R,X,Y,AddRemove) : AddRemove == remove <- -res(R,X,Y).

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

