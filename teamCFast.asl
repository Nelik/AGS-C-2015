// !!! Pri kopirovani celeho kodu do jinych agentu je potreba prepsat:       !!!
// !!!  1) pocatecni znalosti range(X)                                       !!!
// !!!  2) commander agent obsahuje akce pro zadavani prikazu                !!!
// !!!                                                                       !!!
// !!!  Fast a Middle jsou temer totozni agenti z pohledu kodu. Slow agent   !!!
// !!!  navic odesila prikazy ostatnim.                                      !!!
/* =========================== POCATECNI ZNALOSTI =========================== */

range(1). // Ulozeni vzdalenosti, protoze implicitne neni ulozena.
commander(aSlow).

// Agent nic nedela, ale aSlow mu na zacatku posle prikaz scout.
intention(idle). // Pocatecni zamer

/* ============================== INICIALIZACE ============================== */
!init.

// Inicializace baze znalosti
@init[atomic] +!init <-
    !initUnknown;
    !lookAround.

// Inicializace nenavstivenych bunek
+!initUnknown : grid_size(GX,GY) & depot(DX,DY) <-
    for (.range(X, 0, GX - 1))
    {
        for (.range(Y, 0, GY - 1))
        {
            +unknown(X,Y);
			+obj(obs, -1, Y);
			+obj(obs, GX, Y);
			+obj(obs, X, -1);
			+obj(obs, X, GY);
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
@macroStep[atomic] +!doMacroStep <- !lookAround; !doIntention.

// Provadeni akci na zaklade aktualniho zameru
+!doIntention : intention(scout)    <- !scout.
+!doIntention : intention(goTo,X,Y) <- !goTo(X,Y).
+!doIntention : intention(pick,X,Y) <- !pick(X,Y).
+!doIntention : intention(unload)   <- !onDepotInit; !unload.
+!doIntention : intention(idle)     <- do(skip).
+!doIntention : true                <- !delete_ws; !chooseNextIntention.

+!chooseNextIntention : unknown(X,Y) <- +intention(scout). // Kdyz nic, tak scout
+!chooseNextIntention : true         <- +intention(idle);.print("idle").

/* ========================== IMPLEMENTACE PRIKAZU ========================== */
// Agent neprve prozkoumava okraj mapy a teprve potom se venuje stredu
// stred agenti projdou castecne pri sbirani surovin
// ignoruje bunky besprostredne u kraje a vybira takove aby videl az do konce plochy
+!scout : .findall(unknown(A,B), (unknown(A,B) & (((A>R & A<GX/4) | (A<GX-R & A<3*GX/4)) & ((B>R & B<GY/4) | (B<GY-R & B<3*GY/4)))), U) & .length(U, L) & L>0 <-
	!getRandomFromFound(U, X, Y);
	-intention(scout); 
    +intention(goTo,X,Y).
// Porad existuji neprozkoumane bunky
+!scout : .findall(unknown(A,B), unknown(A,B), U) & .length(R, L) & L>0 <- 
    !getRandomUnknown(X,Y);
    -intention(scout); 
    +intention(goTo,X,Y).
+!scout : true <- -intention(scout).// Vsechny bunky byly prozkoumany

+!getRandomFromFound(L, X, Y) <-
	.length(L, Length);
	RandIndex = math.round(math.random(Length - 1)); // Nahodne zvolime bunku
    .nth(RandIndex, L, unknown(X,Y)).

// Prikaz k presunu na pozici [X,Y]
+!goTo(X,Y) : pos(X,Y) <- !delete_ws; -intention(goTo,X,Y). // Uz jsme na miste
+!goTo(X,Y) : true     <- !moveTo(X,Y).         // Porad tam nejsme

// Zvednuti zdroje ze zeme (agent musi mit plny pocet pohybovych bodu).
+!pick(X,Y) : pos(X,Y) & ally(X,Y) & moves_left(ML) & moves_per_round(ML) <- 
    !delete_ws;
	do(pick); 
    -intention(pick,X,Y);
    +intention(unload).
+!pick(X,Y) : pos(X,Y) <- do(skip). // Cekani na jineho agenta
+!pick(X,Y) : true     <- !moveTo(X,Y).

// Vyprazdneni agenta (agent musi mit plny pocet pohybovych bodu).
+!unload : onDepot(true) & moves_left(ML) & moves_per_round(ML) & commander(C) & .my_name(MN) <- 
    do(drop); 
	!delete_ws;
    -intention(unload);
    .send(C, achieve, commandDone(MN)).
+!unload : onDepot(true)  <- !delete_ws; do(skip).
+!unload : onDepot(false) <- !moveToDepot.

/* ============================ PRIJMUTI PRIKAZU ============================ */

@intScout[atomic]  +!intentionScout     <- !clearIntention; +intention(scout).
@intGoTo[atomic]   +!intentionGoTo(X,Y) <- !clearIntention; +intention(goTo,X,Y).
@intPick[atomic]   +!intentionPick(X,Y) <- !clearIntention; +intention(pick,X,Y).
@intUnload[atomic] +!intentionUnload    <- !clearIntention; +intention(unload).
@intIdle[atomic]   +!intentionIdle      <- !clearIntention; +intention(idle).

// Odstraneni aktualniho zameru
// !!! Pokud pribudou nove zamery s vetsi aritou je treba dopsat !!!
+!clearIntention <- !delete_ws; -intention(_); -intention(_,_); -intention(_,_,_).

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
+!checkObstacle(X,Y) : obstacle(X,Y) & not obj(obs,X,Y) & intention(_, X, Y) <- // Nova prekazka
    +obj(obs,X,Y); 
	!chooseNextIntention;
    !sendObjectInfo(obs,X,Y,add).
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
+!moveTo(TarX,TarY) : pos(PosX,PosY) 
	<- if(was_there(TarX, TarY)){!delete_ws}; 
	!moveTo(PosX,PosY,TarX,TarY).

// Jsme na miste
+!moveTo(PosX,PosY,TarX,TarY) : PosX == TarX & PosY == TarY <- !delete_ws. 


+!moveTo(PosX,PosY,TarX,TarY) : not was_there(PosX + 1, PosY) & PosX < TarX 
	& not obj(obs,PosX + 1, PosY) <- !my_do(right); -rounding(_); +rounding("R").
	
+!moveTo(PosX,PosY,TarX,TarY) : not was_there(PosX - 1, PosY) & PosX > TarX 
	& not obj(obs,PosX - 1, PosY) <- !my_do(left); -rounding(_); +rounding("L").
	
+!moveTo(PosX,PosY,TarX,TarY) : not was_there(PosX, PosY + 1) & PosY < TarY 
	& not obj(obs,PosX, PosY + 1) <- !my_do(down); -rounding(_); +rounding("D").
	
+!moveTo(PosX,PosY,TarX,TarY) : not was_there(PosX, PosY - 1) & PosY > TarY 
	& not obj(obs,PosX, PosY-1) <- !my_do(up);	-rounding(_); +rounding("U").
	
+!moveTo(PosX,PosY,TarX,TarY) : true <- !roundBar(PosX, PosY, TarX, TarY).

/*======================= OBCHAZENI PREKAZKY ================================ */
// Obchazime prekazku smerem dolu, vime ze nemuzeme jit ve smeru cile doleva/doprava
+!roundBar(PosX, PosY, TarX, TarY): rounding("D") 
	& not was_there(PosX, PosY+1)  
	& not obj(obs,PosX, PosY+1) 
	<- .print ("Obchazim prekazku dolu pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY);
	!my_do(down).

// Obchazime prekazku smerem dolu, vime ze nemuzeme jit ve smeru cile doleva/doprava
+!roundBar(PosX, PosY, TarX, TarY): rounding("D") 
	& not was_there(PosX, PosY+2) & not obj(obs,PosX, PosY+2)  
	& not obj(obs,PosX, PosY+1) 
	<- .print ("Obchazim prekazku dolu2 pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY); 
	!my_do(down).
	
+!roundBar(PosX, PosY, TarX, TarY): rounding("U") 
	& not was_there(PosX, PosY-1)
	& not obj(obs,PosX, PosY-1) 
	<- .print ("Obchazim prekazku nahoru pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY); 
	!my_do(up).
	
+!roundBar(PosX, PosY, TarX, TarY): rounding("U") 
	& not was_there(PosX, PosY-2) & not obj(obs,PosX, PosY-2) 
	& not obj(obs,PosX, PosY-1) 
	<- .print ("Obchazim prekazku nahoru2 pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY); 
	!my_do(up).
	
+!roundBar(PosX, PosY, TarX, TarY): (rounding("U") | rounding("D")) 
	& not was_there(PosX-1, PosY)
	& not obj(obs,PosX-1, PosY) 
	<- -rounding(_); +rounding("L"); .print ("Obchazim prekazku doleva z obchazeni U/D pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY);
	!my_do(left).
	
+!roundBar(PosX, PosY, TarX, TarY): (rounding("U") | rounding("D")) 
	& not was_there(PosX+1, PosY)
	& not obj(obs,PosX+1, PosY) 
	<- -rounding(_); +rounding("R"); .print ("Obchazim prekazku doprava z U/D pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY); 
	!my_do(right).

+!roundBar(PosX, PosY, TarX, TarY): rounding("D")
	& not obj(obs,PosX, PosY+1) 
	<- .print ("Obchazim prekazku dolu3 pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY);
	!my_do(down).
	
+!roundBar(PosX, PosY, TarX, TarY): rounding("U") 
	& not obj(obs,PosX, PosY-1) 
	<- .print ("Obchazim prekazku nahoru3 pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY);
	!my_do(up).

// Obchazime zleva, pokracujeme doleva, pokud muzeme
+!roundBar(PosX, PosY, TarX, TarY): rounding("L") 
	& not was_there(PosX-1, PosY)
	& not obj(obs,PosX - 1, PosY) 
	<- .print ("Obchazim prekazku doleva pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY); 
	!my_do(left).
	
// Obchazime zleva, pokracujeme doleva, pokud muzeme
+!roundBar(PosX, PosY, TarX, TarY): rounding("L") 
	& not was_there(PosX-2, PosY) & not obj(obs,PosX-2, PosY)
	& not obj(obs,PosX - 1, PosY) 
	<- .print ("Obchazim prekazku doleva2 pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY); 
	!my_do(left).

// Obchazime zprava, pokracujeme doprava, pokud muzeme
+!roundBar(PosX, PosY, TarX, TarY): rounding("R") 
	& not was_there(PosX+1, PosY)
	& not obj(obs,PosX+1, PosY) 
	<- .print ("Obchazim prekazku doprava pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY); 
	!my_do(right).
	
+!roundBar(PosX, PosY, TarX, TarY): rounding("R") 
	& not was_there(PosX+2, PosY) & not obj(obs,PosX+2, PosY)
	& not obj(obs,PosX+1, PosY) 
	<- .print ("Obchazim prekazku doprava2 pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY); 
	!my_do(right).
	
+!roundBar(PosX, PosY, TarX, TarY): (rounding("L") | rounding("R")) 
	& not was_there(PosX, PosY-1)
	& not obj(obs,PosX, PosY-1) 
	<- -rounding(_); +rounding("U"); .print ("Obchazim prekazku dolu z L/R pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY); 
	!my_do(up).
	
+!roundBar(PosX, PosY, TarX, TarY): (rounding("L") | rounding("R"))
	& not was_there(PosX, PosY+1)
	& not obj(obs,PosX, PosY+1) 
	<- -rounding(_); +rounding("D"); .print ("Obchazim prekazku nahoru z L/R pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY);
	!my_do(down).
	
+!roundBar(PosX, PosY, TarX, TarY): rounding("L") 
	& not obj(obs,PosX - 1, PosY) 
	<- .print ("Obchazim prekazku doleva3 pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY);
	!my_do(left).

// Obchazime zprava, pokracujeme doprava, pokud muzeme
+!roundBar(PosX, PosY, TarX, TarY): rounding("R") 
	& not obj(obs,PosX + 1, PosY) 
	<- .print ("Obchazim prekazku doprava3 pozice: ", PosX, " ", PosY, " tar: ", TarX, TarY);
	!my_do(right).
	
// Obchazime prekazku zleva/zprava, ale tam nemuzeme jit,
// rozhodujeme se tedy jit nahoru, dolu?
+!roundBar(PosX, PosY, TarX, TarY): rounding(_) 
	<- -rounding(_);
	-was_there(PosX+1, PosY); -was_there(PosX, PosY+1); 
	-was_there(PosX-1, PosY); -was_there(PosX, PosY-1);
	!moveTo(PosX, PosY, TarX, TarY).


/***************** Narazili jsme poprve prekazku ******************************/
// Jsme ve spravne Y souradnici, ale potrebujeme obejit prekazku - musime
// tedy jit vlevo nebo vpravo
+!roundBar(PosX, PosY, TarX, TarY): PosY == TarY
	<- !decide(up_down, PosX, PosY, TarX, TarY).
	
+!roundBar(PosX, PosY, TarX, TarY): PosX == TarX 
	<- !decide(left_right, PosX, PosY, TarX, TarY).
	
// Cil vpravo-nahore/dole ale tam nemuzeme jit, protoze jsme tam bud
// byli nebo je tam prekazka - zkusime nejdrive doleva a potom dolu/nahoru
+!roundBar(PosX, PosY, TarX, TarY): PosX < TarX
	& not was_there(PosX - 1, PosY) & not obj(obs,PosX - 1, PosY) 
	<- +rounding("L"); !my_do(left).
+!roundBar(PosX, PosY, TarX, TarY): PosX < TarX & PosY > TarY
	& not was_there(PosX, PosY+1) & not obj(obs,PosX, PosY + 1) 
	<- +rounding("D"); !my_do(down).
+!roundBar(PosX, PosY, TarX, TarY): PosX < TarX & PosY < TarY
	& not was_there(PosX, PosY-1) & not obj(obs,PosX, PosY - 1) 
	<- +rounding("U"); !my_do(up).
	
// Cil vlevo-nahore/dole ale tam nemuzeme jit, protoze jsme tam bud
// byli nebo je tam prekazka - zkusime nejdrive dolprava a potom dolu/nahoru
+!roundBar(PosX, PosY, TarX, TarY): PosX > TarX
	& not was_there(PosX + 1, PosY) & not obj(obs,PosX + 1, PosY) 
	<- +rounding("R"); !my_do(right).
+!roundBar(PosX, PosY, TarX, TarY): PosX > TarX & PosY > TarY
	& not was_there(PosX, PosY+1) & not obj(obs,PosX, PosY+1) 
	<- +rounding("D"); !my_do(down).
+!roundBar(PosX, PosY, TarX, TarY): PosX > TarX & PosY < TarY
	& not was_there(PosX, PosY-1) & not obj(obs,PosX, PosY-1) 
	<- +rounding("U"); !my_do(up).
	
// Zkusili jsme vsechny smery a nic - vymazeme ze jsme byli v nejblizsim okoli
// a zkusime se znovu pohnout
/*+!roundBar(PosX, PosY, TarX, TarY) <- 
	-was_there(PosX+1, PosY); -was_there(PosX, PosY+1); 
	-was_there(PosX-1, PosY); -was_there(PosX, PosY-1);
	!moveTo(PosX, PosY, TarX, TarY).*/	

/*============================================================================*/
// Pred dosazenim cile, ukladam pozice, kde jsme byli, abychom se nevraceli.
+!my_do(X): pos(PosX, PosY) <- +was_there(PosX, PosY); do(X).
// Jen pro jistotu  - ale nemeli bychom se tady nikdy dostat
+!my_do(X) <- do(X); .print("Divne, tady nikdy nemame byt.").

	
// PosX a PosY - aktualni pozice, X, Y - policko, kde jsme byli predtim

// Prisli jsme shora -> nepujdeme znova nahoru, ale jdeme dolu
+!decide(up_down, PosX, PosY, TarX, TarY): not was_there(PosX, PosY - 1)
	& not obj(obs, PosX, PosY - 1)
	<- !my_do(up); if (PosY <= TarY){+rounding("U")}.

// Prisli jsme zdola -> nepujdeme znova dolu, ale jdeme nahoru	
+!decide(up_down, PosX, PosY, TarX, TarY): not was_there(PosX, PosY + 1) 
	& not obj(obs, PosX, PosY + 1)
	<- !my_do(down); if (PosY >= TarY){+rounding("D")}.

+!decide(up_down, PosX, PosY, TarX, TarY) 
	<- !decide2(left_right, PosX, PosY, TarX, TarY).


// Prisli jsme zprava -> nepujdeme znova doprava, ale jdeme doleva
+!decide(left_right, PosX, PosY, TarX, TarY): not was_there(PosX - 1, PosY) 
	& not obj(obs, PosX - 1, PosY)
	<- !my_do(left); if (PosX <= TarX) {+rounding("L")}.	

// Prisli jsme zleva -> nepujdeme znova doleva, ale jdeme doprava
+!decide(left_right, PosX, PosY, TarX, TarY): not was_there(PosX + 1, PosY) 
	& not obj(obs, PosX + 1, PosY)
	<- !my_do(right); if (PosX >= TarX) {+rounding("R")}.	

+!decide(left_right, PosX, PosY, TarX, TarY)
	<- !decide2(up_down, PosX, PosY, TarX, TarY).
	
//------------------- Decide 2 -----------------------------------------------//
// Prisli jsme shora -> nepujdeme znova nahoru, ale jdeme dolu
+!decide2(up_down, PosX, PosY, TarX, TarY): not was_there(PosX, PosY - 1)
	& not obj(obs, PosX, PosY - 1)
	<- !my_do(up); if (PosY <= TarY){+rounding("U")}.

// Prisli jsme zdola -> nepujdeme znova dolu, ale jdeme nahoru	
+!decide2(up_down, PosX, PosY, TarX, TarY): not was_there(PosX, PosY + 1) 
	& not obj(obs, PosX, PosY + 1)
	<- !my_do(down); if (PosY >= TarY){+rounding("D")}.
	
// Prisli jsme zprava -> nepujdeme znova doprava, ale jdeme doleva
+!decide2(left_right, PosX, PosY, TarX, TarY): not was_there(PosX - 1, PosY) 
	& not obj(obs, PosX - 1, PosY)
	<- !my_do(left); if (PosX <= TarX) {+rounding("L")}.	

// Prisli jsme zleva -> nepujdeme znova doleva, ale jdeme doprava
+!decide2(left_right, PosX, PosY, TarX, TarY): not was_there(PosX + 1, PosY) 
	& not obj(obs, PosX + 1, PosY)
	<- !my_do(right); if (PosX >= TarX) {+rounding("R")}.	

/*// Zkusili jsme vsechny smery a nic - vymazeme ze jsme byli v nejblizsim okoli
// a zkusime se znovu pohnout
+!decide2(_, PosX, PosY, TarX, TarY): PosX == TarX | PosY == TarY <-
	-was_there(PosX+1, PosY); -was_there(PosX, PosY+1); 
	-was_there(PosX-1, PosY); -was_there(PosX, PosY-1);
	!moveTo(PosX, PosY, TarX, TarY).*/
// Zkusili jsme vsechny smery a nic - vymazeme ze jsme byli v nejblizsim okoli
// a zkusime se znovu pohnout
+!decide2(_, PosX, PosY, TarX, TarY) <- 
	-was_there(PosX+1, PosY); -was_there(PosX, PosY+1); 
	-was_there(PosX-1, PosY); -was_there(PosX, PosY-1);//!delete_ws;
	!moveTo(PosX, PosY, TarX, TarY).

//------------------- Konec Decide 2 -----------------------------------------//	
+!decide(left_right, PosX, PosY, TarX, TarY) 
	<- .print("Tady bychom se nemeli nikdy ocitnout :-D.").
+!decide(up_down, PosX, PosY, TarX, TarY) 
	<- .print("Tady bychom se nemeli nikdy ocitnout :-D.").
	
+!delete_ws: was_there(_, _) <- -was_there(_, _); !delete_ws.
+!delete_ws.

