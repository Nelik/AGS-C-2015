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
        //.send(Agent, achieve, Action);
    }.

// Temer zbytecne akce, rovnou by slo psat sendAchieveToAll
+!sendDiscoverInfo(X,Y) <- !sendAchieveToAll(recvDiscoverInfo(X,Y)).
+!sendObjectInfo(O,X,Y,AddRemove) <- !sendAchieveToAll(recvObjectInfo(O,X,Y,AddRemove)).

// Reakce na objeveni bunky
+!recvDiscoverInfo(X,Y) <- -unknown(X,Y).

// Reakce na objeveni zdroje
+!recvObjectInfo(O,X,Y,AddRemove) : AddRemove == add    <- +obj(O,X,Y).
+!recvObjectInfo(O,X,Y,AddRemove) : AddRemove == remove <- -obj(O,X,Y).


/* ================================= TESTY ================================== */
+!nodeTest(Node) <-
	.length(Node, NL);
	.nth(0, Node, NodeX);
	.nth(1, Node, NodeY);
	.nth(2, Node, PNodeX);
	.nth(3, Node, PNodeY);
	.nth(4, Node, Gn);
	.nth(5, Node, Fn).

+!aStarInitTest <-
	.findall([X,Y,Px,Py,G,F], openSet(X,Y,Px,Py,G,F), OpenSet);
	.findall([X,Y,Px,Py,G,F], closedSet(X,Y,Px,Py,G,F), ClosedSet);
	.length(OpenSet, OL);
	.nth(0, OpenSet, Node);
	!nodeTest(Node);
	.length(ClosedSet, CL).
	
+!aStarLowestNodeTest(Node) <-
	!nodeTest(Node).
	
+!aStarNeighborsTest(Neighbors) <-
	.length(Neighbors, L);
	for(.range(X, 0, L-1))
	{
		.nth(X, Neighbors, Node);
		!nodeTest(Node);
	}.
/* ================================= HELPERS ================================ */	
+!getNodeValuesHelper(Node,X,Y,Px,Py,G,F) <-
	.nth(0, Node, X);
	.nth(1, Node, Y);
	.nth(2, Node, Px);
	.nth(3, Node, Py);
	.nth(4, Node, G);
	.nth(5, Node, F).
	
+!getCurrentNodeHelper(CurrentNode): currentNode(Cnx, Cny, Cnpx, Cnpy, Cng, Cnf) <-
	CurrentNode = [Cnx, Cny, Cnpx, Cnpy, Cng, Cnf].
	
/* ================================= POHYB ================================== */

// Pohyb k depu
+!moveToDepot : depot(DX, DY) <- !moveTo(DX,DY).

+!heuristic(NodeX, NodeY, Return) : aStarGoal(GoalX, GoalY) <-
	Dx = math.abs(NodeX - GoalX);
	Dy = math.abs(NodeY - GoalY);
	D = 1;
	Return = D * (Dx + Dy).
	
+!aStarInit(Sx, Sy) <-
	!heuristic(Sx, Sy, H);
	G = 0;
	F = G + H;
	+openSet(Sx,Sy,Sx,Sy,G,F).

+!getLowestRank <- 
	.findall([X,Y,Px,Py,G,F], openSet(X,Y,Px,Py,G,F), OpenSet);
	.length(OpenSet, OsLength);
	for (.range(X, 0, OsLength-1))
	{
		.nth(X, OpenSet, ENode);
		!getNodeValuesHelper(ENode, Nx, Ny, Npx, Npy, Ng, Nf);
		if (X == 0)
		{
			+lowestFn(Nf); +currentNodePosition(Nx, Ny); +currentNode(Nx, Ny, Npx, Npy, Ng, Nf);
		}
		else
		{
			?lowestFn(Lfn);
			if (Lfn > Nf)
			{
				-lowestFn(_); -currentNodePosition(_,_); -currentNode(_,_,_,_,_,_);
				+lowestFn(Nf); +currentNodePosition(Nx, Ny); +currentNode(Nx, Ny, Npx, Npy, Ng, Nf);
			}
		}
	}
	.abolish(lowestFn(_));
	.
	
+!getNeigborsOfCurrent(Current, Neighbors): grid_size(GX, GY) <-
	.nth(0, Current, CurrentX);
	.nth(1, Current, CurrentY);
	?aStarGoal(GoalX, GoalY);
	for(.range(X, CurrentX-1, CurrentX+1))
	{
		if (not obj(obs, X, CurrentY) & X \==CurrentX & X >= 0 & X < GX)
		{
			+neighbor(X, CurrentY, CurrentX, CurrentY);
		}
	}
	for(.range(Y, CurrentY-1, CurrentY+1))
	{
		if(not obj(obs, CurrentX, Y) & Y \== CurrentY & Y >= 0 & Y < GY)
		{
			+neighbor(CurrentX,Y, CurrentX, CurrentY);
		}
	}
	if (obj(obs, GoalX, GoalY))
	{
		.println("Goal is obstacle!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
		.drop_all_events;
		.drop_all_desires;
		.drop_all_intentions;
		.abolish(neighbor(_,_,_,_));
		.abolish(openSet(_,_,_,_,_,_));
		.abolish(closedSet(_,_,_,_,_,_));
		-lowestFn(_); -currentNodePosition(_,_); -currentNode(_,_,_,_,_,_);
		-actualX(_);
		-actualY(_);
		-continue(_);
		-aStarGoal(_,_);
		-subStepDone(_);
		!intentionScout;
	}
	.findall([X,Y,Px,Py,0,0],neighbor(X,Y,Px,Py), Neighbors);
	.abolish(neighbor(_,_,_,_)).

+!aStar(Sx, Sy, Gx, Gy) <-
	!aStarInit(Sx, Sy);
	.println("aStar");
	// while lowest rank in OPEN is not the GOAL
	+continue(1);
	while(continue(1)){
		!getLowestRank;
		-continue(_);
		?aStarGoal(TarX, TarY);
		?currentNodePosition(Nx, Ny);
		if (TarX == Nx & TarY == Ny)
		{
			.println("Do NOT continue!!");
			+continue(0);		
		}
		else
		{
			.println("Do continue!!");
			+continue(1);
		}
		if (continue(1)){
			?currentNode(Cnx, Cny, Cnpx, Cnpy, Cng, Cnf);
			-openSet(Cnx, Cny, Cnpx, Cnpy, Cng, Cnf); // remove lowest rank node from OPEN
			+closedSet(Cnx, Cny, Cnpx, Cnpy, Cng, Cnf); // add current to CLOSED
			!getCurrentNodeHelper(CurrentNode);
			!getNeigborsOfCurrent(CurrentNode, Neighbors);
			.nth(4, CurrentNode, CurrentCost);
			Cost = CurrentCost + 1; // 1 is movementCost which is always 1
			.length(Neighbors, NeiLength);
			for(.range(X, 0, NeiLength - 1))
			{
				.nth(X, Neighbors, Neighbor);

				!getNodeValuesHelper(Neighbor, Neix, Neiy, Neipx, Neipy, Ng, Nf);
				if (openSet(Neix, Neiy, _, _, _, _)) //if neighbor in OPEN
				{
					if(Cost < CostG)
					{
						//remove neighbor from OPEN, because new path is better
						//.println("remove neighbor from OPEN, because new path is better");
						-openSet(Neix, Neiy, Neipx, Neipy, _, _);
					}
				}
				if (closedSet(Neix, Neiy, _, _, _, _)) //if neighbor in CLOSED
				{
					if(Cost < Ng)
					{
						//remove neighbor from CLOSED
						//.println("remove neighbor from CLOSED");
						-closedSet(Neix, Neiy, _, _, Ng, _);
					}
				}
				if (not (openSet(Neix, Neiy, _, _, _, _) | closedSet(Neix, Neiy, _, _, _, _)))
				{
					//if neighbor not in OPEN and neighbor not in CLOSED:
					//set g(neighbor) to cost
					!heuristic(Neix, Neiy, H);
					NewF = Cost + H; //set priority queue rank to g(neighbor) + h(neighbor)
					//set neighbor's parent to current
					//add neighbor to OPEN
					+openSet(Neix, Neiy, Cnx, Cny, Cost, NewF);
				}
			}
		}
		-currentNodePosition(_,_); -currentNode(_,_,_,_,_,_);
	}
	// reconstruct reverse path from goal to start by following parent pointers
	.println("Now I should reconstruct my path...");
	+continue(1);
	?aStarGoal(TarX, TarY);
	?pos(PosX, PosY);
	+actualX(PosX);
	+actualY(PosY);
	.findall([X,Y,PX,PY], closedSet(X,Y,PX,PY,_,_), PP);
	while(continue(1))	
	{
		?actualX(Ax); ?actualY(Ay);
		if(closedSet(Px, Py, Ax, Ay, _, _)){
			-closedSet(Px, Py, Ax, Ay, _, _);
			+path(Px,Py);
			-actualX(_);
			-actualY(_);
			+actualX(Px);
			+actualY(Py);
			if (Px == TarX & Py == TarY)
			{
				-continue(_);
				+continue(0);
			}
		}
		else
		{
			+path(TarX, TarY);
			-continue(_);
			+continue(0);
		}
	}
	.abolish(openSet(_,_,_,_,_,_));
	.abolish(closedSet(_,_,_,_,_,_));
	-lowestFn(_); -currentNodePosition(_,_); -currentNode(_,_,_,_,_,_);
	-actualX(_);
	-actualY(_);
	-continue(_);
	-aStarGoal(_,_);
	.findall([X,Y], path(X,Y), ReversedPath);
	.reverse(ReversedPath, Path);
	.println("Path: ", Path);
	.abolish(path(_,_));
	//-aStarDone(_);
	//+aStarDone(1);
	//.length(Path, PL);
	//for(.range(P, 0, PL - 1))
	//{
	//}.
	.nth(0, Path, PathPoint);
	.nth(0, PathPoint, NewX);
	.nth(1, PathPoint, NewY);
	?pos(ActualX, ActualY);
	if (ActualX == NewX & ActualY == NewY)
	{
		.delete(0, Path, Path1);
		.nth(0, Path1, PathPoint1);
		.nth(0, PathPoint1, NewX1);
		.nth(1, PathPoint1, NewY1);
		!moveTo(ActualX,ActualY,NewX1,NewY1);
	}
	else
	{
		!moveTo(ActualX,ActualY,NewX,NewY);
	}
	//+intention(goTo, NewX, NewY);
	.


// Pohyb na [X,Y] bunku
// calculate destination angle
//+!moveTo(TarX,TarY) : pos(PosX,PosY) & aStarDone(0) <- +aStarGoal(TarX, TarY); !aStar(PosX,PosY,TarX,TarY).
//+!moveTo(TarX,TarY) : pos(PosX,PosY) & aStarDone(1) <- !moveTo(PosX, PosY, TarX, TarY).
//+!moveTo(PosX,PosY,TarX,TarY) : PosX < TarX <- !tangBug(right,TarX,TarY); !onDepotInit.
//+!moveTo(PosX,PosY,TarX,TarY) : PosX > TarX <- !tangBug(left,TarX,TarY); !onDepotInit.
//+!moveTo(PosX,PosY,TarX,TarY) : PosY < TarY <- !tangBug(down,TarX,TarY); !onDepotInit.
//+!moveTo(PosX,PosY,TarX,TarY) : PosY > TarY <- !tangBug(up,TarX,TarY); !onDepotInit.
// Uz jsem na miste: PosX ==  TarX & PosY == TarY
+!moveTo(TarX,TarY) : pos(PosX,PosY) <- +aStarGoal(TarX, TarY); !aStar(PosX,PosY,TarX,TarY).
+!moveTo(PosX,PosY,TarX,TarY) : PosX < TarX <- do(right); !onDepotInit.
+!moveTo(PosX,PosY,TarX,TarY) : PosX > TarX <- do(left); !onDepotInit.
+!moveTo(PosX,PosY,TarX,TarY) : PosY < TarY <- do(down); !onDepotInit.
+!moveTo(PosX,PosY,TarX,TarY) : PosY > TarY <- do(up); !onDepotInit.
//+!moveTo(PosX,PosY,TarX,TarY). // Uz jsem na miste: PosX == TarX & PosY == TarY
+!moveTo(PosX,PosY,TarX,TarY) <- !onDepotInit.

