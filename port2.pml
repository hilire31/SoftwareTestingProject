#define ND 2      /* number of docks */
#define NC 2      /* number of cranes */

chan reqDock = [2] of { byte };         /* ship → port */
chan dockAcquire = [2] of { byte };     /* port → dock (sends ship id as byte) */
chan dockGranted = [2] of { byte };     /* dock → port (dockId) */
chan grantDock = [2] of { byte, byte }; /* port → ship */

chan reqCrane = [2] of { byte };
chan craneAcquire = [2] of { byte };
chan craneGranted = [2] of { byte };
chan grantCrane = [2] of { byte, byte };

chan releaseDock = [2] of { byte };   /* ship → port */
chan releaseCrane = [2] of { byte };

/********************  DOCK  *************************/
proctype Dock(byte id) {
    bool free = true;
    byte id2;
    byte msg;
    do
    :: dockAcquire ? msg ->
        if
        :: free ->
            free = false;
            dockGranted ! id;
        :: else ->
            skip;
        fi
    :: releaseDock ? id2 ->
        if
        :: id2 == id ->
            free = true;
        :: else -> skip;
        fi
    od
}

/********************  CRANE  *************************/
proctype Crane(byte id) {
    bool free = true;
    byte id2;
    byte msg;
    do
    :: craneAcquire ? msg ->
        if
        :: free ->
            free = false;
            craneGranted ! id;
        :: else -> skip;
        fi
    :: releaseCrane ? id2 ->
        if
        :: id2 == id ->
            free = true;
        :: else -> skip;
        fi
    od
}

/********************  PORT  *************************/
proctype Port() {
    byte ship;
    byte resourceId;

    do
    /* --- Docking --- */
    :: reqDock ? ship ->
        dockAcquire ! ship;
        dockGranted ? resourceId;
        grantDock ! ship, resourceId;

    :: releaseDock ? resourceId ->
        releaseDock ! resourceId;

    /* --- Crane --- */
    :: reqCrane ? ship ->
        craneAcquire ! ship;
        craneGranted ? resourceId;
        grantCrane ! ship, resourceId;

    :: releaseCrane ? resourceId ->
        releaseCrane ! resourceId;
    od
}

/********************  SHIP 1  *************************/
proctype Ship1() {
    byte dockId, craneId;
    byte sender;

    reqDock ! 1;
    grantDock ? sender, dockId;

    reqCrane ! 1;
    grantCrane ? sender, craneId;

    /* use crane */
    releaseCrane ! craneId;
    releaseDock ! dockId;
}

/********************  SHIP 2  *************************/
proctype Ship2() {
    byte dockId, craneId;
    byte sender;

    reqDock ! 2;
    grantDock ? sender, dockId;

    reqCrane ! 2;
    grantCrane ? sender, craneId;

    /* use crane */
    releaseCrane ! craneId;
    releaseDock ! dockId;
}

/********************  INIT  *************************/
init {
    atomic {
        run Port();
        run Dock(1); run Dock(2);
        run Crane(1); run Crane(2);
        run Ship1();
        run Ship2();
    }
}
