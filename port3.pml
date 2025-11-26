mtype = {
    /* Dock */
    REQ_DOCK, ACQUIRE_DOCK, GRANT_DOCK, RELEASE_DOCK,

    /* Crane */
    REQ_CRANE, ACQUIRE_CRANE, GRANT_CRANE, RELEASE_CRANE
};
chan reqDock       = [2] of { mtype, byte };          // ship -> port
chan dockAcquire   = [2] of { mtype, byte };          // port -> dock
chan dockGranted   = [2] of { mtype, byte };          // dock -> port (dockId)
chan grantDock     = [2] of { mtype, byte, byte };    // port -> ship (shipId, dockId)

chan reqCrane      = [2] of { mtype, byte };
chan craneAcquire  = [2] of { mtype, byte };
chan craneGranted  = [2] of { mtype, byte };
chan grantCrane    = [2] of { mtype, byte, byte };

chan releaseDock   = [2] of { mtype, byte };
chan releaseCrane  = [2] of { mtype, byte };



proctype Dock(byte id)
{
    byte ship;

Start:
    atomic {
        if
        :: dockAcquire?ACQUIRE_DOCK, ship ->
                goto HandleAcquire

        :: releaseDock?RELEASE_DOCK, ship ->
                goto HandleRelease
        fi
    }

    goto Start;


/* ----------------------------------------------------------- */

HandleAcquire:
    dockGranted!GRANT_DOCK, id;
    goto Start;

HandleRelease:
    /* Reset / free dock */
    goto Start;
}


proctype Crane(byte id)
{
    byte ship;

Start:
    atomic {
        if
        :: craneAcquire?ACQUIRE_CRANE, ship ->
                goto HandleAcquire

        :: releaseCrane?RELEASE_CRANE, ship ->
                goto HandleRelease
        fi
    }

    goto Start;


/* ----------------------------------------------------------- */

HandleAcquire:
    craneGranted!GRANT_CRANE, id;
    goto Start;

HandleRelease:
    /* Reset / free crane */
    goto Start;
}


proctype Port()
{
    byte ship;
    byte dockId;
    byte craneId;

Start:
    atomic {
        if
        :: reqDock?REQ_DOCK, ship ->
                goto HandleReqDock

        :: dockGranted?GRANT_DOCK, dockId ->
                goto HandleDockGranted

        :: reqCrane?REQ_CRANE, ship ->
                goto HandleReqCrane

        :: craneGranted?GRANT_CRANE, craneId ->
                goto HandleCraneGranted

        :: releaseCrane?RELEASE_CRANE, craneId ->
                goto HandleReleaseCrane

        fi
    }

    goto Start;     /* cycle */
    

/* ----- Sub-states ------------------------------------------- */

HandleReqDock:
    /* Accept request and forward to a dock */
    dockAcquire!ACQUIRE_DOCK, ship;
    goto Start;


HandleDockGranted:
    /* Forward dock to the ship */
    grantDock!GRANT_DOCK, ship, dockId;
    goto Start;


HandleReqCrane:
    craneAcquire!ACQUIRE_CRANE, ship;
    goto Start;


HandleCraneGranted:
    grantCrane!GRANT_CRANE, ship, craneId;
    goto Start;


HandleReleaseCrane:
    /* eventual bookkeeping, simplified */
    goto Start;
}


proctype Ship(byte id) {
    byte dockId, craneId;

    Start: atomic {
        reqDock ! REQ_DOCK, 1;
        goto Next1
    }
    Next1: atomic {
        grantDock ? GRANT_DOCK, 1, dockId;
        goto Next2
    }
    Next2: atomic {
        reqCrane ! REQ_CRANE, 1;
        goto Next3
    }
    Next3: atomic {
        grantCrane ? GRANT_CRANE, 1, craneId;
        goto Next4
    }
    Next4: atomic {
        releaseCrane ! RELEASE_CRANE, craneId;
        goto Next5
    }
    Next5: atomic {
        releaseDock ! RELEASE_DOCK, dockId;
    }
}


init {
    run Port();
    run Dock(1); run Dock(2);
    run Crane(1); run Crane(2);
    run Ship(1);
    run Ship(2);
}
