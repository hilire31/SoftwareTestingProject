bool dockFree[2];
bool craneFree[2];

bool ship1_docked = false;
bool ship2_docked = false;

bool ship1_usingCrane = false;
bool ship2_usingCrane = false;

bool ship1_departed = false;
bool ship2_departed = false;

chan reqDock = [2] of { byte };
chan reqCrane = [2] of { byte };
chan grantDock = [2] of { byte, byte }; /* ship, dockId */
chan grantCrane = [2] of { byte, byte }; /* ship, craneId */
chan releaseDock = [2] of { byte }; /* dockId */
chan releaseCrane = [2] of { byte }; /* craneId */

/* PORT */
proctype Port() {
    byte ship;
    do
    :: reqDock ? ship ->
        /* choose first free dock (1 or 2) and grant it to requesting ship */
        if
        :: dockFree[0] ->
            dockFree[0] = false;
            grantDock ! ship, 1;
        :: dockFree[1] ->
            dockFree[1] = false;
            grantDock ! ship, 2;
        :: else -> skip;
        fi
    :: releaseDock ? ship ->
        /* releaseDock carries dockId */
        dockFree[ship-1] = true;

    :: reqCrane ? ship ->
        /* choose first free crane and grant it to requesting ship */
        if
        :: craneFree[0] ->
            craneFree[0] = false;
            grantCrane ! ship, 1;
        :: craneFree[1] ->
            craneFree[1] = false;
            grantCrane ! ship, 2;
        :: else -> skip;
        fi
    :: releaseCrane ? ship ->
        /* releaseCrane carries craneId */
        craneFree[ship-1] = true;
    od
    

}

/* SHIP 1 */
proctype Ship1() {
    byte dockId;
    byte craneId;
    reqDock ! 1;
    grantDock ? 1, dockId; /* receive (ship, dockId) */
    ship1_docked = true;

    reqCrane ! 1;
    grantCrane ? 1, craneId; /* receive (ship, craneId) */
    ship1_usingCrane = true;

    /* use crane */
    ship1_usingCrane = false;
    releaseCrane ! craneId;
    releaseDock ! dockId;
    ship1_docked = false;
    ship1_departed = true;
}

/* SHIP 2 */
proctype Ship2() {
    byte dockId;
    byte craneId;
    reqDock ! 2;
    grantDock ? 2, dockId;
    ship2_docked = true;

    reqCrane ! 2;
    grantCrane ? 2, craneId;
    ship2_usingCrane = true;

    /* use crane */
    ship2_usingCrane = false;
    releaseCrane ! craneId;
    releaseDock ! dockId;
    ship2_docked = false;
    ship2_departed = true;
}

/* ---------- INITIALISATION + VÉRIFICATIONS ---------- */
init {
    atomic {
        /* initialisation des ressources */
        dockFree[0] = true;
        dockFree[1] = true;
        craneFree[0] = true;
        craneFree[1] = true;

        run Port();
        run Ship1();
        run Ship2();
    }

    /* Boucle de surveillance continue */
    do
    :: true ->
        /* Vérifications de sûreté */

        /* Exclusion mutuelle sur le dock */
        assert(!(ship1_docked && ship2_docked));

        /* Exclusion mutuelle sur la grue */
        assert(!(ship1_usingCrane && ship2_usingCrane));

        /* Cohérence d’état : on ne peut pas utiliser la grue sans être docké */
        assert(!ship1_usingCrane || ship1_docked);
        assert(!ship2_usingCrane || ship2_docked);

        /* Vérifications de vivacité (approximées via assertions temporelles) */
        /* On vérifie que chaque navire finit par partir au moins une fois */
        if
        :: (ship1_departed && ship2_departed) ->
            printf("Les deux navires ont terminé sans interblocage.\n");
            break;
        :: else -> skip;
        fi;
    od
}