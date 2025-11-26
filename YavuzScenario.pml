mtype = { requestDock, checkDock, dockFree, assignDock, requestCrane, checkCrane, craneMaintenance, operationCancelled, depart, releaseDock, acknowledge };

#define iSize 100

chan ShipPort = [iSize] of { mtype }
chan PortDock = [iSize] of { mtype }
chan PortCrane = [iSize] of { mtype }

proctype Ship(byte id) {
    Start: atomic {
        ShipPort!requestDock 
        goto Next1
    }
    Next1: atomic {
        ShipPort?assignDock 
        goto Next2
    }
    Next2: atomic {
        ShipPort!requestCrane 
        goto Next3
    }
    Next3: atomic {
        ShipPort?operationCancelled 
        goto Next4
    }
    Next4: atomic {
        ShipPort!acknowledge
        goto Next5
    }
    Next5: atomic {
        ShipPort!depart 
        goto Next6
    }
    Next6: atomic {
        ShipPort?acknowledge
    }
}

proctype PortController() {
    Start: atomic {
        ShipPort?requestDock 
        goto Next1
    }
    Next1: atomic {
        PortDock!checkDock 
        goto Next2
    }
    Next2: atomic {
        PortDock?dockFree 
        goto Next3
    }
    Next3: atomic {
        ShipPort!assignDock 
        goto Next4
    }
    Next4: atomic {
        ShipPort?requestCrane 
        goto Next5
    }
    Next5: atomic {
        PortCrane!checkCrane 
        goto Next6
    }
    Next6: atomic {
        PortCrane?craneMaintenance 
        goto Next7
    }
    Next7: atomic {
        ShipPort!operationCancelled 
        goto Next8
    }
    Next8: atomic {
        ShipPort?acknowledge 
        goto Next9
    }
    Next9: atomic {
        ShipPort?depart 
        goto Next10
    }
    Next10: atomic {
        ShipPort!acknowledge 
        goto Next11
    }
    Next11: atomic {
        PortDock!releaseDock 
        goto Next12
    }
    Next12: atomic {
        PortDock?acknowledge 
    }
}

proctype Dock(byte id) {
    Start: atomic {
        PortDock?checkDock 
        goto Next1
    }
    Next1: atomic {
        PortDock!dockFree 
        goto Next2
    }
    Next2: atomic {
        PortDock?releaseDock 
        goto Next3
    }
    Next3: atomic {
        PortDock!acknowledge
    }
}

proctype Crane(byte id) {
    Start: atomic {
        PortCrane?checkCrane 
        goto Next1
    }
    Next1: atomic {
        PortCrane!craneMaintenance 
    }
}

init {
    run Ship(0);
    run PortController();
    run Dock(0);
    run Crane(0);
}
