// port_model.pml
/* Simple Promela model of the port simulation.
   n_berths = 2, crane available = 1
*/

int berths = 2;   // number of free berths (0..2)
int crane = 1;    // crane available (0 or 1)

/* proctype representing a Ship's lifecycle */
proctype Ship(byte id) {
    bool inBerth = false;
    /* Arrive */
    /* try to acquire a berth (non-blocking choice modeled by spin nondet) */
    atomic {
        if
        :: (berths > 0) -> berths = berths - 1; inBerth = true;
        :: else -> skip /* if no berth, this execution path will just skip (other interleavings model waiting) */
        fi
    }

    /* If we failed to get a berth we still allow other interleavings; 
       to model waiting, we let several transitions where ship retries.
       For simplicity here we assume at least some run obtains a berth. */

    /* Only proceed if inBerth */
    if
    :: (inBerth) ->
        /* Acquire crane */
        atomic {
            if
            :: (crane > 0) -> crane = crane - 1;
            :: else -> skip
            fi
        }

        /* Use crane (abstract action) */
        /* release crane */
        atomic { crane = crane + 1; }

        /* depart: release berth */
        atomic { berths = berths + 1; inBerth = false; }

    :: else -> skip
    fi;

    /* end of ship */
}

/* Initialize several ships */
init {
    /* spawn 5 ships */
    run Ship(0);
    run Ship(1);
    run Ship(2);
    run Ship(3);
    run Ship(4);

    /* safety checks as assertions - these will be checked by SPIN during verification */
    assert(berths >= 0 && berths <= 2);
    assert(crane == 0 || crane == 1);
}
