// port_model.pml
/* Simple Promela model of the port simulation.
   n_docks = 2, crane available = 1
*/

int docks = 2;   // number of free docks (0..2)
int crane = 1;    // crane available (0 or 1)

/* proctype representing a Ship's lifecycle */
proctype Ship(byte id) {
    bool indock = false;
    /* Arrive */
    /* try to acquire a dock (non-blocking choice modeled by spin nondet) */
    atomic {
        if
        :: (docks > 0) -> docks = docks - 1; indock = true;
        :: else -> skip /* if no dock, this execution path will just skip (other interleavings model waiting) */
        fi
    }

    /* If we failed to get a dock we still allow other interleavings; 
       to model waiting, we let several transitions where ship retries.
       For simplicity here we assume at least some run obtains a dock. */

    /* Only proceed if indock */
    if
    :: (indock) ->
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

        /* depart: release dock */
        atomic { docks = docks + 1; indock = false; }

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
    assert(docks >= 0 && docks <= 2);
    assert(crane == 0 || crane == 1);
}
