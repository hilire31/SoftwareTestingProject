/* Intelligent Harbor Logistics Control System
   Model in Promela for SPIN verification
   - n_docks = 2
   - crane = 1
   - each ship retries if no dock is available, up to a patience limit
*/

int docks = 2;    /* number of free docks (0..2) */
int crane = 1;    /* available cranes (0 or 2)   */
int ships_quit = 0; // number of ships that have left the port by patience limit
#define MAX_WAIT 2   /* maximum number of retries before giving up */
int has_waited = 0; /* number of ships that have waited */
int ships_docked = 0; /* number of ships that have docked */
/* proctype representing a Ship's lifecycle */
proctype Ship(byte id)
{
    bool indock = false;
    bool craned = false;
    byte wait_count = 0;

    printf("Ship %d arrives at port\n", id);

    do
    :: (indock == false && wait_count < MAX_WAIT) ->
        atomic {
            if
            :: (docks > 0) ->
                docks = docks - 1;
                indock = true;
                ships_docked++;
                printf("Ship %d got a dock (remaining: %d)\n", id, docks);
            :: else ->
                printf("Ship %d waits (attempt %d)\n", id, wait_count + 1);
                has_waited++;
                wait_count++;
            fi
        }

    :: (indock) ->
        /* Acquire crane */
        atomic {
            if
            :: (crane > 0) ->
                crane = crane - 1;
                craned = true;
                printf("Ship %d starts using crane\n", id);
            :: else ->
                printf("Ship %d waiting for crane\n", id);
                skip
            fi
        }

        /* Simulate work */
        printf("Ship %d unloading...\n", id);

        /* Release resources */
        atomic {
            if 
            :: (craned) ->
                crane = crane + 1;
                craned = false;
            :: else ->
                skip
            fi
            
            docks = docks + 1;
            indock = false;
            printf("Ship %d leaves port (docks=%d, crane=%d)\n", id, docks, crane);
        }
        break

    :: (wait_count >= MAX_WAIT && !indock) ->
        printf("Ship %d leaves without docking (too long wait)\n", id);
        ships_quit++;
        break
    od
}

/* Initialization */
init {
    run Ship(0);
    run Ship(1);
    run Ship(2);
    run Ship(3);
    run Ship(4);

    /* Safety assertions */
    assert(docks >= 0 && docks <= 2);
    assert(crane >= 0 && crane <= 1);

    ltl positive_eventually { <>[] (has_waited > 0) }
    //assert(ships_quit > 0); // assertion violated (ships_quit>0)
    //assert(ships_quit == 3);
    
    
    
}
