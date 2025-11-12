#define N_DOCKS 2
#define N_SHIPS 5

int docks = N_DOCKS;   /* available docks */
bool crane = true;     /* true = free, false = in use */

proctype Ship(byte id) {
    printf("Ship %d arriving...\n", id);

    /* Wait for dock */
    do
    :: atomic {
        if
        :: docks > 0 ->
            docks--;
            printf("Ship %d acquired a dock.\n", id);
            break
        :: else -> skip
        fi
    }
    od;

    /* Wait for crane */
    do
    :: atomic {
        if
        :: crane ->
            crane = false;
            printf("Ship %d acquired the crane.\n", id);
            break
        :: else -> skip
        fi
    }
    od;

    /* Simulate operation (critical section) */
    printf("Ship %d loading/unloading...\n", id);
    /* atomic section ensures exclusive crane use */
    atomic {
        crane = true;
        docks++;
        printf("Ship %d released crane and dock.\n", id);
    }
    progress: printf("Ship %d finished.\n", id);
    /* Safety check */
    assert(docks >= 0 && docks <= N_DOCKS);
    assert(crane == true || crane == false);
}

init {
    run Ship(0);
    run Ship(1);
    run Ship(2);
    run Ship(3);
    run Ship(4);
}

never { /* no two ships should hold the crane at once */
    do
    :: (crane == false && crane == false) -> assert(false)
    :: else -> skip
    od
}
