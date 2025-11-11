mtype = { req_crane, grant, release, wait }

chan ship1_to_port = [0] of { mtype }
chan ship2_to_port = [0] of { mtype }
chan port_to_ship1 = [0] of { mtype }
chan port_to_ship2 = [0] of { mtype }

bool crane_busy = false

proctype Ship(chan to_port; chan from_port; byte id) {
    to_port ! req_crane;
    from_port ? grant;
    /* use crane */
    to_port ! release;
}

proctype Port() {
    mtype msg;
    do
    :: ship1_to_port ? msg ->
        if
        :: (msg == req_crane && !crane_busy) ->
            crane_busy = true;
            port_to_ship1 ! grant;
        :: (msg == req_crane && crane_busy) ->
            port_to_ship1 ! wait;
        :: (msg == release) ->
            crane_busy = false;
        fi
    :: ship2_to_port ? msg ->
        if
        :: (msg == req_crane && !crane_busy) ->
            crane_busy = true;
            port_to_ship2 ! grant;
        :: (msg == req_crane && crane_busy) ->
            port_to_ship2 ! wait;
        :: (msg == release) ->
            crane_busy = false;
        fi
    od
}

init {
    atomic {
        run Port();
        run Ship(ship1_to_port, port_to_ship1, 1);
        run Ship(ship2_to_port, port_to_ship2, 2);
    }
}