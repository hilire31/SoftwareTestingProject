mtype = {login, requestHotel, getHotel, requestTasks, getTasks, dashboard, pickTask, markInProgress, notifyClientStart, notifyManagerStart, passkey, uploadInitialState, logEntry, uploadFinalState, notifyClientDone, notifyManagerDone, logExit, acknowledge};

#define iSize 100

chan StaffSystem = [iSize] of { mtype }
chan SystemHotel = [iSize] of { mtype }
chan SystemSystem = [iSize] of { mtype }
chan SystemClient = [iSize] of { mtype }
chan SystemManager = [iSize] of { mtype }

proctype Staff() {
	Start: atomic {
		StaffSystem!login 
		goto Next1
	}
	Next1: atomic {
		StaffSystem?dashboard 
		goto Next2
	}
	Next2: atomic {
		StaffSystem!pickTask 
		goto Next3
	}
	Next3: atomic {
		StaffSystem?passkey 
		goto Next4
	}
	Next4: atomic {
		StaffSystem!uploadInitialState 
		goto Next5
	}
	Next5: atomic {
		StaffSystem?acknowledge
		goto Next6
	}
	Next6: atomic {
		StaffSystem!uploadFinalState
	}
}

proctype System() {
	Start: atomic {
		StaffSystem?login 
		goto Next0
	}
	Next0: atomic {
		SystemHotel!requestHotel
		goto Next01
	}
	Next01: atomic {
		SystemHotel?getHotel
		goto Next02
	}
	Next02: atomic {
		SystemHotel!requestTasks
		goto Next03
	}
	Next03: atomic {
		SystemHotel?getTasks
		goto Next1
	}
	Next1: atomic {
		StaffSystem!dashboard 
		goto Next2
	}
	Next2: atomic {
		StaffSystem?pickTask 
		goto Next3
	}
	Next3: atomic {
		SystemSystem!markInProgress
		goto Next4
	}
	Next4: atomic {
		SystemSystem?markInProgress
		goto Next5
	}
	Next5: atomic {
		SystemClient!notifyClientStart 
		goto Next6
	}
	Next6: atomic {
		SystemClient?acknowledge 
		goto Next7
	}
	Next7: atomic {
		SystemManager!notifyManagerStart 
		goto Next8
	}
	Next8: atomic {
		SystemManager?acknowledge 
		goto Next9
	}
	Next9: atomic {
		StaffSystem!passkey 
		goto Next10
	}
	Next10: atomic {
		StaffSystem?uploadInitialState 
		goto Next11
	}
	Next11: atomic {
		SystemSystem!logEntry
		goto Next12
	}
	Next12: atomic {
		SystemSystem?logEntry 
		goto Next13
	}
	Next13: atomic {
		StaffSystem!acknowledge
		goto Next14
	}
	Next14: atomic {
		StaffSystem?uploadFinalState
		goto Next15
	}
	Next15: atomic {
		SystemClient!notifyClientDone
		goto Next16
	}
	Next16: atomic {
		SystemClient?acknowledge 
		goto Next17
	}
	Next17: atomic {
		SystemManager!notifyManagerDone
		goto Next18
	}
	Next18: atomic {
		SystemManager?acknowledge 
		goto Next19
	}
	Next19: atomic {
		SystemSystem!logExit 
		goto Next20
	}
	Next20: atomic {
		SystemSystem?logExit 
	}
}

proctype Client() {
	Start: atomic {
		SystemClient?notifyClientStart
		goto Next1
	}
	Next1: atomic {
		SystemClient!acknowledge
		goto Next2
	}
	Next2: atomic {
		SystemClient?notifyClientDone
		goto Next3
	}
	Next3: atomic {
		SystemClient!acknowledge
	}
}

proctype Hotel() {
	Start: atomic {
		SystemHotel?requestHotel
		goto Next1
	}
	Next1: atomic {
		SystemHotel!getHotel
		goto Next2
	}
	Next2: atomic {
		SystemHotel?requestTasks
		goto Next3
	}
	Next3: atomic {
		SystemHotel!getTasks
	}
}

proctype Manager() {
	Start: atomic {
		SystemManager?notifyManagerStart 
		goto Next1
	}
	Next1: atomic {
		SystemManager!acknowledge 
		goto Next2
	}
	Next2: atomic {
		SystemManager?notifyManagerDone
		goto Next3
	}
	Next3: atomic {
		SystemManager!acknowledge 
	}
}

init {
	run Staff();
	run System();
	run Client();
	run Manager();
	run Hotel();
    
}