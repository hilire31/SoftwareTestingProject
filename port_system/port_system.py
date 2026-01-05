# port_system.py

import os
from datetime import datetime
from enum import Enum


# Logging configuration: writes to workspace-level logs/ folder by default.
LOG_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "logs"))
LOG_FILE = os.path.join(LOG_DIR, "port.log")


def ensure_log_dir():
    os.makedirs(LOG_DIR, exist_ok=True)


def write_log(message):
    """Append a timestamped message to the log file (creates logs/ if needed)."""
    ensure_log_dir()
    ts = datetime.utcnow().isoformat()
    with open(LOG_FILE, "a", encoding="utf-8") as f:
        f.write(f"{ts} - {message}\n")


def set_log_file(path):
    """Set the log file to a custom path (used by tests). Path may be absolute or relative."""
    global LOG_FILE, LOG_DIR
    LOG_FILE = os.path.abspath(path)
    LOG_DIR = os.path.dirname(LOG_FILE)
    ensure_log_dir()


class ShipState(Enum):
    WAITING = "waiting"
    DOCKED = "docked"
    UNLOADING = "unloading"
    DEPARTED = "departed"


class ResourceError(Exception):
    pass


class Dock:
    def __init__(self, dock_id):
        self.id = dock_id
        self.occupied_by = None
        write_log(f"Dock {dock_id} created")

    def acquire(self, ship):
        if self.occupied_by is not None:
            raise ResourceError(f"Dock {self.id} already occupied")
        self.occupied_by = ship

    def release(self):
        self.occupied_by = None


class Crane:
    def __init__(self, crane_id):
        self.id = crane_id
        self.occupied_by = None
        write_log(f"Crane {crane_id} created")

    def acquire(self, ship):
        if self.occupied_by is not None:
            raise ResourceError(f"Crane {self.id} already occupied")
        self.occupied_by = ship

    def release(self):
        self.occupied_by = None


class Ship:
    def __init__(self, ship_id):
        self.id = ship_id
        self.state = ShipState.WAITING
        self.dock = None
        self.crane = None
        write_log(f"Ship {ship_id} created (state={self.state.value})")

    def dock_ship(self, dock):
        if self.state != ShipState.WAITING:
            raise RuntimeError("Ship not ready to dock")
        self.dock = dock
        self.state = ShipState.DOCKED

    def start_unloading(self, crane):
        if self.state != ShipState.DOCKED:
            raise RuntimeError("Ship must be docked before unloading")
        self.crane = crane
        self.state = ShipState.UNLOADING

    def depart(self):
        if self.state != ShipState.UNLOADING:
            raise RuntimeError("Ship must unload before departure")
        self.state = ShipState.DEPARTED



class PortCoordinator:
    def __init__(self, docks, cranes):
        self.docks = docks
        self.cranes = cranes
        self.message_log = []

    def log(self, message):
        self.message_log.append(message)
        # Also write to persistent log
        write_log(message)

    def assign_dock(self, ship):
        for dock in self.docks:
            if dock.occupied_by is None:
                dock.acquire(ship)
                ship.dock_ship(dock)
                self.log(f"Ship {ship.id} docked at Dock {dock.id}")
                return dock
        raise ResourceError("No available dock")

    def assign_crane(self, ship):
        for crane in self.cranes:
            if crane.occupied_by is None:
                crane.acquire(ship)
                ship.start_unloading(crane)
                self.log(f"Ship {ship.id} unloading with Crane {crane.id}")
                return crane
        raise ResourceError("No available crane")

    def release_resources(self, ship):
        if ship.crane:
            ship.crane.release()
            self.log(f"Crane {ship.crane.id} released")
            ship.crane = None

        if ship.dock:
            ship.dock.release()
            self.log(f"Dock {ship.dock.id} released")
            ship.dock = None

        ship.depart()
        self.log(f"Ship {ship.id} departed")

