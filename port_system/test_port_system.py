# test_port_system.py

import pytest
from port_system import Dock, Crane, Ship, PortCoordinator, ShipState, ResourceError


def test_dock_acquisition_and_release():
    dock = Dock(1)
    ship = Ship("S1")

    dock.acquire(ship)
    assert dock.occupied_by == ship

    dock.release()
    assert dock.occupied_by is None


def test_crane_acquisition_and_release():
    crane = Crane(1)
    ship = Ship("S1")

    crane.acquire(ship)
    assert crane.occupied_by == ship

    crane.release()
    assert crane.occupied_by is None


def test_correct_ship_operation_order():
    ship = Ship("S1")
    dock = Dock(1)
    crane = Crane(1)

    ship.dock_ship(dock)
    assert ship.state == ShipState.DOCKED

    ship.start_unloading(crane)
    assert ship.state == ShipState.UNLOADING

    ship.depart()
    assert ship.state == ShipState.DEPARTED


def test_invalid_ship_operation_order():
    ship = Ship("S1")
    crane = Crane(1)

    with pytest.raises(RuntimeError):
        ship.start_unloading(crane)


def test_port_coordinator_full_scenario():
    docks = [Dock(1)]
    cranes = [Crane(1)]
    port = PortCoordinator(docks, cranes)

    ship = Ship("S1")

    port.assign_dock(ship)
    assert ship.state == ShipState.DOCKED

    port.assign_crane(ship)
    assert ship.state == ShipState.UNLOADING

    port.release_resources(ship)
    assert ship.state == ShipState.DEPARTED

    # Message flow verification
    assert port.message_log == [
        "Ship S1 docked at Dock 1",
        "Ship S1 unloading with Crane 1",
        "Crane 1 released",
        "Dock 1 released",
        "Ship S1 departed"
    ]


def test_no_available_dock():
    dock = Dock(1)
    port = PortCoordinator([dock], [])

    ship1 = Ship("S1")
    ship2 = Ship("S2")

    port.assign_dock(ship1)

    with pytest.raises(ResourceError):
        port.assign_dock(ship2)


def test_logging_created_and_events(tmp_path):
    from port_system import set_log_file

    log_path = tmp_path / "test_port.log"
    set_log_file(str(log_path))

    # Création d'objets après configuration du fichier de log
    dock = Dock(1)
    crane = Crane(1)
    ship = Ship("S1")
    port = PortCoordinator([dock], [crane])

    port.assign_dock(ship)
    port.assign_crane(ship)
    port.release_resources(ship)

    # Lecture du fichier de log
    with open(log_path, "r", encoding="utf-8") as f:
        content = f.read()

    assert "Dock 1 created" in content
    assert "Crane 1 created" in content
    assert "Ship S1 created" in content
    assert "Ship S1 docked at Dock 1" in content
    assert "Ship S1 unloading with Crane 1" in content
    assert "Ship S1 departed" in content


if __name__ == "__main__":
    import pytest
    raise SystemExit(pytest.main(["-q"]))



