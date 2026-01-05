#!/usr/bin/env python3
"""
main.py — Petit démonstrateur et utilitaire pour le projet Port Management
Usage:
  - python main.py demo       # Lance une démonstration simple du flux (dock, crane, release)
  - python main.py test       # Lance les tests (via pytest)

Ce script est volontairement simple : il montre comment utiliser les classes du module
`port_system` et offre un moyen pratique d'exécuter la batterie de tests.
"""
import argparse
import sys
from port_system.port_system import Dock, Crane, Ship, PortCoordinator


def demo():
    docks = [Dock(1), Dock(2)]
    cranes = [Crane(1), Crane(2)]
    port = PortCoordinator(docks, cranes)

    # Création de quelques navires et exécution d'un scénario simple
    ships = [Ship("S1"), Ship("S2")]

    for ship in ships:
        try:
            port.assign_dock(ship)
            port.assign_crane(ship)
            # Ici on simule la fin de l'opération
            port.release_resources(ship)
        except Exception as exc:
            print(f"Erreur pour le navire {ship.id}: {exc}")

    print("\nJournal des événements :")
    for msg in port.message_log:
        print(f" - {msg}")


def run_tests():
    # Import local runner pour garder la logique de test separée
    import run_tests as rt
    rt.run()


def main(argv=None):
    parser = argparse.ArgumentParser(description="Port Management demo & test runner")
    parser.add_argument("action", nargs="?", choices=("demo", "test"), default="demo",
                        help="Action à effectuer : 'demo' (par défaut) ou 'test'")
    args = parser.parse_args(argv)

    if args.action == "demo":
        demo()
    elif args.action == "test":
        run_tests()


if __name__ == "__main__":
    main()
