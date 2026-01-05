"""
run_tests.py — petit utilitaire pour exécuter pytest depuis le projet
Usage: python run_tests.py
Retourne le code de sortie de pytest.
"""
import sys


def run():
    try:
        import pytest
    except ImportError:
        print("pytest n'est pas installé dans cet environnement. Installez-le (pip install pytest) et réessayez.")
        return 1

    # Lancer pytest en mode verbeux court
    exit_code = pytest.main(["-q"])
    if exit_code == 0:
        print("\n✅ Tous les tests ont réussi.")
    else:
        print(f"\n❌ Tests échoués (code {exit_code}).")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(run())
