


def run():
    try:
        import pytest
    except ImportError:
        print("pytest isn't installed.")
        return 1

    # Lancer pytest en mode verbeux court
    exit_code = pytest.main(["-q"])
    if exit_code == 0:
        print("\n [run_tests.py] all test passed")
    else:
        print(f"\n [run_tests.py] at least one test failed (code {exit_code}).")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(run())
