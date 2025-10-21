# port_simulation.py
import threading
import time
import random

class Port:
    def __init__(self, n_docks=2):
        self.docks = threading.Semaphore(n_docks)  # available docks
        self.crane = threading.Lock()                # exclusive crane
        self.n_docks = n_docks

    def arrive_and_service(self, ship_id):
        print(f"Ship {ship_id} arriving...")
        # request a dock
        self.docks.acquire()
        try:
            print(f"Ship {ship_id} docked (dock acquired).")
            # simulate unloading/loading that requires crane
            with self.crane:
                print(f"Ship {ship_id} using crane...")
                # simulate variable work
                time.sleep(random.uniform(0.1, 0.5))
                print(f"Ship {ship_id} finished using crane.")
            # simulate some post-crane operations
            time.sleep(random.uniform(0.05, 0.2))
        finally:
            # leave dock
            self.docks.release()
            print(f"Ship {ship_id} departed (dock released).")

def ship_thread(port, ship_id):
    # ships might attempt service multiple times in a longer sim; keep it simple: one visit
    port.arrive_and_service(ship_id)

def main():
    random.seed(42)
    port = Port(n_docks=2)
    ships = []
    n_ships = 5

    for i in range(n_ships):
        t = threading.Thread(target=ship_thread, args=(port, i))
        ships.append(t)
        t.start()
        # random arrival spacing
        time.sleep(random.uniform(0.01, 0.15))

    for t in ships:
        t.join()

    print("Simulation finished.")

if __name__ == "__main__":
    main()
