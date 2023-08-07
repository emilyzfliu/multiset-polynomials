from utils import ModularInverter
import random
P = 101

def main():
    omega = random.randint(2, 101)
    residues = {1, omega}
    accumulator = omega
    for i in range(2, P):
        accumulator *= omega
        accumulator = accumulator % P
        if accumulator not in residues:
            residues.add(accumulator)
        else:
            break
    print(f'generator {omega} has subgroup of order {len(residues)}')

def main2():
    omega = 6
    m = ModularInverter(P)
    for i in range(1, 11):
        print(f'omega^i = {omega**i % P}, inverse is claimed to be {m.modular_inverse(omega**i % P)}')


if __name__ == '__main__':
    main2()
