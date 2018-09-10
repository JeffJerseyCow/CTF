import z3
import sys

def constrain_prime(s, x, off):
    pos = (0xf << (off * 4))
    p2 = 0x2 << (off * 4)
    p3 = 0x3 << (off * 4)
    p5 = 0x5 << (off * 4)
    p7 = 0x7 << (off * 4)
    pb = 0xb << (off * 4)
    pd = 0xd << (off * 4)
    s.add((x & pos) != p2)
    s.add((x & pos) != p3)
    s.add((x & pos) != p5)
    s.add((x & pos) != p7)
    s.add((x & pos) != pb)
    s.add((x & pos) != pd)

def constrain_nine(s, x):
    for num in range(16):
        pos = 0xf << (4 * num)
        nine = 0x9 << (4 * num)
        s.add((x & pos) != nine)

def main():
    s = z3.Solver()
    x = z3.BitVec('x', 64)
    s.add(x % 0x3 == 0)
    s.add((x % 0x2) != 0)
    s.add(x > 0x100000000000)
    s.add(x < 0x1000000000000000)
    s.add(((x * 0x7) % 0xb) == 0)
    constrain_prime(s, x, 0x2)
    constrain_prime(s, x, 0x3)
    constrain_prime(s, x, 0x5)
    constrain_prime(s, x, 0x7)
    constrain_prime(s, x, 0xb)
    constrain_prime(s, x, 0xd)
    constrain_nine(s, x)

    if s.check() == z3.sat:
        m = s.model()
        print(hex(m[m[0]].as_long()))

if __name__ == '__main__':
    sys.exit(main())
