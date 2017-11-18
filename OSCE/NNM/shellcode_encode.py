#!/usr/bin/env python

# System Imports
import z3
import sys
import binascii
import argparse


def main():
    """
    Entry point.

    Returns:
        True is successful and error free else false.
    """

    # Create Parser
    parser = argparse.ArgumentParser()
    parser.add_argument('value', nargs='?', type=str, metavar='value', help='Value to calculate')
    args = parser.parse_args()

    # Check Value
    if not args.value:
        parser.print_help()
        return False

    # Value to Calculate
    try:
        value = int(args.value, 16)
    except ValueError:
        print('[-] Invalid Hex String {}'.format(args.value))
        return False

    # Debug
    print('[*] Using Value {}'.format(hex(value)))

    # Calculate Difference
    diff = 0xffffffff - value + 1

    # Solver
    s = z3.Solver()

    # Value Already Valid
    if is_valid(s, value):
        print('[*] Sat')
        print('[*] Push {}'.format(hex(value)))

        # Success
        return True

    # Diff Already Valid
    if is_valid(s, diff):
        print('[*] Sat')
        print('[*] 0x0 - {} = {}'.format(hex(diff), hex(value)))

        # Success
        return True

    # Symbols
    num0 = z3.BitVec('num0', 32)
    num1 = z3.BitVec('num1', 32)
    num2 = z3.BitVec('num2', 32)

    # Constraints Good Characters
    add_chrs(s, num0)
    add_chrs(s, num1)
    add_chrs(s, num2)

    # Add Width Constraints
    s.add(num0 >= 0x10000000)
    s.add(num1 >= 0x10000000)
    s.add(num2 >= 0x10000000)

    # Add Addition Constraints
    s.add(num0 + num1 + num2 == diff)

    # Sat
    if s.check() == z3.sat:
       
        # Get Model
        m = s.model()
        num0 = m[num0].as_long()
        num1 = m[num1].as_long()
        num2 = m[num2].as_long()
        total = (num0 + num1 + num2) & 0xffffffff

        # Output
        print('[*] Sat')
        print('[*] 0x0 - {} - {} - {} = {}'.format(
            hex(num0),
            hex(num1),
            hex(num2),
            hex(abs(total - 1 - 0xffffffff))))

        # Success
        return True

    # Unsat
    else:
        print('[*] Unsat')

        return False

def add_chrs(s, num):
    """
    Add bad character constraints.

    Args:
        s: z3 solver instance.
        num: Symbol to constrain.
    """

    # Allowed Chars
    valid_chars = "\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0b\x0c\x0e\x0f\x10\x11\x12\x13" \
                  "\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f\x20\x21\x22\x23\x24" \
                  "\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x30\x31\x32\x33\x34\x35\x36" \
                  "\x37\x38\x39\x3b\x3c\x3d\x3e\x41\x42\x43\x44\x45\x46\x47\x48\x49\x4a" \
                  "\x4b\x4c\x4d\x4e\x4f\x50\x51\x52\x53\x54\x55\x56\x57\x58\x59\x5a\x5b" \
                  "\x5c\x5d\x5e\x5f\x60\x61\x62\x63\x64\x65\x66\x67\x68\x69\x6a\x6b\x6c" \
                  "\x6d\x6e\x6f\x70\x71\x72\x73\x74\x75\x76\x77\x78\x79\x7a\x7b\x7c\x7d" \
                  "\x7e\x7f"
    
    # Get Bad Char List
    clist = [x for x in range(256)]
    flist = filter(lambda c: chr(c) not in valid_chars, clist)

    # Constrains Loop
    for val in flist:
        val0 = val
        val8 = val << 8
        val16 = val << 16
        val24 = val << 24

        # Add Constrains
        s.add(num & 0xff != val0)
        s.add(num & 0xff00 != val8)
        s.add(num & 0xff0000 != val16)
        s.add(num & 0xff000000 != val24)

def is_valid(s, num):
    """
    Check if num is valid.

    Args:
        s: z3 solver instance.
        num: Number to check.

    Returns:
        True if sat else false.
    """

    # Check Num Valid
    s.push()
    add_chrs(s, num)

    # Sat
    if s.check() == z3.sat:

        # Success
        return True

    # Unsat 
    else:
        s.pop()    
        return False


if __name__ == '__main__':
    """
    Exit on main return code.
    """

    sys.exit(main())
