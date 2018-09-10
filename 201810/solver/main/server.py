#!/usr/bin/env python3
import sys
import struct
import socket
import string
from multiprocessing import Process

FLAG = b'{c14c1a78b99fcd9c23875986107748f5}\n'

def div_3(conn, num):
    if (num % 0x3) != 0:
        msg = '"%s" is not evenly divisible by 3' % hex(num)
        conn.send(msg.encode())
        conn.close()
        return False
    return True

def is_even(conn, num):
    if (num % 0x2) == 0:
        msg = '"%s" is even' % hex(num)
        conn.send(msg.encode())
        conn.close()
        return False
    return True

def is_large(conn, num):
    if num <= 0x100000000000 or num >= 0x1000000000000000:
        msg = '"%s" is out of range' % hex(num)
        conn.send(msg.encode())
        conn.close()
        return False
    return True

def is_div17_11(conn, num):
    if ((num * 0x11) % 0xb) != 0:
        msg = '"%s" is not evenly divisible by 0xb when ' \
              'multiplied by 0x11' % hex(num)
        conn.send(msg.encode())
        conn.close()
        return False
    return True

def is_prime_pos(conn, num):
    hex_num = hex(num)[::-1]
    if is_prime(hex_num[0x2]) or is_prime(hex_num[0x3]) or \
    is_prime(hex_num[0x5]) or is_prime(hex_num[0x7]) or \
    is_prime(hex_num[0xb]) or is_prime(hex_num[0xd]):
        msg = '"%s" doesn\'t abide the prime position requirement' % hex(num)
        conn.send(msg.encode())
        return False
    return True

def is_prime(num):
    num = int(num, 16)
    if num == 0x2 or num == 0x3 or num == 0x5 or num == 0x7 or num == 0xb or \
    num == 0xd:
        return True
    return False

def is_nine(conn, num):
    for digit in hex(num):
        if digit == '9':
            msg = '"%s" contains a 0x9 digit' % hex(num)
            conn.send(msg.encode())
            conn.close()
            return False
    return True

def send_banner(conn):
    conn.send(b'==================================================\n')
    conn.send(b'I\'m thinking of a hexidecimal number\n')
    conn.send(b'It must be evenly divisible by 3\n')
    conn.send(b'It must not be even\n')
    conn.send('It must not contain the digit 0x9\n'.encode())
    conn.send('It must larger than 0x100000000000 and smaller than\n' \
              '0x1000000000000000\n'.encode())
    conn.send('When multiplied by 0x7 the result must be evenly divisible\n' \
              'by 0xb\n'.encode())
    conn.send('Starting with index 0 being the right most digit, each prime\n' \
              'number position must not contain a prime digit. For example\n' \
              'position 3 is a prime number and the digit in that position\n' \
              'must not be prime\n'.encode())
    conn.send(b'#> ')

def handle_conn(conn, addr):
    send_banner(conn)
    num = conn.recv(1024).decode().strip()
    try:
        num = int(num, 16)
    except:
        msg = '"%s" is not hexidecimal' % num
        conn.send(msg.encode())
        conn.close()
        return False
    if not div_3(conn, num): return False
    if not is_even(conn, num): return False
    if not is_large(conn, num): return False
    if not is_div17_11(conn, num): return False
    if not is_prime_pos(conn, num): return False
    if not is_nine(conn, num): return False
    conn.send(FLAG)
    conn.close()

def main():
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.bind(('', 8080))
    s.listen(10)
    while True:
        conn, addr = s.accept()
        p = Process(target=handle_conn, args=(conn, addr))
        p.start()

if __name__ == '__main__':
    sys.exit(main())
