# Shellcode Encode

One of the more difficult problems to solve in the OSCE lab environment is a shellcode encoding
issue. There's a very limited character set and you must write a manual encoding payload
to magically equal instruction values as a 32 bit interger.

The idea is simple — find three values containing contain no bad bytes that when subtracted from 0 
wrap around the 32 bit maximum integer value — 0xffffffff — and equal the orignal value. For 
instance find three values that satisfy the following contraint that also contains no bad bytes:

Shellcode int **0xfaf56837**

Bad bytes **0x68** and **0x37**

Three underflow operations equals:

**0xfaf56837 = 0x0 - 0x11014342 - 0x77050408 - 0x7d04507f**

This problems is easy to understand — yet difficult to solve. I use the z3 engine from Microsoft
to mathematically prove satisfiablity of the problem.

Usage: **./shellcode_encody.py 0x12345678**

The only requirment is z3. Please follow the guide here to install it with Python bindings:
https://github.com/Z3Prover/z3

You can test this within gdb using the following command.

`p/x 0x0 - 0x11014342 - 0x77050408 - 0x7d04507f`
