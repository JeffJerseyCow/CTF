# InsomniHack-CTF-2017
baby - InsomniHack-CTF 2017

Baby was the initial solution for the PWN series of capture the flag events during InsomniHack's 2017 CTF event.

Now the idea was fairly simple, the binary "baby" was listening on port 1337. You connect to it and select a format string, stack overflow or heap over flow based attack. The most simple solution I could fathom is to use the format string to leak the security cookie (canary), save frame pointer and return address from the stack. As it uses "fork()", a copy on write duplicate of the parent process, the cookie value will remain the same. This means that after I calculated the offset to be 1032 bytes I could send an additional byte to see if normal operation resumes. I check “normal operation” by searching for the phrase “Welcome” in the response. This means that the check passed and returned back to its initial menu. If it didn’t I tried a different byte value and so on. This meant I could byte by byte brute force the security cookie, saved frame pointer and return address. Knowing these offsets into the file using “objdump -D ./baby” I could calculate the current load address. Using this I built and initial exploit to use a ROP chain that utilises the local “sendlen” function prologue to write the accept glibc GOT entry to a file descriptor of my choosing. The idea being that the OS loader over wrote the relocation entry using dlopen/dlsym functionality with the absolute virtual address within glibc. As they kindly provided the libc library I was able to calculate the offset of various ROP gadgets from within the library.

NOTE: The exploit works with libc.so.6 lifted from my target/test Kali box. If you’d like this to work with the libc library on InsomniHack’s server look for identical ROP gadgets within libc.so.6. Use a tool called “Ropper” it’s awesome. Simply swap out the offsets for ones in the “libc.so.6” binary and use “LD_PRELOAD=./libc.so.6 ./baby” to test. The OS loader should handle the rest. 

At this point I used the “mprotect” syscall on my base address of the stack (page aligned) hence the & symbol. Once called it marks 1000 bytes as read, write, execute. The final return jumps into the start of the shell code at “RBP + 0x28” and binds a shell to TCP port 4444. 

If running baby on a Kali x64 box the exploit is capable of automatically spawning a shell on tcp port 4444. This takes a while.

Any comments, explanations or additional questions that you have, please contact me directly.

Run “python exploit.py [ip] [port]”

Contact:
jeffjerseycow@gmail.com
