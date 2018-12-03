#include <stdio.h>

int main(int argc, char **argv, char **envp)
{
  char str[] = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA";
  char xor[] = "\x66\x15\x62\x2c\xdc\x21\xfa\x2e\xcc\xbf\xa8\x93\x24\xb4\xb4\xd5"
               "\xe5\xe7\x3a\x0a\xb5\x7a\xce\x58\x63\xb4\x9e\xce\xf2\x93\x66\x6f"
               "\xe1\xfc";
  for(int i = 0; i < sizeof(xor); i ++)
  {
    printf("%c", str[i] ^ xor[i]);
  }
  return 0;
}
