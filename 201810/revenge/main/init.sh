#!/usr/bin/env bash

echo Using flag $REVENGE_FLAG
sed 's/"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"/'\"$REVENGE_FLAG\"'/g' revenge.c > revenge-strap.c
gcc revenge-strap.c -o revenge-strap
ENCODED_REVENGE_FLAG=$(echo -n {`./revenge-strap | xxd -i`})
sed 's/"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"/'"$ENCODED_REVENGE_FLAG"'/g' revenge.c > revenge-final.c
gcc revenge-final.c -o revenge-final -static
while true; do nc -nlvp 8443 < revenge-final; done
