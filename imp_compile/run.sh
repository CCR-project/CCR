#!/bin/bash

./test.native -conf compcert.ini

mv simple.s bin/simple.s
cc -o bin/simple bin/simple.s
bin/simple
echo $?

mv factorial.s bin/factorial.s
cc -o bin/factorial bin/factorial.s
bin/factorial
echo $?

mv mutsumF.s bin/mutsumF.s
mv mutsumG.s bin/mutsumG.s
mv mutsumMain.s bin/mutsumMain.s
cc -o bin/mutsum bin/mutsumF.s bin/mutsumG.s bin/mutsumMain.s
bin/mutsum
echo $?

mv knot.s bin/knot.s
cc -o bin/knot bin/knot.s
bin/knot
echo $?

mv mem1F.s bin/mem1F.s
mv mem1Main.s bin/mem1Main.s
cc -o bin/mem1 bin/mem1F.s bin/mem1Main.s
bin/mem1
echo $?

mv mem2.s bin/mem2.s
cc -o bin/mem2 bin/mem2.s
bin/mem2
echo $?

mv link.s bin/link.s
gcc -no-pie -o bin/link bin/link.s bin/print.s bin/scan.s
bin/link
echo $?

mv stack.s bin/stack.s
mv echo.s bin/echo.s
mv echo_main.s bin/echo_main.s
mv client.s bin/client.s
cc -o bin/echo_all bin/stack.s bin/echo.s bin/echo_main.s bin/client.s bin/print.s bin/scan.s
bin/echo_all
echo $?
