#!/bin/bash
echo ""
echo "IMP compiler for x86_64-linux"
echo ""

./configure x86_64-linux
echo ""

echo "Generating compcert.ini:"
make
echo ""

echo "Build IMP compiler and example program:"
./build.sh
echo ""

echo "Run IMP compiler:"
./test.native -conf compcert.ini
echo ""

echo "Compile IO modules..."
gcc -S -o bin/print.s bin/print.c
gcc -S -o bin/scan.s bin/scan.c

echo "Linking modules (in ./bin)..."
# mv MWApp.s bin/MWApp.s
# mv MWC.s bin/MWC.s
# mv MWMap.s bin/MWMap.s
# gcc -m64 -no-pie -o bin/MW_all bin/MWApp.s bin/MWC.s bin/MWMap.s bin/print.s bin/scan.s

mv stack.s bin/stack.s
mv echo.s bin/echo.s
mv echo_main.s bin/echo_main.s
mv client.s bin/client.s
gcc -m64 -no-pie -o bin/echo_all bin/stack.s bin/echo.s bin/echo_main.s bin/client.s bin/print.s bin/scan.s

echo "Run program: echo example (on the technical report)."
#read input
bin/echo_all
# echo "(Echo) Input integers, -1 to stop:"
# bin/MW_all

# mv simple.s bin/simple.s
# cc -o bin/simple bin/simple.s
# bin/simple
# echo $?

# mv factorial.s bin/factorial.s
# cc -o bin/factorial bin/factorial.s
# bin/factorial
# echo $?

# mv mutsumF.s bin/mutsumF.s
# mv mutsumG.s bin/mutsumG.s
# mv mutsumMain.s bin/mutsumMain.s
# cc -o bin/mutsum bin/mutsumF.s bin/mutsumG.s bin/mutsumMain.s
# bin/mutsum
# echo $?

# mv knot.s bin/knot.s
# cc -o bin/knot bin/knot.s
# bin/knot
# echo $?

# mv mem1F.s bin/mem1F.s
# mv mem1Main.s bin/mem1Main.s
# cc -o bin/mem1 bin/mem1F.s bin/mem1Main.s
# bin/mem1
# echo $?

# mv mem2.s bin/mem2.s
# cc -o bin/mem2 bin/mem2.s
# bin/mem2
# echo $?

# mv link.s bin/link.s
# gcc -no-pie -o bin/link bin/link.s bin/print.s bin/scan.s
# bin/link
# echo $?
