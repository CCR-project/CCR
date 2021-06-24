#!/bin/bash
cc -o simple simple.s
./simple
echo $?
cc -o factorial factorial.s
./factorial
echo $?
cc -o mutsum mutsumF.s mutsumG.s mutsumMain.s
./mutsum
echo $?
cc -o knot knot.s
./knot
echo $?
cc -o mem1 mem1F.s mem1Main.s
./mem1
echo $?
cc -o mem2 mem2.s
./mem2
echo $?
cc -o link link.s
./link
echo $?
