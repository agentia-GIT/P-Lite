#!/bin/sh
# Compilation croisée Linux -> Windows x64 (mingw-w64)
x86_64-w64-mingw32-windres lecteur.rc -O coff -o lecteur_res.o
x86_64-w64-mingw32-gcc -O2 -Wall -mwindows -municode -static -s lecteur.c lecteur_res.o -o lecteur.exe \
  -lgdi32 -lcomdlg32 -lshell32 -luser32 -lcomctl32 -lurlmon -lwininet -lole32 -ladvapi32 -luuid
