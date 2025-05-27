CC=clang
CFLAGS=-Wall -Wextra -std=c11 -pg

build: main

main.o: main.c ds.h
	$(CC) $(CFLAGS) -c $< -o $@

main: main.o
	$(CC) $^ -o $@

clean:
	rm -f main main.o

.PHONY: build clean
