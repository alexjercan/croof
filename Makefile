CC=clang
CFLAGS=-Wall -Wextra -std=c11 -g
SRC=src
OUT=build

all: $(OUT)/main

$(OUT):
	mkdir -p $(OUT)

$(OUT)/ds.o: $(SRC)/ds.c $(SRC)/ds.h | $(OUT)
	$(CC) $(CFLAGS) -c $< -o $@

$(OUT)/lexer.o: $(SRC)/lexer.c $(SRC)/ds.h $(SRC)/lexer.h | $(OUT)
	$(CC) $(CFLAGS) -c $< -o $@

$(OUT)/parser.o: $(SRC)/parser.c $(SRC)/ds.h $(SRC)/lexer.h $(SRC)/parser.h | $(OUT)
	$(CC) $(CFLAGS) -c $< -o $@

$(OUT)/solver.o: $(SRC)/solver.c $(SRC)/ds.h $(SRC)/lexer.h $(SRC)/parser.h $(SRC)/solver.h | $(OUT)
	$(CC) $(CFLAGS) -c $< -o $@

$(OUT)/main.o: $(SRC)/main.c $(SRC)/ds.h $(SRC)/lexer.h $(SRC)/parser.h | $(OUT)
	$(CC) $(CFLAGS) -c $< -o $@

$(OUT)/main: $(OUT)/main.o $(OUT)/ds.o $(OUT)/lexer.o $(OUT)/parser.o $(OUT)/solver.o | $(OUT)
	$(CC) $(CFLAGS) $^ -o $@

clean:
	rm -rf $(OUT)

.PHONY: all clean
