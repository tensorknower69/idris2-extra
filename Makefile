all: libextra.so

libextra.so: libextra.c
	gcc -Wall -shared -o $@ $^

.PHONY: clean

clean:
	rm -f libextra.so
