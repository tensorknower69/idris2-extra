all: libextra.so

libextra.so: libextra.c
	gcc -shared -o $@ $^
