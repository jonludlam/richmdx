ifneq (, $(shell command -v opam || which opam))
  ifeq ($(origin PKG_CONFIG_PATH), undefined)
    PKG_CONFIG_PATH := $(shell opam var prefix)/lib/pkgconfig
  endif
endif

ifeq ($(OS), Windows_NT)
  ifneq (, $(shell command -v cygpath || which cygpath))
    PKG_CONFIG_PATH := $(shell cygpath --unix --path "$(PKG_CONFIG_PATH)")
  endif
endif

EXISTS := $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) pkg-config --exists ocaml-freestanding; echo $$?)

.PHONY: all clean
all: libcheckseum_freestanding_stubs.a

ifeq ($(EXISTS), 1)
libcheckseum_freestanding_stubs.a:
	touch $@
else
CC ?= cc
FREESTANDING_CFLAGS := $(shell PKG_CONFIG_PATH=$(PKG_CONFIG_PATH) pkg-config --cflags ocaml-freestanding)
CFLAGS := -I../src-c/native -O3 $(FREESTANDING_CFLAGS)

OBJS= adler32.o crc24.o crc32.o crc32c.o stubs.o

libcheckseum_freestanding_stubs.a: $(OBJS)
	$(AR) r $@ $^
endif

clean:
	$(RM) $(OBJS) libcheckseum_freestanding_stubs.a
