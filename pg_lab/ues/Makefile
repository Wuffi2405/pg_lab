MODULES = ues

# use 'make -e MODE=gdb' to make with debugging symbols
GDB_MODE = $(MODE)
CFLAGS = -Wall -Wextra -Wpedantic -Wshadow -Wconversion -Wsign-conversion -Wformat=2 -Wnull-dereference -Wdouble-promotion -Wfloat-equal -Wstack-protector -Wunreachable-code -Wstack-usage=1024
ifeq ($(GDB_MODE), gdb)
	CFLAGS += -ggdb -O0 -Wall -Wextra -fsanitize=address,undefined,thread -fstack-protector-strong
endif

export PG_CFLAGS=$(CFLAGS)

PG_CONFIG = ../../postgres-server/dist/bin/pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
