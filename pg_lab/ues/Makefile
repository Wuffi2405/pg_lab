MODULES = ues

# use 'make -e MODE=gdb' to make with debugging symbols
GDB_MODE = $(MODE)
MYFLAGS = -Wall -Wextra -Wpedantic -Wshadow -Wconversion -Wsign-conversion -Wformat=2 -Wnull-dereference -Wdouble-promotion -Wfloat-equal -Wstack-protector -Wunreachable-code -Wstack-usage=1024

ifeq ($(GDB_MODE), gdb)
	MYFLAGS += -ggdb -O0 -Wall -Wextra 
endif
#-fsanitize=address,undefined -fstack-protector-strong

export PG_CFLAGS = $(MYFLAGS)

PG_CONFIG = ../../postgres-server/dist/bin/pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)