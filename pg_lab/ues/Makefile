MODULES = ues

#
# We use this Makefile for compiling our ues extension against 
# PostgreSQL with with PostgreSQL build system(PGXS).
# See https://www.postgresql.org/docs/current/extend-pgxs.html
# 
# Our Makefile has a few options available to make compiling a
# sense of achievement. First of all we can trigger make with
# navigating into its directory and call 'make'.
#
# By default we run make with a lot of compile flags. We can
# additionally add the following options:
#
# use -e GDB=1
# to compile ues with debug symbols for gdb. This options adds
# corresponding compiler flags.
#
# use -e PRINT=1 
# to compile ues with debug prints. This option will not add any
# compile flags (actually it adds one) but will define a makro 
# variable named DEBUG for the preprocessor to trigger the 
# inclusion of elog statements.
#
# use -e CONFIG=path
# set a custom path for PG_CONFIG. The default paht is
# ../../postgres-server/dist/bin/pg_config
#
GDB_MODE = $(MODE)

# this are our default flags that we use every time
MYFLAGS = -Wall -Wextra -Wpedantic -Wshadow -Wconversion -Wsign-conversion -Wformat=2 -Wnull-dereference -Wdouble-promotion -Wfloat-equal -Wstack-protector -Wunreachable-code -Wstack-usage=1024
#-fsanitize=address,undefined -fstack-protector-strong

#
# add gdb compiler flags if GDB option is set
#
ifdef GDB
MYFLAGS += -ggdb -O0
$(info compile with gdb flags)
endif

#
# adds a compiler flag that defines DEBUG for preprocessor if 
# PRINT option is set
#
ifdef PRINT
MYFLAGS += -DDEBUG
$(info compile with debug prints)
endif

# transfer our custom compiler flags to PG_CFLAGS
export PG_CFLAGS = $(MYFLAGS)

#
# makes it possible to give the Makefile a custom
# pg_config location. 
#
ifdef CONFIG
PG_CONFIG = $(CONFIG)
$(info custom pg_config path set: $(CONFIG))
else
PG_CONFIG = ../../postgres-server/dist/bin/pg_config
endif

# trigger compiling
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)