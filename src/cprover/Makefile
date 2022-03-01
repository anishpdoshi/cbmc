SRC = console.cpp \
      cprover_main.cpp \
      cprover_parse_options.cpp \
      equality_propagation.cpp \
      free_symbols.cpp \
      help_formatter.cpp \
      state_encoding.cpp \
      state_encoding_targets.cpp \
      solver.cpp \
      wcwidth.c \
      # Empty last line

include ../config.inc
include ../common

OBJ += ../util/util$(LIBEXT) \
       ../big-int/big-int$(LIBEXT) \
       ../goto-programs/goto-programs$(LIBEXT) \
       ../ansi-c/ansi-c$(LIBEXT) \
       ../linking/linking$(LIBEXT) \
       ../langapi/langapi$(LIBEXT) \
       ../solvers/solvers$(LIBEXT) \
       # Empty last line

INCLUDES= -I ..

LIBS = 

CLEANFILES = cprover$(EXEEXT)

all: cprover$(EXEEXT)

###############################################################################

cprover$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: cprover-signed
cprover-signed: cprover$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) cprover$(EXEEXT)
