# Makefile
# 19-Nov-11 Markku-Juhani O. Saarinen <mjos@iki.fi>

BINARY          = kctest
OBJS     	= keccak.o main.o 
DIST            = readable_keccak

CC              = gcc
CFLAGS		= -Wall -O
LIBS            = 
LDFLAGS         =
INCLUDES	=

$(BINARY):      $(OBJS)
		$(CC) $(LDFLAGS) -o $(BINARY) $(OBJS) $(LIBS)

.c.o:
		$(CC) $(CFLAGS) $(INCLUDES) -c $< -o $@

clean:
		rm -rf $(DIST).tgz $(OBJS) $(BINARY) *~ 

dist:           clean
		cd ..; tar cfvz $(DIST)/$(DIST).tgz $(DIST)/*
