CC = gcc
CFLAGS = -O2 -Wall -MMD -MP
LDFLAGS =

SRCS = gc.c val.c parse.c kernel.c eval.c main.c
OBJS = $(SRCS:.c=.o)
DEPS = $(SRCS:.c=.d)

min: $(OBJS)
	$(CC) $(CFLAGS) -o $@ $(OBJS) $(LDFLAGS)

%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

clean:
	rm -f min $(OBJS) $(DEPS)

-include $(DEPS)

.PHONY: clean
