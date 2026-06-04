CC = gcc
CFLAGS = -O2 -Wall -Werror -MMD -MP

SRCS = $(wildcard src/*.c)
OBJS = $(patsubst src/%.c,dst/%.o,$(SRCS))
DEPS = $(OBJS:.o=.d)

TESTS = $(wildcard test/*.c)
TEST_BINS = $(patsubst test/%.c,dst/%,$(TESTS))

dst/min: $(OBJS)
	$(CC) $(CFLAGS) -o $@ $(OBJS)

dst/%.o: src/%.c | dst
	$(CC) $(CFLAGS) -c -o $@ $<

dst/%: test/%.c $(OBJS) | dst
	$(CC) $(CFLAGS) -o $@ $< $(filter-out dst/main.o,$(OBJS))

dst:
	mkdir -p dst

test: $(TEST_BINS)
	@for t in $(TEST_BINS); do ./$$t || exit 1; done

clean:
	rm -rf dst

-include $(DEPS)

.PHONY: clean test
