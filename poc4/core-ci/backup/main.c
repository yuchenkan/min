#include "eval.h"

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: core-ci/min <file.min>\n");
        return 1;
    }

    root_dir = ".";

    load_file(argv[1]);
    return 0;
}
