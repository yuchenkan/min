#!/bin/bash
# Lint .min proof files.
# Usage: lint.sh [--git] [DIR]
#   --git : only check files git tracks or is about to track (staged), so
#           untracked work-in-progress files don't block commits. The
#           pre-commit hook uses this.
#
# 1. vocab-internal prefixed names: proofs should use clean readable names;
#    the kernel's alpha-eq handles matching with vocab expansions.
# 2. theorems library structure (only when linting the theorems tree):
#    a. each theorems/*.min exports exactly one public bind, named after the file
#    b. each theorems/*.min is qed-tested in its folder's test.min
#    c. every folder is listed (imported) in its parent folder's test.min
#    d. every folder corresponds to a vocab module / namespace dir

if [ ! -f lint.sh ]; then
    echo "error: lint.sh must be run from the poc4 directory" >&2
    exit 1
fi

GIT_ONLY=0
if [ "$1" = "--git" ]; then GIT_ONLY=1; shift; fi
DIR="${1:-theorems}"

# enumerate *.min files under DIR: tracked-or-staged with --git, else the tree.
list_files() {
    if [ "$GIT_ONLY" = 1 ]; then
        git ls-files --cached -- "$DIR/*.min"
    else
        find "$DIR" -name '*.min' | sort
    fi
}
# enumerate subdirs of DIR (mindepth 1): dirs holding listed files with --git.
list_dirs() {
    if [ "$GIT_ONLY" = 1 ]; then
        list_files | xargs -n1 dirname 2>/dev/null | sort -u | grep -vx "$DIR"
    else
        find "$DIR" -mindepth 1 -type d | sort
    fi
}

FILES="$(list_files)"

# ---- 1. vocab-internal prefixed names ----

NAME_ERRORS=0

if [ -n "$FILES" ]; then
    # "__" prefix (double underscore as string value). Exclude comment lines.
    while IFS= read -r line; do
        echo "  $line"
        NAME_ERRORS=$((NAME_ERRORS + 1))
    done < <(grep -Hn '"__"' $FILES \
        | grep -v ':[0-9]*:\s*#')

    # "_x" style names (vocab-internal bound vars) as string literals.
    # Exclude import/from lines and comments.
    while IFS= read -r line; do
        echo "  $line"
        NAME_ERRORS=$((NAME_ERRORS + 1))
    done < <(grep -Hn '"_[a-zA-Z]' $FILES \
        | grep -v ':[0-9]*:\s*from \|:[0-9]*:\s*import ' \
        | grep -v ':[0-9]*:\s*#')
fi

if [ "$NAME_ERRORS" -gt 0 ]; then
    echo ""
    echo "Found $NAME_ERRORS line(s) with vocab-internal prefixed names."
    echo "Use clean names (\"y\" not \"_y\", \"_\" not \"__\")."
    echo "The kernel's alpha-equivalence handles matching."
fi

# ---- 2. theorems library structure ----
# Only enforced on the theorems tree (skip if linting some other subtree).

STRUCT_ERRORS=0

if [ "$(basename "$DIR")" = "theorems" ] && [ -d "$DIR" ]; then

    # a. exactly one public (non-underscore) top-level bind, named after the file.
    #    $_-prefixed top-level binds are private helpers and are ignored.
    while IFS= read -r f; do
        base="$(basename "$f" .min)"
        pub="$(grep -oE '^\$[A-Za-z][A-Za-z0-9_]*' "$f" | sed 's/^\$//' | sort -u | tr '\n' ' ')"
        if [ "$pub" != "$base " ]; then
            echo "  $f: public bind(s) [${pub% }] — expected exactly [$base]"
            STRUCT_ERRORS=$((STRUCT_ERRORS + 1))
        fi
    done < <(printf '%s\n' $FILES | grep -v '/test\.min$')

    # b. qed-tested in its folder's test.min, directly (qed(foo,...) / qed(foo(...)))
    #    or via a one-hop local variable bound to the theorem ($x foo(...); qed(x,...)).
    while IFS= read -r f; do
        base="$(basename "$f" .min)"
        t="$(dirname "$f")/test.min"
        if [ ! -f "$t" ]; then
            echo "  $f: no test.min in its folder"
            STRUCT_ERRORS=$((STRUCT_ERRORS + 1))
            continue
        fi
        # candidates: the theorem itself + any var bound to an expr mentioning it
        cands="$base $(grep -oE "^[[:space:]]*\\\$[A-Za-z_][A-Za-z0-9_]*[[:space:]].*\\b$base\\b" "$t" \
            | sed -E 's/^[[:space:]]*\$([A-Za-z_][A-Za-z0-9_]*).*/\1/')"
        tested=no
        for c in $cands; do
            if grep -qE "qed\($c[,()]" "$t"; then tested=yes; break; fi
        done
        if [ "$tested" = no ]; then
            echo "  $f: not qed-tested in $t"
            STRUCT_ERRORS=$((STRUCT_ERRORS + 1))
        fi
    done < <(printf '%s\n' $FILES | grep -v '/test\.min$')

    # c. every subfolder is imported in its parent's test.min
    #    (convention: from theorems.<...>.<sub>.test import ...)
    while IFS= read -r d; do
        parent="$(dirname "$d")"
        sub="$(basename "$d")"
        pt="$parent/test.min"
        if [ ! -f "$pt" ]; then
            echo "  $d: parent has no test.min ($pt)"
            STRUCT_ERRORS=$((STRUCT_ERRORS + 1))
            continue
        fi
        if ! grep -qE "\.$sub\.test import" "$pt"; then
            echo "  $d: not listed in parent test.min ($pt)"
            STRUCT_ERRORS=$((STRUCT_ERRORS + 1))
        fi
    done < <(list_dirs)

    # d. theorems mirror vocab: a theorems/<P> folder holds the theorems about the
    #    vocab named <P>, so it must correspond to vocab/<P>.min (a module) or
    #    vocab/<P>/ (a namespace dir). vocab without theorems is allowed (proofs
    #    may lag definitions); a theorems folder without vocab is not.
    VOCAB="$(dirname "$DIR")/vocab"
    if [ -d "$VOCAB" ]; then
        while IFS= read -r d; do
            rel="${d#"$DIR"/}"
            if [ ! -f "$VOCAB/$rel.min" ] && [ ! -d "$VOCAB/$rel" ]; then
                echo "  $d: no corresponding vocab ($VOCAB/$rel.min or $VOCAB/$rel/)"
                STRUCT_ERRORS=$((STRUCT_ERRORS + 1))
            fi
        done < <(list_dirs)
    fi

    if [ "$STRUCT_ERRORS" -gt 0 ]; then
        echo ""
        echo "Found $STRUCT_ERRORS theorems-structure violation(s)."
        echo "Each theorems/*.min must (a) export exactly one public bind = its filename,"
        echo "(b) be qed-tested in its folder's test.min; (c) every folder must be listed"
        echo "in its parent folder's test.min; and (d) every folder must correspond to a"
        echo "vocab module (vocab/<path>.min) or namespace dir (vocab/<path>/)."
    fi
fi

# ---- summary ----

if [ "$((NAME_ERRORS + STRUCT_ERRORS))" -gt 0 ]; then
    exit 1
fi
echo "lint: clean (names + theorems structure)."
exit 0
