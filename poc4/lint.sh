#!/bin/bash
# Lint .min proof files for vocab-internal prefixed names
# These should be clean readable names; the kernel's alpha-eq handles matching.

ERRORS=0
DIR="${1:-theorems}"

# Check for "__" prefix (double underscore as string value)
# Exclude comments (# after optional whitespace in the content part)
while IFS= read -r line; do
    echo "  $line"
    ERRORS=$((ERRORS + 1))
done < <(grep -rn '"__"' "$DIR" --include="*.min" \
    | grep -v ':[0-9]*:\s*#')

# Check for "_x" style variable names (vocab-internal bound var names)
# Match: "_" followed by a letter, as a string literal
# Exclude: import/from lines, comments
while IFS= read -r line; do
    echo "  $line"
    ERRORS=$((ERRORS + 1))
done < <(grep -rn '"_[a-zA-Z]' "$DIR" --include="*.min" \
    | grep -v ':[0-9]*:\s*from \|:[0-9]*:\s*import ' \
    | grep -v ':[0-9]*:\s*#')

if [ "$ERRORS" -gt 0 ]; then
    echo ""
    echo "Found $ERRORS lines with vocab-internal prefixed names."
    echo "Use clean names (\"y\" not \"_y\", \"_\" not \"__\")."
    echo "The kernel's alpha-equivalence handles matching."
    exit 1
else
    echo "No vocab-internal prefixed names found."
    exit 0
fi
