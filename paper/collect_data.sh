set -ex
cd "$(dirname "$0")/.."

# Collect proof line counts per day from git history.
# Handles both pre-split (src/theorems.py) and post-split (src/theorems/*.py).
git log --all --reverse --oneline --format="%H" | while read hash; do
  old=$(git show "$hash:src/theorems.py" 2>/dev/null | wc -l)
  new=0
  for f in logic.py sets.py omega.py recursion.py arithmetic.py tm.py axioms.py; do
    n=$(git show "$hash:src/theorems/$f" 2>/dev/null | wc -l)
    new=$((new + n))
  done
  total=$((old + new))
  if [ "$total" -gt 0 ]; then
    date=$(git show -s --format="%ai" "$hash" | cut -d' ' -f1)
    echo "$date $total"
  fi
done | awk '{if($2>max[$1]) max[$1]=$2} END {for(d in max) print d, max[d]}' | sort
