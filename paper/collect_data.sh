set -ex
cd "$(dirname "$0")/.."

# Collect proof line counts per day from git history.
# Counts poc4/theorems/*.min (excluding test.min).
git log --all --reverse --oneline --format="%H" -- poc4/theorems/ | while read hash; do
  total=0
  for f in $(git ls-tree -r --name-only "$hash" -- poc4/theorems/ 2>/dev/null \
             | grep '\.min$' | grep -v 'test\.min$'); do
    n=$(git show "$hash:$f" 2>/dev/null | wc -l)
    total=$((total + n))
  done
  if [ "$total" -gt 0 ]; then
    date=$(git show -s --format="%ai" "$hash" | cut -d' ' -f1)
    echo "$date $total"
  fi
done | awk '{if($2>max[$1]) max[$1]=$2} END {for(d in max) print d, max[d]}' | sort
