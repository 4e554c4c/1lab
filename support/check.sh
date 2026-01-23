#!/bin/sh

set -e

# Beautiful AWK script to generate _build/all-pages.agda and check it,
# possibly with a specified version of Agda (use the AGDA environment
# variable).

agda="${AGDA:-agda}"

if ! command -v "${agda}" 2>/dev/null; then
  echo "${agda} is not executable. Either add it to your path or set \$AGDA."
  exit 1
else
  echo ">>> Checking with ${agda} ($(type "${agda}"))"
fi

git ls-files --full-name src/ | awk "$(cat<<'EOF'
BEGIN{
  num_files = 0;
}
/\.lagda\.md$/ || /\.agda$/ {
  ++num_files;
  gsub(/^src\//, "");
  gsub(/\.lagda\.md|\.agda$/, "");
  gsub(/\//, ".");
  print "open import " $0;
}
END {
  print ">>> Checking " num_files " modules" > "/dev/stderr";
}
EOF
)" | sort > _build/all-pages.agda

$agda _build/all-pages.agda --trace-imports=3 ${AGDAFLAGS}
