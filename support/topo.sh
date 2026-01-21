#!/bin/sh

script=$(cat <<'EOF'
@load "filefuncs"
function exists(file) {
	return stat(file, null) == 0;
}

/^open import/ {
	path = $3
	gsub(/\./, "/", path);
	path = "src/" path
	if (exists(path ".lagda.md")) {
		path = path ".lagda.md";
	} else if (exists(path ".agda")) {
		path = path ".agda";
	} else {
		print "unable to find path: " path > "/dev/stderr";
	}
	print FILENAME, path;
}
EOF
);


find src -type f '(' -name '*.lagda.md' -o -name '*.agda' ')' -exec gawk "$script" {} ';'  | tsort | tac
