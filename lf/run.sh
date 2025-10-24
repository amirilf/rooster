if [ "$1" == "cl" ]; then
    find . -type f \( -name "*.vo" -o -name "*.aux" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" \) -delete
    exit 0
fi

declare -A compiled

compile_file() {
    local f="$1"
    [ ! -f "$f" ] && return 1
    [ "${compiled["$f"]}" ] && return 0

    grep 'From LF\.' "$f" | while read -r line; do
        dep=$(echo "$line" | sed -E 's/From LF\.([a-zA-Z0-9_]+) Require Import ([a-zA-Z0-9_]+)\.?/\1\/\2.v/')
        [ -f "$dep" ] && compile_file "$dep"
    done

    rocq compile -Q . LF "$f"
    compiled["$f"]=1
}

compile_file "$1"
