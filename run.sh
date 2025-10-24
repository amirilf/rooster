if [ "$1" == "cl" ]; then
    find . -type f \( -name "*.vo" -o -name "*.aux" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" \) -delete
    exit 0
fi

FILE="$1"
if [ -f "$FILE" ]; then
    rocq compile "$FILE"
else
    echo "file '$FILE' not found!"
    exit 1
fi
