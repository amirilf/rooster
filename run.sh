if [ "$1" = "build" ]; then
    find . -name "*.v" -exec rocq compile -Q . SF {} \;
    
elif [ "$1" = "clean" ]; then
    find . -type f \( -name "*.vo" -o -name "*.vok" -o -name "*.vos" -o -name "*.glob" -o -name "*.aux" -o -name ".*.aux" \) -delete
    
elif [ "$1" = "file" ]; then
    rocq compile -Q . SF "$2"
    
else
    echo "Usage:"
    echo "  ./run.sh build"
    echo "  ./run.sh clean"
    echo "  ./run.sh file <path.v>"
fi
