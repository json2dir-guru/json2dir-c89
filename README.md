# json2dir-c89

json2dir in ANSI C (C89): create the directory tree a JSON document describes.

    gcc -std=c89 -pedantic-errors -o json2dir json2dir.c && ./json2dir < document.json
