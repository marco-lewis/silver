silq --ast-dump $1
file_name="${1#*/}"
file_name="${file_name%\.*}"
new_loc="tests/${file_name}.json"
out="${1%\.*}.json"
mv "${out}" "${new_loc}"