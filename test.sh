# !/bin/bash
for f in test/*.vnnlib ;
do 
  output=$(Syntax/Test "$f" 2>&1)
  exit_code=$?
  if (( exit_code != 0 )); then
    echo >&2 "error $exit_code: \"$output\""
    exit $exit_code # break
  else
    echo "parse success: $f"
  fi
done