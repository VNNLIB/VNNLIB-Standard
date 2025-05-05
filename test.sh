# !/bin/bash
for f in test/*.vnnlib ;
do 
  output=$(VNNLibLBNF/Test "$f" 2>&1)
  if (( $? )); then
    echo >&2 "error $?: \"$output\""
    echo "$f" >> test/error-files.txt
    # break
  else
    echo "parse success: $f"
  fi
done