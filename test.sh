# !/bin/bash
echo -n "Enter Grammar File: " 
read Filename

bnfc -d -m $Filename &&  make

Parser=${Filename//"_"/}
Parser=${Parser//".cf"/}

for f in test/*.vnnlib ;
do 
  output=$("$Parser"/Test "$f" 2>&1)
  if (( $? )); then
  echo >&2 "error $?: \"$output\""
  break
  else
    echo "make success: $f"
  fi
done