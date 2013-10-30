#!/bin/bash

echo -e "\e[1;32m"
echo -e "***************************************************************"
echo -e "POSITIVE TESTS"
echo -e "\e[0m"

for FN in `ls ../tests/simple-0/ | grep "^[^\.]*\.[ij]s$"`
do
  echo -n "../tests/simple-0/$FN  "
  ./impscript ../tests/simple-0/$FN | tail -1
done

