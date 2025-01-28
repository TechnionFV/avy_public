#! /bin/bash

DIR="/home/dekel/CLionProjects/btor-analyzer/hwmcc20/btor2/bv/2020/mann/s*"
for f in $DIR
do
  echo ""
  echo "************************************** running $f **************************************"
  /home/dekel/CLionProjects/extavy/cmake-build-debug/avy/src/avybtor "$f"
  ret_code=$?

  if [[ "$ret_code" == "1" ]]; then
       echo ""
       echo "SUCCESS"
  else
       echo
       echo "FAILED"
  fi
done

