#!/bin/zsh

set -e
# 0: 29094e006d4c88f51d744b0fd26f3e2e18af3ce0 # baseline
# 1: f8d4ee7ee0d3d617c6d30401592f5639be60b14a # GHC options
# 2: 54b87689f345173dbed3510a396641cd8c5e43f2 # IORefs instead of MVars
# 3: b06413d43cecc33ff40b21836e7c88523ab4929f # sequential task execution
# 4: 7ca773e347dae952d4c7249a0310f10077a2474b # manual query parallelisation
# 5: 8ea6700415f1c46fb300571382ef438ae6082e8e # parser lookahead
# 6: 722533c5d71871ca1aa6235fe79a53f33da99c36 # dependent hashmap
# 7: 048d2cec50e9994a0b159a2383580e3df5dd2a7e # ReaderT in rock
# 8: 11c46c5b03f26a66347d5f387bd4cdfd5f6de4a2 # separate lexer
# 9: d5bad6f606450d0a2c8926072e7b4845d982b81f # speed up hashing

index=0

for commit in \
  29094e006d4c88f51d744b0fd26f3e2e18af3ce0 \
  f8d4ee7ee0d3d617c6d30401592f5639be60b14a \
  54b87689f345173dbed3510a396641cd8c5e43f2 \
  b06413d43cecc33ff40b21836e7c88523ab4929f \
  7ca773e347dae952d4c7249a0310f10077a2474b \
  8ea6700415f1c46fb300571382ef438ae6082e8e \
  722533c5d71871ca1aa6235fe79a53f33da99c36 \
  048d2cec50e9994a0b159a2383580e3df5dd2a7e \
  11c46c5b03f26a66347d5f387bd4cdfd5f6de4a2 \
  d5bad6f606450d0a2c8926072e7b4845d982b81f \
  ;
do
  git checkout $commit

  GHC_OPTIONS=""
  if [[ "$commit" = "29094e006d4c88f51d744b0fd26f3e2e18af3ce0" ]]; then
    GHC_OPTIONS="--ghc-options=-threaded -rtsopts -with-rtsopts=-N"
  fi

  stack install --force-dirty $GHC_OPTIONS
  bench 'sixty check' --output output/$index-$commit.time

  stack install --force-dirty --ghc-options="-eventlog" $GHC_OPTIONS
  sixty check +RTS -la
  mv sixty.eventlog output/$index-$commit.eventlog

  stack install --force-dirty --profile $GHC_OPTIONS
  sixty check +RTS -p
  stack exec --package ghc-prof-flamegraph -- ghc-prof-flamegraph sixty.prof
  mv sixty.prof output/$index-$commit.prof
  mv sixty.svg output/$index-$commit.svg

  ((++index))
done
