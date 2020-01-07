#!/bin/bash -e

if [ ! -e gf22fdx ]; then
   git clone git@iis-git.ee.ethz.ch:huawei/huawei_gf22fdx.git gf22fdx
fi  

pushd gf22fdx > /dev/null
git checkout huawei
git pull
popd > /dev/null

./scripts/generate-scripts-syn
