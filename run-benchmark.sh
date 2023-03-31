#!/bin/bash

BASEDIR=$(dirname "$0")

cd ${BASEDIR}

# create output product directory
mkdir -p output

# if there is a build directory, point Paraview to the plugins
test -d build && export PV_PLUGIN_PATH=$(pwd)/build/lib/TopologyToolKit
test -d build && export LD_LIBRARY_PATH=$(pwd)/build/lib

# run benchmark scripts
/usr/local/bin/pvpython data/teaser-pathmapping.py
/usr/local/bin/pvpython data/teaser-wasserstein.py
