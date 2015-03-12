#!/usr/bin/env bash

## Usage: ./fetch-homework.sh

# Make sure that `upstream` points to the valid offical repository.
git remote rm upstream
git remote add upstream https://github.com/snu-sf/pl2015.git

# Download and update.
git fetch upstream
git merge upstream/master
