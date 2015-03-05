#!/usr/bin/env bash


## Configurations ##

# You have to write down your own GitHub user id.
USERID=jeehoonkang

# You have to write down the directory you want to place the repository.
WORKSPACE=~/Works


## Execution ##

# Go to the workspace.
cd $WORKSPACE

# Download the original repository.
git clone https://github.com/snu-sf/pl2015.git

# Copy.
cd pl2015
git remote rm origin
git remote add origin https://github.com/$USERID/pl2015.git
git remote add upstream https://github.com/snu-sf/pl2015.git
git push --set-upstream origin master
