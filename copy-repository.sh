#!/usr/bin/env bash

## Usage: USERID=jeehoonkang WORKSPACE=~ ./copy-repository.sh

## Configurations ##

# You have to write down your own GitHub user id.
if [ -z $USERID ] ; then
  echo "You have to specify USERID."
  exit 1
fi

# You have to write down the directory you want to place the repository.
if [ -z $WORKSPACE ] ; then
  echo "You have to specify WORKSPACE."
  exit 1
fi

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
