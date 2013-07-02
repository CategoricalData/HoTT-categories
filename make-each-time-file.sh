#!/bin/bash

NEW_FILE="$1"
OLD_FILE="$2"

SHELF_NAME="compare-times-shelf"

if [ ! -z "$OLD_FILE" ]; then
    trap "hg import --no-commit $SHELF_NAME" SIGINT SIGTERM

    # make the old version
    #hg shelve --all --name $SHELF_NAME
    hg diff > $SHELF_NAME && hg revert -a
    make clean
    make timed 2>&1 | tee "$OLD_FILE"


    # make the current version
    if [ -z "$(cat $SHELF_NAME)" ]; then
        # there is no diff, so just copy the time file
	cp "$OLD_FILE" "$NEW_FILE"
    else
	if [ -z "$(hg diff)" ]; then
	    hg revert -a # clean up any, e.g., chmod +x
	fi
	hg import --no-commit $SHELF_NAME && mv $SHELF_NAME "$SHELF_NAME-$(date | base64).bak"
	make clean
	make timed 2>&1 | tee "$NEW_FILE"
    fi
else
    make clean
    make timed 2>&1 | tee "$NEW_FILE"
fi
