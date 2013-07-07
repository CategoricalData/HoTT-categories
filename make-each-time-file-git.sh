#!/bin/bash

MAKE="$1"
NEW_FILE="$2"
OLD_FILE="$3"

if [ ! -z "$OLD_FILE" ]; then
    # make the old version
    CHANGE="$(git stash)"
    trap "git stash pop" SIGINT SIGTERM
    
    make clean
    $MAKE TIMED=1 -k 2>&1 | tee "$OLD_FILE"


    # make the current version
    if [ ! -z "$(echo "$CHANGE" | grep "No local changes to save")" ]; then
        # there is no diff, so just copy the time file
	cp "$OLD_FILE" "$NEW_FILE"
    else
	git stash pop
	trap "" SIGINT SIGTERM
	make clean
	$MAKE TIMED=1 -k 2>&1 | tee "$NEW_FILE"
    fi
else
    make clean
    $MAKE TIMED=1 -k 2>&1 | tee "$NEW_FILE"
fi
