#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source "$DIR/pushd-root.sh" 1>/dev/null

MAKE="$1"
NEW_FILE="$2"
OLD_FILE="$3"

SHELF_NAME="compare-times-shelf"

if [ ! -z "$OLD_FILE" ]; then
    trap "hg import --no-commit $SHELF_NAME" SIGINT SIGTERM

    # make the old version
    #hg shelve --all --name $SHELF_NAME
    hg diff > $SHELF_NAME && hg revert -a
    make clean
    $MAKE TIMED=1 -k 2>&1 | tee "$OLD_FILE"


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
	$MAKE TIMED=1 -k 2>&1 | tee "$NEW_FILE"
    fi
else
    make clean
    $MAKE TIMED=1 -k 2>&1 | tee "$NEW_FILE"
fi

popd 1>/dev/null
