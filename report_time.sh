#!/bin/sh
#  from http://stackoverflow.com/questions/6966877/measure-time-spent-in-each-target-of-a-makefile

shift  # get rid of the '-c' supplied by make.
time sh -c "$*"
