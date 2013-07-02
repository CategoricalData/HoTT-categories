#!/usr/bin/python
from __future__ import with_statement
import os, sys, re

def get_times(file_name):
    with open(file_name, 'r') as f:
        lines = f.readlines()
    lines = [i for i in
             [re.sub('"?coqc"?.*?\\s([^\\s]+)$', r'coqc \1', i.replace('\n', '').strip())
              for i in lines]
             if i[:4] in ('coqc', 'real')]
    times_dict = {}
    for i in range(len(lines) - 1):
        if lines[i][:4] == 'coqc':
            if lines[i + 1][:4] == 'real':
                name = lines[i][4:].strip()
                time = lines[i + 1][4:].strip()
                minutes, seconds = time.split('m')
                if seconds[0].isdigit() and seconds[1] == '.':
                    # we want,e.g., 0m05.111s, not 0m5.111s
                    seconds = '0' + seconds
                time = '%sm%s' % (minutes, seconds)
                times_dict[name] = time
    return times_dict

def get_sorted_file_list_from_times_dict(times_dict, descending=True):
    def get_key(name):
        minutes, seconds = times_dict[name].replace('s', '').split('m')
        return (int(minutes), float(seconds))
    return sorted(times_dict.keys(), key=get_key, reverse=descending)

def sum_times(times):
    def to_seconds(time):
        minutes, seconds = time.replace('s', '').split('m')
        return int(minutes) * 60 + float(seconds)
    seconds = sum(map(to_seconds, times))
    minutes = int(seconds) / 60
    seconds -= minutes * 60
    full_seconds = int(seconds)
    partial_seconds = int(1000 * (seconds - full_seconds))
    return '%dm%02d.%03ds' % (minutes, full_seconds, partial_seconds)
