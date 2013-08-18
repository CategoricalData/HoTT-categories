#!/usr/bin/python
from __future__ import with_statement
import os, sys, re
from TimeFileMaker import *

def make_table_string(times_dict,
                      descending=True,
                      tag="Time"):
    names = get_sorted_file_list_from_times_dict(times_dict, descending=descending)
    times_width = max(max(map(len, times_dict.values())), len(sum_times(times_dict.values())))
    names_width = max(map(len, names + ["File Name", "Total"]))
    format_string = "%%-%ds | %%-%ds" % (times_width, names_width)
    header = format_string % (tag, "File Name")
    footer = format_string % (sum_times(times_dict.values()),
                              "Total")
    sep = '-' * len(header)
    return '\n'.join([header, sep] + [format_string % (times_dict[name],
                                                       name)
                                      for name in names] +
                     [sep, footer])

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Usage: %s FILE_NAME [OUTPUT_FILE_NAME]' % sys.argv[0])
        sys.exit(1)
    else:
        times_dict = get_times(sys.argv[1])
        table = make_table_string(times_dict)
        if len(sys.argv) == 2 or sys.argv[2] == '-':
            print(table)
        else:
            with open(sys.argv[2], 'w') as f:
                f.write(table)
