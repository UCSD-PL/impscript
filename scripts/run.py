#!/usr/bin/python

import os, re, sys

# http://stackoverflow.com/questions/287871/print-in-terminal-with-colors-using-python
class bcolors:
    PURPLE = '\033[95m'
    BLUE = '\033[94m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    ENDC = '\033[0m'

root_dir = os.getenv('IMPSCRIPT_DIR') # TODO
test_dir = '../tests/'

def printHeader(color, s):
    print color
    print 80 * "*"
    print "*** " + s
    print 80 * "*"
    print bcolors.ENDC

def runTests(color, header, pattern):
    printHeader(color, header)
    for top, _, files in os.walk(test_dir):
        for nm in files:       
            if re.match(pattern, nm):
                f = os.path.join(top, nm)
                print f + " ",
                sys.stdout.flush()
                os.system("./impscript %s %s | tail -1" % ("", f))
                sys.stdout.flush()

runTests(bcolors.YELLOW, "UNANNOTATED JAVASCRIPT (MAY FAIL)", ".*.js$")

runTests(bcolors.RED, "NEGATIVE TESTS", "^xx[^.]*.is$")

runTests(bcolors.GREEN, "POSITIVE TESTS", "[^x][^x][^.]*.is$")
