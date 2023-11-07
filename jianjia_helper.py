import re
import sys
import os

cmd = "tools/run-tests.py --outdir out/x64.debug/ cctest/test-taint-tracking/"
clearCmd = "rm -rf /home/suzy/temp/taint_log_file && mkdir /home/suzy/temp/taint_log_file"

def extractCases():
    filename = "test/cctest/test-taint-tracking.cc"
    with open(filename) as f:
        c = f.read()
    # print(c)
    cases = re.findall(r'TEST\((.*)\)', c)
    print(len(cases))
    return cases

os.system(clearCmd)
cases = extractCases()
if len(sys.argv)<=1:
    os.system(cmd+"*")
else:
    if sys.argv[1] in cases:
        os.system(cmd+sys.argv[1])
    else:
        num = int(sys.argv[1])
        for i in range(0, num):
            os.system(cmd+cases[i])