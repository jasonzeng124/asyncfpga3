# run datal_t.py in a thread with a large stack (C's unbounded relative-Up recursion is deep)
import sys, threading
sys.setrecursionlimit(400000); threading.stack_size(1024 * 1024 * 1024)
def main():
    sys.argv = ["datal_t.py"] + sys.argv[1:]
    g_ = {"__name__": "__main__"}
    exec(compile(open("/tmp/claude-0/bsub1/tocc/datal_t.py").read(), "datal_t.py", "exec"), g_)
th = threading.Thread(target=main); th.start(); th.join()
