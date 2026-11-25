# run datal.py in a thread with a large stack (the unbounded relative-Up recursion is deep)
import sys, threading
sys.setrecursionlimit(200000); threading.stack_size(1024 * 1024 * 1024)
def main():
    g_ = {"__name__": "__main__"}
    exec(compile(open("/tmp/claude-0/r1e/datal.py").read(), "datal.py", "exec"), g_)
th = threading.Thread(target=main); th.start(); th.join()
