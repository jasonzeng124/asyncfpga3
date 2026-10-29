import os, sys
mode = os.environ.get("FAKE_MODE")
bit = sys.argv[sys.argv.index("--bit") + 1] if "--bit" in sys.argv else ""
unp = "unpatched" in bit
if mode == "empty":
    sys.exit(0)
if mode == "garbled":
    print("Segmentation fault (core dumped)"); sys.exit(139)
if mode == "pass_rc1":
    print("SOAK stalled PASS lat=1"); print("SOAK_VERDICT PASS"); sys.exit(1)
if mode == "crash_on_unpatched":
    if unp:
        print("SOAK all FAIL: gen.py failed, see /x/generate.log"); print("SOAK_VERDICT FAIL"); sys.exit(1)
    print("SOAK stalled PASS lat=1"); print("SOAK fast PASS lat=1"); print("SOAK_VERDICT PASS"); sys.exit(0)
