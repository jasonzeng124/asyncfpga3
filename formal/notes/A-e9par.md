# A-e9par (probe E9Par, shard A): a log rule for parallel virtual C-elements

STATUS (2026-10-29, start): IN PROGRESS. Plan:
1. Read Events7Core/Cert, Events8Cert, Events9Cert/Beh/Main, Events9Arb(Beh), cert9.py, arbfix/.
2. Design a rule "par": grant g and its shadow s read the same ctl and the same request through
   different pin bands -> count lower bound M g >= M s - k (exact form as the Back/guard certs need).
3. Prove it sound in the Events9 induction (new Formal/Core/XAudit/Events9Par*.lean).
4. Generator in formal/tools-A/xaudit/par/, rerun 16 gcd_hw rows, negative controls.
