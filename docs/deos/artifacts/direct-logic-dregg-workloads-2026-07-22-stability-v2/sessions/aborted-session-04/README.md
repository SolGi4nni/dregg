# Aborted orchestration attempt

This process was sent SIGHUP after the parent SSH command exceeded the local
tool's bounded execution window.  It ended after the two Admission tamper
checks and before any timing samples.  It is retained as an operational audit
record and excluded by `analyze.py`, which only reads `session-*/raw.log`.
