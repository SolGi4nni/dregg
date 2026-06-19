#!/usr/bin/env python3
"""Boot the deos-image seL4 image, drive the keyboard over QMP, and screendump
BOTH modes — the live image AND the starbridge-v2 cockpit (TAB) — to PNG.

This is the evidence-capture for the gpui-offscreen -> seL4 framebuffer weld:
the cockpit frame is a REAL gpui render (lavapipe, no GPU) baked into the PD and
blitted onto the ramfb framebuffer QEMU scans out (sel4/dregg-pd/deos-image/
cockpit_frame.rs). We boot headless (-display none), let the PD configure ramfb +
paint the live image, screendump it, then `send-key` TAB (evdev keycode 15) so
the PD's notified() handler toggles to Cockpit mode + blits the gpui frame, and
screendump again.

No external deps (macOS has no socat): QMP is driven over the unix socket with
the stdlib. The virtio-keyboard is on virtio-mmio slot 30 exactly as
deos-image.system maps it; QMP `send-key` injects into it via the qcode.
"""
import json
import os
import socket
import subprocess
import sys
import time

SEL4 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMG = os.path.join(SEL4, "build", "deos-image.img")
QMP_SOCK = "/tmp/deos-image-qmp.sock"
SERIAL_LOG = "/tmp/deos-image-serial.log"
OUT_IMAGE = "/tmp/sel4-cockpit-image-mode.png"
OUT_COCKPIT = "/tmp/sel4-cockpit-cockpit-mode.png"
OUT_COCKPIT_NAV = "/tmp/sel4-cockpit-cockpit-nav-mode.png"


class Qmp:
    def __init__(self, path):
        # Wait for QEMU to create the socket.
        for _ in range(100):
            if os.path.exists(path):
                break
            time.sleep(0.1)
        self.s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        for _ in range(100):
            try:
                self.s.connect(path)
                break
            except (FileNotFoundError, ConnectionRefusedError):
                time.sleep(0.1)
        else:
            raise RuntimeError("could not connect to QMP socket")
        self.f = self.s.makefile("rwb", buffering=0)
        self._recv()  # the greeting
        self._cmd("qmp_capabilities")

    def _recv(self):
        while True:
            line = self.f.readline()
            if not line:
                raise RuntimeError("QMP socket closed")
            msg = json.loads(line)
            # Skip async events; return command results / greetings.
            if "event" in msg:
                continue
            return msg

    def _cmd(self, execute, **arguments):
        req = {"execute": execute}
        if arguments:
            req["arguments"] = arguments
        self.f.write((json.dumps(req) + "\n").encode())
        return self._recv()

    def screendump(self, filename):
        # format=png needs QEMU >= 7.1; fall back to ppm if rejected.
        r = self._cmd("screendump", filename=filename, format="png")
        if "error" in r:
            ppm = filename.rsplit(".", 1)[0] + ".ppm"
            r = self._cmd("screendump", filename=ppm)
            return ppm, r
        return filename, r

    def send_tab(self):
        # qcode "tab" -> the virtio-keyboard. press + release.
        return self._cmd(
            "send-key",
            keys=[{"type": "qcode", "data": "tab"}],
        )

    def send_key(self, qcode):
        # any qcode -> the virtio-keyboard. press + release.
        return self._cmd("send-key", keys=[{"type": "qcode", "data": qcode}])

    def close(self):
        try:
            self._cmd("quit")
        except Exception:
            pass
        self.s.close()


def wait_for_serial(needle, timeout=40):
    """Poll the serial log for a marker line."""
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            with open(SERIAL_LOG, "r", errors="replace") as fh:
                if needle in fh.read():
                    return True
        except FileNotFoundError:
            pass
        time.sleep(0.25)
    return False


def main():
    if not os.path.exists(IMG):
        print(f"FAIL: {IMG} not found — run `make build-image` first", file=sys.stderr)
        return 2
    for p in (QMP_SOCK, SERIAL_LOG, OUT_IMAGE, OUT_COCKPIT):
        try:
            os.remove(p)
        except FileNotFoundError:
            pass

    qemu = [
        "qemu-system-aarch64",
        "-machine", "virt,virtualization=on",
        "-cpu", "cortex-a53",
        "-m", "2G",
        "-device", "ramfb",
        "-display", "none",
        "-global", "virtio-mmio.force-legacy=false",
        "-device", "virtio-keyboard-device,bus=virtio-mmio-bus.30",
        "-device", f"loader,file={IMG},addr=0x70000000,cpu-num=0",
        "-serial", f"file:{SERIAL_LOG}",
        "-qmp", f"unix:{QMP_SOCK},server,nowait",
    ]
    print("booting:", " ".join(qemu))
    proc = subprocess.Popen(qemu)
    try:
        # Wait for ramfb to be configured (the PD prints this once scanout is live).
        if not wait_for_serial("ramfb CONFIGURED", timeout=40):
            print("FAIL: ramfb never configured (see serial log)", file=sys.stderr)
            with open(SERIAL_LOG, errors="replace") as fh:
                print(fh.read())
            return 3
        # Let the first frame settle.
        time.sleep(1.0)

        q = Qmp(QMP_SOCK)

        # (1) the LIVE IMAGE mode.
        f1, r1 = q.screendump(OUT_IMAGE)
        print(f"captured IMAGE mode -> {f1}  ({r1})")
        time.sleep(0.5)

        # (2) TAB -> the COCKPIT mode (the PD toggles + blits the gpui frame).
        rk = q.send_tab()
        print(f"sent TAB ({rk})")
        # Wait for the PD to log the mode switch + repaint.
        if not wait_for_serial("MODE: the starbridge-v2 COCKPIT", timeout=10):
            print("WARN: did not see the cockpit-mode serial marker; capturing anyway")
        time.sleep(1.0)
        f2, r2 = q.screendump(OUT_COCKPIT)
        print(f"captured COCKPIT mode -> {f2}  ({r2})")
        time.sleep(0.5)

        # (3) RIGHT, RIGHT, ENTER -> move the cockpit focus cursor to AGENT and
        # select it (cockpit mode now CONSUMES nav). The PD logs the focus move
        # + repaints the overlay; capture proves the cursor moved on glass.
        q.send_key("right")
        q.send_key("right")
        q.send_key("ret")
        if not wait_for_serial("cockpit tab focus AGENT (selected AGENT)", timeout=10):
            print("WARN: did not see the cockpit-nav serial marker; capturing anyway")
        time.sleep(1.0)
        f3, r3 = q.screendump(OUT_COCKPIT_NAV)
        print(f"captured COCKPIT-NAV mode -> {f3}  ({r3})")

        time.sleep(0.5)
        q.close()
        print("OK")
        return 0
    finally:
        time.sleep(0.5)
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()


if __name__ == "__main__":
    sys.exit(main())
