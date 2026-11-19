"""Timestamped progress messages for long replays."""

import time

_START = time.monotonic()


def elapsed():
    seconds = int(time.monotonic() - _START)
    return f"{seconds // 3600}:{seconds // 60 % 60:02d}:{seconds % 60:02d}"


def log(message):
    print(f"[{elapsed()}] {message}", flush=True)


class Progress:
    """Report a running count at most every `interval` seconds."""

    def __init__(self, label, total=None, interval=30):
        self.label, self.total, self.interval = label, total, interval
        self.count, self.last = 0, time.monotonic()

    def update(self, step=1):
        self.count += step
        now = time.monotonic()
        if now - self.last >= self.interval:
            self.last = now
            of = f"/{self.total:,}" if self.total else ""
            log(f"{self.label}: {self.count:,}{of}")
