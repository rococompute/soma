#!/usr/bin/env python3
"""Build and boot checked TCP against local FIN/RST fixtures on Solo5/Mac.
No agents, providers or external network endpoints. Requires solo5-vmnet.
SOMA_MIRAGE_SWITCH=kykeon python3 dev/tcp-errors-check.py
"""
from contextlib import ExitStack
import os
from pathlib import Path
import queue
import signal
import socket
import struct
import subprocess
import tempfile
import threading

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "examples/example_files/mirage_tcp_errors/mirage_tcp_errors.soma"
SOMA = os.environ.get("SOMA", str(ROOT / "_build/install/default/bin/soma"))
SWITCH = os.environ.get("SOMA_MIRAGE_SWITCH", "hvf")
GATEWAY = "192.168.105.1"  # solo5-vmnet's default shared network


def exactly(conn, count):
    data = b""
    while len(data) < count:
        chunk = conn.recv(count - len(data))
        if not chunk:
            raise RuntimeError("guest closed before sending fixture bytes")
        data += chunk
    return data


def main():
    subprocess.run([SOMA, "build", str(SOURCE)], cwd=ROOT, check=True)
    errors = queue.Queue()
    with ExitStack() as stack, tempfile.TemporaryDirectory(prefix="soma-tcp-guest-") as work:
        listeners = []
        for _ in range(2):
            listener = stack.enter_context(socket.socket())
            listener.bind(("0.0.0.0", 0))
            listener.listen(1)
            listener.settimeout(40)
            listeners.append(listener)

        def serve(listener, reset):
            try:
                conn, _ = listener.accept()
                with conn:
                    conn.settimeout(15)
                    if exactly(conn, 5) != b"hello":
                        raise RuntimeError("unexpected fixture greeting")
                    if reset:
                        conn.setsockopt(socket.SOL_SOCKET, socket.SO_LINGER, struct.pack("ii", 1, 0))
                    else:
                        conn.shutdown(socket.SHUT_WR)
                        if exactly(conn, 9) != b"after EOF":
                            raise RuntimeError("checked EOF did not preserve writing")
            except Exception as error:
                errors.put(error)

        threads = [threading.Thread(target=serve, args=(listener, i == 1), daemon=True)
                   for i, listener in enumerate(listeners)]
        for thread in threads:
            thread.start()
        ports = [listener.getsockname()[1] for listener in listeners]
        command = ["opam", "exec", "--switch=" + SWITCH, "--", "solo5-vmnet", "--no-dns",
                   *[f"--allow={GATEWAY}:{port}" for port in ports], "--", "solo5-hvt", "--mem=256",
                   "--", str(SOURCE.with_suffix(".hvt")), "--arg=" + GATEWAY,
                   *["--arg=" + str(port) for port in ports]]
        log = Path(work) / "guest.log"
        with log.open("wb") as output:
            process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.DEVNULL,
                                       stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = process.wait(timeout=45)
            finally:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        process.wait()
        text = log.read_text(errors="replace")
        print(text, end="")
        if code != 0 or "TCP EOF and transport errors distinguished" not in text:
            raise RuntimeError(f"TCP guest failed (exit {code})")
        for thread in threads:
            thread.join(timeout=2)
            if thread.is_alive():
                raise RuntimeError("local fixture did not finish")
        if not errors.empty():
            raise errors.get()
        print("PASS Solo5 TCP: orderly read EOF, write after EOF, and peer reset")


if __name__ == "__main__":
    main()
