# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import atexit
import json
import os
import shutil
import signal
import socket
from subprocess import run
import sys
import time
import serial


class QemuMonitor:
    """QMP monitor and GPIO socket controller for OpenTitan QEMU."""

    # SW_STRAP_MASK = bits 24..22 (0x01c00000); invert for data_bi = 0xfe3fffff
    # SW_STRAP_RMA_ENTRY = GPIO24=1, GPIO23=1, GPIO22=0 (0x01800000)
    GPIO_RMA_STRAP_SET_CMD = b"M:fe3fffff\nI:01800000\n"
    GPIO_RMA_STRAP_CLR_CMD = b"M:ffffffff\nI:00000000\n"

    def __init__(self, monitor_path=None, gpio_path=None):
        self.monitor_path = monitor_path or os.environ.get("QEMU_MONITOR", "qemu-monitor")
        self.gpio_path = gpio_path or os.environ.get("QEMU_GPIO", "qemu-gpio.sock")
        self._sock = None
        self._sock_file = None
        self._gpio_sock = None
        self._cmd_id = 0
        self.always_rma_strap = False
        self._pc_tracing = False

    def connect(self):
        self.close()
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        sock.settimeout(5.0)
        sock.connect(self.monitor_path)
        sock_file = sock.makefile("r", encoding="utf-8")
        # Read QMP greeting
        greeting = sock_file.readline()
        if not greeting:
            sock.close()
            raise RuntimeError("Empty QMP greeting from QEMU monitor")
        self._sock = sock
        self._sock_file = sock_file
        self.cmd("qmp_capabilities")
        log_dir = os.environ.get("TEST_UNDECLARED_OUTPUTS_DIR")
        if log_dir:
            qemu_log_path = os.path.join(log_dir, "qemu.log")
            try:
                self.cmd(
                    "human-monitor-command",
                    {"command-line": f"logfile {qemu_log_path}"},
                )
            except Exception:
                pass

    def close(self):
        if self._sock_file:
            try:
                self._sock_file.close()
            except Exception:
                pass
            self._sock_file = None
        if self._sock:
            try:
                self._sock.close()
            except Exception:
                pass
            self._sock = None

    def close_gpio(self):
        if self._gpio_sock:
            try:
                self._gpio_sock.close()
            except Exception:
                pass
            self._gpio_sock = None

    def set_gpio_rma_strap(self, enabled: bool):
        """Asserts or deasserts SW_STRAP_RMA_ENTRY on QEMU's ot-gpio-eg chardev."""
        cmd_bytes = self.GPIO_RMA_STRAP_SET_CMD if enabled else self.GPIO_RMA_STRAP_CLR_CMD
        if self._gpio_sock is not None:
            try:
                self._gpio_sock.sendall(cmd_bytes)
                return
            except Exception:
                self.close_gpio()

        if not os.path.exists(self.gpio_path):
            return
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        sock.settimeout(2.0)
        try:
            sock.connect(self.gpio_path)
            sock.sendall(cmd_bytes)
            self._gpio_sock = sock
        except Exception:
            sock.close()
            raise

    def cmd(self, execute, arguments=None):
        for attempt in range(2):
            try:
                if self._sock is None:
                    self.connect()
                self._cmd_id += 1
                req_id = self._cmd_id
                payload = {"execute": execute, "id": req_id}
                if arguments is not None:
                    payload["arguments"] = arguments
                msg = (json.dumps(payload) + "\n").encode("utf-8")
                self._sock.sendall(msg)
                while True:
                    line = self._sock_file.readline()
                    if not line:
                        raise ConnectionError("QMP connection closed by QEMU")
                    resp = json.loads(line)
                    if "event" in resp:
                        continue
                    if resp.get("id") == req_id:
                        if "error" in resp:
                            raise RuntimeError(f"QMP error on {execute}: {resp['error']}")
                        return resp.get("return")
            except Exception:
                self.close()
                if attempt == 1:
                    raise

    def _trigger_por_reset(self):
        status = self.cmd("query-status")
        if status and status.get("status") == "prelaunch":
            return
        self.cmd("stop")
        self.cmd(
            "qom-set",
            {"path": "ot-eg-pad-ring.0", "property": "por_n", "value": "low"},
        )
        self.cmd("system_reset")
        time.sleep(0.02)
        self.cmd(
            "qom-set",
            {"path": "ot-eg-pad-ring.0", "property": "por_n", "value": "high"},
        )

    def reset(self, halt=False, rma_spin_delay=0.05):
        """Resets the OpenTitan Earlgrey machine via QMP."""
        self._pc_tracing = False
        for attempt in range(2):
            try:
                if halt:
                    # Assert SW_STRAP_RMA_ENTRY so _rom_start_boot initializes gp, AST,
                    # disables watchdog, and parks in .L_rma_spin_cycles_loop, and keep
                    # it asserted so subsequent internal SW resets also park in the spin loop.
                    self.set_gpio_rma_strap(True)
                    self._trigger_por_reset()
                    self.cmd("cont")
                    time.sleep(rma_spin_delay)
                    self.cmd("stop")
                    if getattr(self, "_qemu", None) is not None and self._qemu.serial is not None:
                        try:
                            self._qemu.serial.reset_input_buffer()
                        except Exception:
                            pass
                        self._qemu._faulted = False
                        self._qemu._timed_out = False
                        if self._qemu.has_rma_spin:
                            self._qemu._halted_at_reset = True
                            self._qemu.serial.timeout = self._qemu.RMA_SPIN_TIMEOUT
                        else:
                            self._qemu.serial.timeout = self._qemu._default_timeout
                elif self.always_rma_strap:
                    self.set_gpio_rma_strap(True)
                    self._trigger_por_reset()
                    self.cmd("cont")
                    time.sleep(rma_spin_delay)
                else:
                    # Deassert SW_STRAP_RMA_ENTRY so ROM skips RMA spin and boots ROM_EXT -> BL0.
                    self.set_gpio_rma_strap(False)
                    self._trigger_por_reset()
                    self.cmd("cont")
                return
            except Exception:
                if attempt == 0 and getattr(self, "_qemu", None) is not None:
                    self._qemu._restart_qemu()
                else:
                    raise

    def is_running(self) -> bool:
        try:
            status = self.cmd("query-status")
            return bool(status and status.get("running", False))
        except Exception:
            return False

    def get_uart_pty(self, label="uart0"):
        chardevs = self.cmd("query-chardev")
        for dev in chardevs:
            if dev.get("label") == label:
                filename = dev.get("filename", "")
                if filename.startswith("pty:"):
                    return filename[len("pty:"):]
        raise RuntimeError(f"QEMU chardev '{label}' PTY not found in {chardevs}")

    def reset_uart_pty(self, label="uart0"):
        resp = self.cmd(
            "chardev-change",
            {"id": label, "backend": {"type": "pty", "data": {}}},
        )
        if resp and "pty" in resp:
            return resp["pty"]
        return self.get_uart_pty(label)


_shared_monitor = None


def get_qemu_monitor() -> QemuMonitor:
    global _shared_monitor
    if _shared_monitor is None:
        _shared_monitor = QemuMonitor()
    return _shared_monitor


def is_qemu_available() -> bool:
    monitor_path = os.environ.get("QEMU_MONITOR", "qemu-monitor")
    return os.path.exists(monitor_path)


class QemuSerialProxy:
    """Proxy around serial.Serial that survives QEMU restarts and PTY changes."""

    def __init__(self, qemu_target):
        self._qemu = qemu_target
        self._empty_reads = 0

    @property
    def in_waiting(self) -> int:
        if self._qemu.serial is None:
            return 0
        try:
            return self._qemu.serial.in_waiting
        except Exception:
            return 0

    @property
    def timeout(self):
        return self._qemu.serial.timeout if self._qemu.serial is not None else None

    @timeout.setter
    def timeout(self, value):
        if value is not None and value > 0:
            self._qemu._default_timeout = value
        if self._qemu.serial is not None:
            self._qemu.serial.timeout = value

    def __getattr__(self, name):
        return getattr(self._qemu.serial, name)

    def write(self, data):
        if self._qemu._faulted:
            return len(data)
        if not self._qemu._timed_out:
            self._empty_reads = 0
        try:
            return self._qemu.serial.write(data)
        except Exception:
            self._qemu._restart_qemu()
            return self._qemu.serial.write(data)

    def readline(self):
        if self._qemu._faulted:
            return b""
        try:
            if self._qemu.has_rma_spin:
                if self._qemu._halted_at_reset:
                    self._qemu._halted_at_reset = False
                    if not self._qemu.monitor.is_running():
                        return b""
                raw = self._qemu.serial.readline()
                if not raw:
                    self._qemu.serial.timeout = self._qemu.RMA_SPIN_TIMEOUT
                    return b""
                clean = raw.decode("utf-8", errors="replace").encode("utf-8")
                if any(m in clean for m in self._qemu.RMA_SPIN_TERMINAL_MARKERS):
                    self._qemu.serial.timeout = self._qemu.RMA_SPIN_SHORT_TIMEOUT
                else:
                    self._qemu.serial.timeout = self._qemu.RMA_SPIN_TIMEOUT
                return clean

            if self._qemu._timed_out:
                if self.in_waiting > 0:
                    self._qemu._timed_out = False
                    self._empty_reads = 0
                    self._qemu.serial.timeout = self._qemu._default_timeout
                else:
                    return b""

            raw = self._qemu.serial.readline()
            if not raw:
                if self._qemu.monitor._pc_tracing:
                    return b""
                self._empty_reads += 1
                if self._empty_reads >= 250:
                    if not self._qemu.monitor.is_running():
                        self._empty_reads = 0
                    else:
                        self._qemu._timed_out = True
                        self._qemu.serial.timeout = 0
                return b""
            self._empty_reads = 0
            clean = raw.decode("utf-8", errors="replace").encode("utf-8")
            if b"FAULT" in clean or b"Exception Frame" in clean:
                self._qemu._faulted = True
                self._qemu.serial.timeout = 0
            return clean
        except Exception:
            return b""

    def close(self):
        if self._qemu.serial:
            try:
                self._qemu.serial.close()
            except Exception:
                pass


class Qemu:
    """Class for the OpenTitan QEMU simulation target.

    Provides the same target interface as HyperDebug so GDB fault-injection tests
    can run unmodified against QEMU.
    """

    FLASH_HEADER_SIZE = 32
    DEFAULT_TIMEOUT = 0.004
    RMA_SPIN_TIMEOUT = 1.8
    RMA_SPIN_SHORT_TIMEOUT = 0.02
    RMA_SPIN_TERMINAL_MARKERS = (
        b"VER:",
        b"FAULT",
        b"Exception Frame",
        b"owner_page_1 erased and written",
        b"min_sec_ver_bl0 upgraded to 2",
        b"BL0 Slot B",
        b"firmware_cryptolib_fi_",
    )

    def __init__(self, fw_bin=None, gdb_port=3333):
        self.fw_bin = fw_bin
        self.gdb_port = gdb_port
        self.has_rma_spin = any(arg.startswith("--rom") for arg in sys.argv)
        self.monitor = get_qemu_monitor()
        self.monitor._qemu = self
        self.monitor.always_rma_strap = self.has_rma_spin
        self.serial = None
        self.baudrate = 115200
        self._initialized_count = 0
        self._restarted_qemu = False
        self._faulted = False
        self._timed_out = False
        self._halted_at_reset = False
        self._default_timeout = (
            self.RMA_SPIN_TIMEOUT if self.has_rma_spin else self.DEFAULT_TIMEOUT
        )

        self.otp_file = os.environ.get("QEMU_OTP", "otp_img.mut.raw")
        self.flash_file = os.environ.get("QEMU_FLASH", "flash_img.mut.bin")
        self.pid_file = os.environ.get("QEMU_PIDFILE", "qemu.pid")
        self.otp_orig_file = "otp_img.orig.raw"
        self.flash_orig_file = "flash_img.orig.bin"

        if os.path.exists(self.otp_file) and not os.path.exists(self.otp_orig_file):
            shutil.copyfile(self.otp_file, self.otp_orig_file)
        if os.path.exists(self.flash_file) and not os.path.exists(self.flash_orig_file):
            shutil.copyfile(self.flash_file, self.flash_orig_file)

        atexit.register(self._atexit_cleanup)

    def _is_qemu_alive(self) -> bool:
        if not os.path.exists(self.pid_file):
            return False
        try:
            with open(self.pid_file, "r") as f:
                pid = int(f.read().strip())
            os.kill(pid, 0)
            return True
        except Exception:
            return False

    def _open_serial(self, reset_pty=False):
        if self.serial:
            try:
                self.serial.close()
            except Exception:
                pass
        pty_path = (
            self.monitor.reset_uart_pty("uart0")
            if reset_pty
            else self.monitor.get_uart_pty("uart0")
        )
        self._faulted = False
        self._timed_out = False
        self._halted_at_reset = False
        self._default_timeout = (
            self.RMA_SPIN_TIMEOUT if self.has_rma_spin else self.DEFAULT_TIMEOUT
        )
        self.serial = serial.Serial(
            pty_path,
            baudrate=self.baudrate,
            timeout=self._default_timeout,
            write_timeout=1.0,
        )

    def init_communication(self, port, baudrate):
        self.baudrate = baudrate
        self._open_serial()
        return QemuSerialProxy(self)

    def _expected_flash_bytes(self):
        if not os.path.exists(self.flash_orig_file):
            return None
        with open(self.flash_orig_file, "rb") as f:
            data = bytearray(f.read())
        if self.fw_bin and os.path.exists(self.fw_bin):
            with open(self.fw_bin, "rb") as f:
                fw_data = f.read()
            end = self.FLASH_HEADER_SIZE + len(fw_data)
            data[self.FLASH_HEADER_SIZE:end] = fw_data
        return bytes(data)

    def _needs_image_restore(self) -> bool:
        if os.path.exists(self.otp_orig_file) and os.path.exists(self.otp_file):
            with open(self.otp_orig_file, "rb") as f1, open(self.otp_file, "rb") as f2:
                if f1.read() != f2.read():
                    return True
        expected_flash = self._expected_flash_bytes()
        if expected_flash is not None and os.path.exists(self.flash_file):
            with open(self.flash_file, "rb") as f:
                if f.read() != expected_flash:
                    return True
        return False

    def _restore_and_patch_images(self):
        if os.path.exists(self.otp_orig_file):
            shutil.copyfile(self.otp_orig_file, self.otp_file)
            os.chmod(self.otp_file, 0o644)
        expected_flash = self._expected_flash_bytes()
        if expected_flash is not None:
            with open(self.flash_file, "wb") as f:
                f.write(expected_flash)
            os.chmod(self.flash_file, 0o644)

    def _kill_qemu_pid(self):
        if not os.path.exists(self.pid_file):
            return
        try:
            with open(self.pid_file, "r") as f:
                pid = int(f.read().strip())
            os.kill(pid, signal.SIGTERM)
            for _ in range(20):
                time.sleep(0.05)
                try:
                    os.kill(pid, 0)
                except OSError:
                    break
            else:
                os.kill(pid, signal.SIGKILL)
        except Exception:
            pass

    def _restart_qemu(self):
        if self.serial:
            try:
                self.serial.close()
            except Exception:
                pass
            self.serial = None
        self.monitor.close()
        self.monitor.close_gpio()
        self._kill_qemu_pid()
        self._restore_and_patch_images()

        # Note: qemu_test.sh creates QEMU_LOG (qemu.log) as a named pipe (mkfifo)
        # with a single `cat qemu.log &` reader that exits when the initial QEMU
        # terminates. Remove QEMU_LOG so the restarted QEMU creates a regular file
        # instead of blocking forever opening a FIFO with no reader.
        for sock_env, default_name in [
            ("QEMU_MONITOR", "qemu-monitor"),
            ("QEMU_GPIO", "qemu-gpio.sock"),
            ("QEMU_RV_DM_JTAG", "qemu-jtag.sock"),
            ("QEMU_LC_JTAG", "qemu-jtag-lc-ctrl.sock"),
            ("QEMU_PIDFILE", "qemu.pid"),
            ("QEMU_LOG", "qemu.log"),
        ]:
            path = os.environ.get(sock_env, default_name)
            if os.path.exists(path):
                try:
                    os.remove(path)
                except OSError:
                    pass

        qemu_start = "hw/top_earlgrey/sw/util/qemu_start"
        run(
            [qemu_start, "-gdb", f"tcp::{self.gdb_port}", "-no-shutdown"],
            check=True,
            close_fds=True,
        )
        self._restarted_qemu = True
        self.monitor.connect()
        self._open_serial()

    def _atexit_cleanup(self):
        if self.serial:
            try:
                self.serial.close()
            except Exception:
                pass
            self.serial = None
        self.monitor.close()
        self.monitor.close_gpio()
        if self._restarted_qemu:
            self._kill_qemu_pid()
        for f in (self.otp_orig_file, self.flash_orig_file):
            if os.path.exists(f):
                try:
                    os.remove(f)
                except OSError:
                    pass

    def _wait_for_boot(self):
        """Waits for target to finish booting ROM -> ROM_EXT -> BL0/TestOS."""
        if not self.serial:
            return
        try:
            start_t = time.time()
            self.serial.timeout = 0.2
            while time.time() - start_t < 6.0:
                line = self.serial.readline()
                if b"Running " in line:
                    break
        finally:
            self.serial.timeout = self.RMA_SPIN_TIMEOUT if self.has_rma_spin else 0.004

    def initialize_target(self, print_output=True):
        if not self._is_qemu_alive() or self._needs_image_restore():
            self._restart_qemu()
        self._initialized_count += 1
        self.reset_target()
        if print_output:
            print(f"Info: QEMU target initialized with {self.fw_bin}.", flush=True)

    def clear_bitstream(self, delay=0, print_output=True):
        pass

    def reset_target(self, com_reset=False, reset_delay=0.005):
        if not self._is_qemu_alive():
            self._restart_qemu()
        try:
            self._open_serial(reset_pty=True)
        except Exception:
            self._restart_qemu()
        self.monitor.reset(halt=False)
        if not self.has_rma_spin:
            self._wait_for_boot()
        time.sleep(reset_delay)

    def start_openocd(self, startup_delay=0, print_output=False):
        # QEMU provides its own built-in GDB stub on tcp::3333; OpenOCD is not needed.
        if not self._is_qemu_alive():
            self._restart_qemu()

    def close_openocd(self, timeout=0):
        pass

    def read_openocd(self):
        return None

    def send_openocd_command(self, command, timeout=1.0, port=6666):
        return ""
