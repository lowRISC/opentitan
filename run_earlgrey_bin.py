#!/usr/bin/python3

import subprocess
import sys
import argparse
import logging
import threading

arg_parser = argparse.ArgumentParser(description='Run a binary on earlgrey FPGA, giving clipped UART output on stdout')
arg_parser.add_argument('--bin_file', type=str, help='Binary file to run', required = True)
arg_parser.add_argument('--fpga_uart', type=str, help='Path to FPGA UART Device (generally /dev/ttyUSBnn)', required = True)
arg_parser.add_argument('--baud_rate', type=int, help='Baud rate of UART', default=115200)
arg_parser.add_argument('--spiflash', type=str, help='Path to spiflash binary', default='./build-bin/sw/host/spiflash/spiflash')
arg_parser.add_argument('--log_prefix', type=str, help='Prefix for log files', default='run_earlgrey_log')
arg_parser.add_argument('--log', action='store_true', help='Enable loogging')
arg_parser.add_argument('--log_level', type=str, help='Log level INFO/WARNING/DEBUG', default='INFO')
arg_parser.add_argument('--timeout', type=int, help='Timeout for spiflash and uart in seconds', default=120)

UART_CLIP_PATTERN = '#*#*#*\n'

class UARTThread(threading.Thread):
    def __init__(self, args):
        super().__init__()

        if args.log:
            self.uart_log_name = args.log_prefix + '_uart.log'
            logging.info(f"Opening uart log at {self.uart_log_name}")
            self.uart_log = open(self.uart_log_name, 'w')
        else:
            self.uart_log = None

        logging.info(f"Opening uart {args.fpga_uart}")
        self.uart = open(args.fpga_uart, 'r', errors='ignore')

        self.found_clip_start      = False
        self.clip_pattern_pos      = 0
        self.in_clip_output_region = False
        self.terminate             = False

    def requestTerminate(self):
        self.terminate = True

    def run(self):
        while True:
            if(self.terminate):
                break

            next_char = self.uart.read(1)

            if self.uart_log:
                self.uart_log.write(next_char)
                self.uart_log.flush()

            if next_char == UART_CLIP_PATTERN[self.clip_pattern_pos]:
                self.found_clip_start = True
                self.clip_pattern_pos += 1
                if self.clip_pattern_pos == len(UART_CLIP_PATTERN):
                    if self.in_clip_output_region:
                        logging.info("Found clip pattern, exiting output region")
                        break
                    else:
                        logging.info("Found clip pattern, entering output region")
                        self.found_clip_start = False
                        self.clip_pattern_pos = 0
                        self.in_clip_output_region = True
            else:
                if self.in_clip_output_region:
                    if self.found_clip_start:
                        sys.stdout.write(UART_CLIP_PATTERN[:clip_pattern_pos])

                    sys.stdout.write(next_char)
                    sys.stdout.flush()

                self.found_clip_start = False
                self.clip_pattern_pos = 0

        logging.info("Closing UART stream and log")

        if self.uart_log:
            self.uart_log.close()

        self.uart.close()


def run_cmd(cmd, timeout=5):
    success = False

    logging.debug("Running cmd: " + ' '.join(cmd))

    try:
        cmd_res = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout
        )

        if cmd_res.returncode != 0:
            logging.critical(f"{cmd[0]} Failed with {cmd_res.returncode}")
            logging.critical(f"stdout: {cmd_res.stdout.decode('utf-8')}")
            logging.critical(f"stderr: {cmd_res.stderr.decode('utf-8')}")
        else:
            success = True
            logging.debug(f"stdout: {cmd_res.stdout.decode('utf-8')}")
            logging.debug(f"stderr: {cmd_res.stderr.decode('utf-8')}")

    except subprocess.TimeoutExpired:
        logging.critical(f"{cmd[0]} timed out")
    except FileNotFoundError:
        logging.critical(f"{cmd[0]} binary not found")

    return success

def setup_uart(args):
    logging.info(f"Setting UART {args.fpga_uart} to baud {args.baud_rate}")

    stty_cmd = ['stty',
            '-F',
            args.fpga_uart,
            str(args.baud_rate),
            'raw']

    return run_cmd(stty_cmd)

def run_bin(args):
    logging.info(f"Loading image {args.bin_file} using spiflash {args.spiflash}")

    spiflash_cmd = [
        args.spiflash,
        '--input',
        args.bin_file
    ]

    return run_cmd(spiflash_cmd, args.timeout)

def main():
    args = arg_parser.parse_args()

    if not args.log:
        logging.basicConfig(level='CRITICAL')
    else:
        logging.basicConfig(filename=args.log_prefix + '.log', level=args.log_level)
        stderr_handler = logging.StreamHandler()
        stderr_handler.setLevel('CRITICAL')
        logging.getLogger().addHandler(stderr_handler)

    if not setup_uart(args):
        logging.critical("UART setup failed, quitting")
        return

    try:
        uart_thread = UARTThread(args)
    except FileNotFoundError as e:
        logging.critical("Failed to open UART")
        logging.critical(e)
        return

    uart_thread.start()

    if not run_bin(args):
        logging.critical("Could not run binary, quitting")
        uart_thread.requestTerminate()
        return

    uart_thread.join(timeout=args.timeout)

    if uart_thread.is_alive():
        logging.warning('UART timed out')

if __name__ == "__main__":
  main()

