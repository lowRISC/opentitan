# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# Original author: Louis-Emile Ploix
# SPDX-License-Identifier: Apache-2.0

# This program handles the running of proof processes. It can discover efficient proofs, schedule them, find
# counterexamples, and analyse the results.

import asyncio
import argparse
import re
import subprocess
import time
import json
import os
from math import floor
from datetime import datetime
import hashlib
from typing import Iterable
import typing
import psutil
from pathlib import Path

# Skipped properties are excluded from every step
SKIPPED_PROPS = [
    'MType_Div_Data',
    'MType_Rem_Data',
    'MType_Mul_Data',
    'MType_RemU_Data',
    'MType_MulH_Data',
    'MType_DivU_Data',
    'MType_MulHU_Data',
    'MType_MulHSH_Data',
]

# --------------------- Utilities ----------------------

PROOFLOG = os.environ.get("PROOFLOG", "prooflog.txt")
LOGFILE = os.environ.get("LOGFILE", "logfile.txt")

# ANSI coloring, supported everywhere but windows, but since this script exists within a nix
# setup, which won't support windows anyway, there seems little point in handling it.
def green(s): return f"\033[32;1m{s}\033[0m"
def red(s): return f"\033[31;1m{s}\033[0m"
def white(s): return f"\033[1m{s}\033[0m"
def orange(s): return f"\033[33;1m{s}\033[0m"
def gray(s): return f"\033[90m{s}\033[0m"

def write_logfile(s):
    if not "NO_LOG" in os.environ:
        with open(LOGFILE, "a") as f:
            f.write(s + "\n")

'''Send all printed text to a log file, and prepend the date and time.'''
def log(*args, c=lambda x: x):
    timestr = datetime.now().strftime('[%d/%m/%y %H:%M:%S.%f]')
    s = " ".join(map(str, args))
    print(gray(timestr), c(s))
    write_logfile(f"{timestr} {s}")

write_logfile("") # Blank line to mark new run

'''
Races allow async processes to cleanly run in parrallel, until one declares victory,
at which point all the other futures are cancelled. Tasks should be sequence of
awaitables. In order to declare victory of a race, simply return something not-None.
'''
async def race[A](tasks: Iterable[typing.Awaitable[A | None]]) -> A | None:
    class RaceWonException(Exception):
        def __init__(self, result):
            super().__init__()
            self.result = result
    winner = None
    try:
        async with asyncio.TaskGroup() as tg:
            for task in tasks:
                async def wrapper():
                    res = await task
                    if res is not None:
                        raise RaceWonException(res)
                tg.create_task(wrapper())
    except* RaceWonException as e:
        for result in e.exceptions:
            assert isinstance(result, RaceWonException)
            winner = result.result
    return winner

# --------------------- Process Management ----------------------

GB = 1024**3

'''
Returns the global free memory according to psutil, which is just MemAvailable in /proc/meminfo.
'''
def global_memory_free():
    return psutil.virtual_memory().available / GB

'''
Finishes when a process exits, and cancelling kills that process.
Produces a ProcessResult.
'''
class ProcessFuture(asyncio.Future):
    def __init__(self, loop, proc):
        super().__init__(loop=loop)
        self.proc = proc

    def cancel(self, msg = None):
        self.proc.kill()
        return super().cancel(msg=msg)

'''
Information regarding the completion of a process, including memory/time and stdio. 
'''
class ProcessResult:
    def __init__(self, code, reason, max_mem, dt, stdout, stderr):
        self.code: int | None = code
        '''
        OK = the process finished
        TIMEOUT = the process was killed by us due to a timeout
        UNINTERESTED = the process was killed by us, probably because another process in the race won
        '''
        self.reason: str = reason
        self.max_mem: float = max_mem
        self.dt: float = dt
        self.stdout: str | None = stdout
        self.stderr: str | None = stderr

    @staticmethod
    def from_proc(proc, code, reason, max_mem, dt):
        return ProcessResult(code, reason, max_mem, dt, proc.stdout.read().decode(), proc.stderr.read().decode())

'''
A process, which me killed, restarted and awaited (via the .future property).
Handles the tracking of time and timeouts, and of memory consumption.
debug_slow allows for periodic logging.
'''
class Process:
    def __init__(self, cmd, expected_memory = 0.0, expected_time = 0.0, timeout = None, debug_slow = None):
        self.cmd: str = cmd
        self.expected_memory: float = expected_memory
        self.expected_time: float = expected_time
        self.timeout: float | None = timeout
        self.kill_: str | None = None # Either kill, restart or None

        self.debug_slow = debug_slow # A message to write when the process is taking a long time
        self.debug_slow_count = 0

        self.proc = None # Will be set on start()
        self.psproc = None

        self.future: asyncio.Future[ProcessResult] = ProcessFuture(asyncio.get_running_loop(), self)

        self.max_memory = 0
        self.start_time = 0

    def start(self):
        log("$", self.cmd)
        self.proc = subprocess.Popen(self.cmd, shell=True, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.psproc = psutil.Process(pid=self.proc.pid)
        self.start_time = time.time()
        self.max_memory = 0
        self.debug_slow_count = 0

    # Give up on the process, may be called by anyone
    def kill(self):
        self.kill_ = "kill"

    # Kill the process with the expectation that it will be restarted again.
    # Only to be called by ProcessRunner
    def kill_restart(self):
        self.kill_ = "restart"

    def poll(self):
        assert self.proc is not None
        assert self.psproc is not None

        self.max_memory = max(self.psproc.memory_info().rss / GB, self.max_memory)

        dt = time.time() - self.start_time
        code = self.proc.poll()
        if code is not None and self.kill_ == None:
            log(f"Finished `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)")
            if not self.future.cancelled():
                self.future.set_result(ProcessResult.from_proc(self.proc, code, "OK", self.max_memory, dt))
                # self.future.set_result((code, self.max_memory, dt, "OK", self.proc.stdout.read().decode(), self.proc.stderr.read().decode()))
            return True
        elif self.kill_ == "restart":
            log(f"Kill (will restart) `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)", c=gray)
            self.proc.kill()
            self.kill_ = None
            self.expected_memory = max(self.expected_memory, self.max_memory)
            self.expected_time = max(self.expected_time, dt)
            return True
        elif self.timeout is not None and dt > self.timeout:
            log(f"Kill `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)")
            self.proc.kill()
            if not self.future.cancelled():
                self.future.set_result(ProcessResult.from_proc(self.proc, None, "TIMEOUT", self.max_memory, dt))
                # self.future.set_result((None, self.max_memory, dt, "TIMEOUT", None, self.proc.stderr.read().decode()))
            return True
        elif self.kill_ == "kill":
            log(f"Kill (uninterested) `{self.cmd}` ({dt:.3f}s) ({self.max_memory:.3f}GB)", c=gray)
            self.proc.kill()
            if not self.future.cancelled():
                self.future.set_result(ProcessResult.from_proc(self.proc, None, "UNINTERESTED", self.max_memory, dt))
                # self.future.set_result((None, self.max_memory, dt, "UNINTERESTED", None, self.proc.stderr.read().decode()))
            return True

        # Every 60 seconds call the debug_slow handler
        n = floor(dt / 60.0)
        if n > self.debug_slow_count:
            if self.debug_slow is not None:
                self.debug_slow(dt)
            self.debug_slow_count = n

        return False

'''
Schedules (and reschedules) Processes according to the memory and CPU
constraints of the system.
'''
class ProcessRunner:
    GLOBAL_MEMORY_BUFFER = 5 # Never allocate more than (total ram - buffer)GB memory
    POLL_DELAY = 0.1 # Time between poll cycles
    MAX_RUNNING = (psutil.cpu_count() or 8) - 2 # Number of CPUs, with a couple spares

    def __init__(self):
        self.pending = []
        self.running = []
        self.first_start = time.time()
        self.debug_count = 0

        log(f"Process runner will have a maximum of {ProcessRunner.MAX_RUNNING} processes, and currently sees {self.mem_avail():.3f}GB free.")

    def append(self, proc):
        self.pending.insert(0, proc)

    def start_loop(self):
        asyncio.get_running_loop().call_soon(lambda: self.poll())

    def children_used_mem(self):
        return sum(proc.max_memory for proc in self.running)

    def mem_avail(self):
        if args.max_mem == 0:
            return global_memory_free()
        return min(global_memory_free(), max(args.max_mem - self.children_used_mem(), 0))

    def poll(self):
        # Kill recently started processes until memory is OK, unless there is just one, then there's no point(?)
        free = self.mem_avail()
        while not args.no_kill and free < ProcessRunner.GLOBAL_MEMORY_BUFFER and len(self.running) > 1:
            last = self.running.pop()
            last.kill_restart()
            free += max(last.max_memory, 3)
            last.poll()
            self.pending.append(last)

        while len(self.running) < ProcessRunner.MAX_RUNNING and len(self.pending) > 0 and free > self.pending[-1].expected_memory + ProcessRunner.GLOBAL_MEMORY_BUFFER:
            if self.first_start == 0:
                self.first_start = time.time()
            last = self.pending.pop()
            last.start()
            free -= max(last.expected_memory, 3) # otherwise lots of zeros won't help
            self.running.append(last)

        # Drop processes that finished
        p = 0
        while p < len(self.running):
            if self.running[p].poll():
                self.running.pop(p)
            else:
                p += 1

        n = floor((time.time() - self.first_start) / 30.0)
        if n > self.debug_count:
            log(f"Running {len(self.running)} processes, with {len(self.pending)} pending. Memory used right now: {self.children_used_mem():.3f}GB", c=gray)
            self.debug_count = n

        asyncio.get_running_loop().call_later(ProcessRunner.POLL_DELAY, lambda: self.poll())

process_runner: ProcessRunner | None = None
'''Run a shell command in the global process runner'''
async def shell(cmd, expected_memory = 0.0, timeout = None, debug_slow = None):
    assert process_runner is not None
    proc = Process(cmd, expected_memory=expected_memory, timeout=timeout, debug_slow=debug_slow)
    process_runner.append(proc)
    return await proc.future

# ------------------------ Proof Primitives ------------------

'''
Prepares an aiger file configured for the properties at the given step specifically, return a run unique path to it
'''
aiger_idx = 0
async def prepare_aiger(step: int, props: list[str]) -> str:
    global aiger_idx

    name = f"build/aiger-{aiger_idx}.aig"
    aiger_idx += 1
    assert (await shell(
        f"build/aig-manip build/all.aig select {name} build/all.ywmap {step} {' '.join(props)}",
        expected_memory=0.5
    )).code == 0

    return name

'''Log a nice message on proof completion, and store in the proof log'''
def proof_done(engine_config: str, path: str, step: int, props: list[str], procres: ProcessResult):
    if not "NO_LOG" in os.environ:
        with open(PROOFLOG, "a") as f:
            json.dump([time.time(), [props, step, ROOT_HASH, engine_config], vars(procres)], f)
            f.write("\n")
    match procres.code:
        case 20:
            log(f"UNSAT: {len(props)} properties in step {step} proven in {procres.dt:.3f}s with {procres.max_mem:.3f}GB", c=green)
        case 10:
            log(f"==========================================================================================================================", c=red)
            log(f"==========================================================================================================================", c=red)
            log(f"==========================================================================================================================", c=red)
            log(f"       ==================== SAT: CEX in step {step}, discovered in {procres.dt:.3f}s with {procres.max_mem:.3f}GB ==================", c=red)
            log(f"==========================================================================================================================", c=red)
            log(f"==========================================================================================================================", c=red)
            log(f"==========================================================================================================================", c=red)
            log(f"One of these properties in step {step} is not valid: {' '.join(props)}", c=red)
            log(f"To recover a witness run the following:")
            log(f"    {engine_config} {path} --witness | tail -n +2 > witness.aiw")
            log(f"Or the following:")
            log(f"    rIC3 -e bmc --no-preproc {path} --witness | tail -n +2 > witness.aiw")
            log(f"Or, to compare against another engine:")
            log(f"    python3 smt2manip.py build/all.smt2 sel.smt2 {step} {' '.join(props)}")
            log(f"    yosys-smtbmc -s yices sel.smt2")
            log(f"Then to view the trace:")
            log(f"    build/aig-manip build/all.aig simulate build/all.ywmap build/all.vmap witness.aiw trace.vcd")
            log(f"    gtkwave trace.vcd")
        case 30:
            log(f"UNDETERMINED: Failed to find a CEX or proof for {len(props)} properties in step {step} ({procres.dt:.3f}s with {procres.max_mem:.3f}GB)", c=orange)
        case -9:
            log(f"KILLED by OS: Failed to prove {len(props)} properties in step {step} ({procres.dt:.3f}s with {procres.max_mem:.3f}GB)", c=red)
        case None:
            log(f"TIMEOUT: Failed to prove {len(props)} properties in step {step} ({procres.dt:.3f}s with {procres.max_mem:.3f}GB)", c=red)
        case n:
            log(f"Unknown Exit Code {n}: Failed to prove {len(props)} properties in step {step} ({procres.dt:.3f}s with {procres.max_mem:.3f}GB)", c=red)

'''Prove some properties with the given config'''
async def prove(engine_config: str, step: int, props: list[str], timeout=None, expected_memory=10.0) -> ProcessResult:
    specialised = await prepare_aiger(step, props)
    res = await shell(f"{engine_config} {specialised}", timeout=timeout, expected_memory=expected_memory)
    proof_done(engine_config, specialised, step, props, res)
    return res

cex_id = 0
'''Run Bounded Model Checking on some properties'''
async def bmc(step: int, props: list[str], timeout=None, start=None, end=None) -> ProcessResult:
    global cex_id
    res = await prove("rIC3 -e bmc --no-preproc --witness" + ("" if start is None else f" --start {start}") + ("" if end is None else f" --end {end}"), step, props, timeout=timeout)
    if res.code == 10:
        assert res.stdout is not None
        own_id = cex_id
        cex_id += 1
        witness = res.stdout.split("\n", maxsplit=1)[1]
        Path(f"witness-{own_id}.aiw").write_text(witness)
        log(f"Written trace to witness-{own_id}.aiw", c=white)
        await shell(f"./aig-manip/target/release/aig-manip build/all.aig simulate build/all.ywmap build/all.vmap witness-{own_id}.aiw trace-{own_id}.vcd")
        log(f"Produced VCD file at trace-{own_id}.vcd", c=white)
    return res

# -------------------------- Proof Exploration -----------------------

'''Try several configurations for some properties and see which is best, if any'''
async def explore(step: int, props: list[str], configs: list[tuple[str, float]], timeout=0.0, debug_slow=None) -> None | tuple[str, ProcessResult]:
    specialised = await prepare_aiger(step, props)

    async def explore_one(engine_config, expected_memory):
        result = await shell(f"{engine_config} {specialised}", timeout=timeout, expected_memory=expected_memory, debug_slow=debug_slow)
        proof_done(engine_config, specialised, step, props, result)
        if result.code in {10, 20}:
            return engine_config, result

    return await race([explore_one(config, mem) for config, mem in configs])

'''
Represents a complete proof step for some properties
'''
class Strategy:
    def __init__(self, step, props, config, procres):
        self.step: int = step
        self.props: list[str] = props
        self.config: str = config
        self.procres: ProcessResult = procres

'''Build a strategy for the given tree, where in each case we either split into subtrees, or prove as a block. A strategy is a flat list of proof instructions.'''
async def build_strategy_rec(step: int, prop_tree: list, failures: list[tuple[int, str]], eager=False, difficult=False) -> list[Strategy]:
    def find_all(prop_tree, all_props):
        for prop in prop_tree:
            if type(prop) == str:
                all_props.append(prop)
            else:
                find_all(prop, all_props)
    all_props = []
    find_all(prop_tree, all_props)

    # These may be helpful to change depending on the nature of the task
    if difficult:
        ENGINES = [
            # ("rIC3", 10),
            # ("rIC3 --no-preproc", 20),
            ("rIC3 -e kind --no-preproc", 10.0),
            # ("rIC3 -e kind", 10)
        ]
    else:
        ENGINES = [
            ("rIC3", 10),
            # ("rIC3 --no-preproc", 20),
            ("rIC3 -e kind --no-preproc", 10.0),
            # ("rIC3 -e kind", 10)
        ]

    if len(all_props) == 0:
        return []

    if len(all_props) == 1:
        while True:
            res = await explore(
                step, all_props,
                timeout=1800.0 if difficult else 600.0,
                configs=ENGINES,
                debug_slow=lambda dt: log(f"Still exploring step {step} property {all_props[0]} ({dt:.3f}s)", c=gray)
            )
            if res is not None:
                if res[1].code == 20:
                    log(f"Constructed proof for 1 property in step {step}: {all_props[0]}", c=green)
                    return [Strategy(step, all_props, res[0], res[1])]
                else:
                    log(f"Failed to construct proof for 1 property in step {step}: {all_props[0]}", c=red)
                    return []
            log(f"Failed to find proof for property in step {step}: {all_props[0]} - ignoring", c=red)
            failures.append((step, all_props[0]))
            return []

    if len(prop_tree) == 1:
        return await build_strategy_rec(step, prop_tree[0], failures, difficult=difficult)

    async def without_split():
        res = await explore(step, all_props, timeout=120.0, configs=ENGINES)
        if res is not None:
            if res[1].code == 20:
                log(f"Constructed proof for {len(all_props)} properties in step {step}: {' '.join(all_props)}", c=green)
                return [Strategy(step, all_props, res[0], res[1])]
            else:
                log(f"Failed to construct proof for {len(all_props)} properties in step {step}: {' '.join(all_props)}", c=red)

    async def with_split():
        children = []
        rest = []
        for prop in prop_tree:
            if type(prop) == str:
                rest.append(prop)
            else:
                children.append(prop)

        if not eager:
            await asyncio.sleep(120.0) # Give the rest a head start
        else:
            await asyncio.sleep(20.0) # Give the rest a tiny head start anyway

        if len(children) == 0:
            solutions = await asyncio.gather(*[build_strategy_rec(step, [child], failures, difficult=difficult) for child in rest])
        else:
            children.append(rest)
            solutions = await asyncio.gather(*[build_strategy_rec(step, tree, failures, difficult=difficult) for tree in children])
        flattened = []
        for solution in solutions:
            flattened.extend(solution)
        return flattened

    winner = await race([without_split(), with_split()])
    assert winner is not None # someone has to win!
    return winner

'''Execute a given strategy, return all the (result, strategy)'''
async def run_strategy(strategy: list[Strategy]) -> list[tuple[ProcessResult, Strategy]]:
    proofs = []
    strategy.sort(key=lambda x: x.procres.dt, reverse=True)
    for step in strategy:
        conf = step.config
        if step.procres.stderr is not None:
            if " -e kind " in step.config:
                s = step.procres.stderr.split("[INFO ] k-induction proofed in depth ")
                if len(s) == 2:
                    conf += f" --start {int(s[1].strip())}"
        proofs.append(prove(conf, step.step, step.props, expected_memory=step.procres.max_mem * 1.1))
    return list(zip(await asyncio.gather(*proofs), strategy))

'''Construct a proof tree by recursively splitting on the prefix of a name, for example a_x, a_y, b will produce [[a_x, a_y], b]'''
def split_by_prefixes(names: list[str]) -> list:
    def chunk_name(name):
        nts = lambda x: "" if x is None else x
        split = re.split(r"_([A-Z])|_|([A-Z])", name)
        return ([split[0]] if split[0] != "" else []) + [nts(split[i + 1]) + nts(split[i + 2]) + split[i + 3] for i in range(0, len(split) - 1, 3)]

    def group(props):
        buckets = {}
        done = []
        for chunks, name in props:
            if len(chunks) == 1:
                done.append(name)
            elif chunks[0] not in buckets:
                buckets[chunks[0]] = [(chunks[1:], name)]
            else:
                buckets[chunks[0]].append((chunks[1:], name))
        for pre in buckets:
            bucket = group(buckets[pre])
            # while len(bucket) == 1:
            #     bucket = bucket[0]
            done.append(bucket)
        return done

    chunked_names = [(chunk_name(name), name) for name in names]
    return group(chunked_names)

# ---------------------------------- Main ------------------------------

parser = argparse.ArgumentParser(prog="conductor.py", description="Constructs and executes proofs.", epilog="Additionally, the PROOFLOG env var sets the prooflog file (i.e. one proof result per line, JSON), and the LOGFILE env var sets the logging file.")
parser.add_argument("mode", choices=["prove", "explore", "bmc", "info"],
                    help="Proof mode. "
                    "prove will run existing proofs where they exist, "
                    "explore will attempt to discover new proofs, "
                    "bmc will do bounded model checking on each property individually, "
                    "info dumps stats about cached proofs.")
parser.add_argument("--fresh", action="store_true", help="In explore mode, do not use already constructed proofs, always construct new proofs.")
parser.add_argument("--no-store", action="store_true", help="In explore mode, do not store constructed proof strategies.")
parser.add_argument("--by-step", action="store_true", help="In prove mode, do proofs one step at a time")
parser.add_argument("-p", "--properties", nargs="*", default=[], help="Restrict to only the properties with the given names, otherwise all properties. Especially helpful for BMC.")
parser.add_argument("--missing", action="store_true", help="Equivalent to -p <each property that is not skipped but has no proof in a step where there are some proofs>")
parser.add_argument("-s", "--start", type=int, default=0, help="First step to start at. (default: 0)")
parser.add_argument("--bmc-step", type=int, default=1, help="Step size for BMC. (default: 1)")
parser.add_argument("--bmc-start", type=int, default=4, help="Start length for BMC. (default: 4)")
parser.add_argument("--hard", action="store_true", help="In explore mode, try harder to prove properties (1hr timeout, more engines).")
parser.add_argument("--no-run", action="store_true", help="In explore mode don't run proofs again to check steps.")
parser.add_argument("--no-kill", action="store_true", help="Don't kill proof processes due to running out of memory.")
parser.add_argument("--check-complete", action="store_true", help="In prove mode, fail if there are unskipped properties without proofs.")
parser.add_argument("--max-mem", type=float, default=0, help="Max memory in GB, otherwise use all available memory")
args = parser.parse_args()

if len(SKIPPED_PROPS) > 0:
    log(f"WARNING: Skipped properties are {' '.join(SKIPPED_PROPS)}", c=orange)

ROOT_HASH = hashlib.new("sha256", Path("build/all.aig").read_bytes()).hexdigest()
log(f"build/all.aig has sha256 {ROOT_HASH}")

def decode_strategy(encoded: list) -> Strategy:
    return Strategy(encoded[0], encoded[1], encoded[2], ProcessResult(encoded[3][0], encoded[3][3], encoded[3][1], encoded[3][2], encoded[3][4] if len(encoded[3]) > 4 else None, encoded[3][5] if len(encoded[3]) > 5 else None))

def load_strategy(step: int) -> list[Strategy] | None:
    if args.fresh:
        return None
    try:
        with open(f"strategies/step{step}.json", "r") as f:
            log(f"Loading strategy for step {step} from cache", c=white)
            encoded = json.load(f)
        return [decode_strategy(d) for d in encoded]
    except FileNotFoundError:
        pass
    except json.JSONDecodeError as e:
        log(f"Error decoding step{step}.json (ignoring): {e}", c=red)
    return None

def store_strategy(step: int, strategy: list[Strategy]):
    encoded = [[s.step, s.props, s.config, [s.procres.code, s.procres.max_mem, s.procres.dt, s.procres.reason, s.procres.stdout, s.procres.stderr]] for s in strategy]
    log(encoded, c=gray)
    if args.no_store:
        return [decode_strategy(d) for d in encoded]
    try:
        os.makedirs("strategies", exist_ok=True)
        with open(f"strategies/step{step}.json", "w") as f:
            json.dump(encoded, f)
    except Exception as e:
        log(f"ERROR: Could not save strategy: {e}", c=red)
    return [decode_strategy(d) for d in encoded]

def missing_from(strategy: list[Strategy], props: list[str]) -> list[str]:
    done_props: list[str] = []
    for strategy_step in strategy:
        done_props.extend(strategy_step.props)
    return list(set(props).difference(done_props))

async def bmc_mode(props: list[tuple[int, str]]):
    if len(props) == 1:
        step, prop = props[0]
        log(f"Doing unbounded BMC for step on {prop} from step {step}", c=white)
        await bmc(step, [prop], start=args.bmc_start)
        return

    if len(props) == 0:
        log("No properties to do BMC on!", c=red)
        return
    i = args.bmc_start
    while True:
        for step, prop in props:
            log(f"Doing BMC at depth {i} on {prop} from step {step}", c=white)
            await bmc(step, [prop], start=i, end=i)
        i += args.bmc_step

async def info_mode(by_step: list[list[str]], by_step_skipped: list[list[str]]):
    total_steps = 0
    for step, _ in enumerate(by_step):
        strategy = load_strategy(step)
        if strategy is None:
            log(f"No proof strategy entry for step {step}", c=orange)
            strategy = []
        total_steps += len(strategy)
        accounted_for: list[str] = []
        for stepi in strategy:
            log(f"Step {stepi.step} :: {stepi.procres.reason} :: {stepi.procres.max_mem:.3f}GB/{stepi.procres.dt:.3f}s :: {stepi.config} :: {' '.join(stepi.props)}")
            accounted_for.extend(stepi.props)
        if len(by_step_skipped[step]) > 0:
            log(f"Step {step} :: SKIPPED :: :: :: {' '.join(by_step_skipped[step])}", c=orange)
        unaccounted: list[str] = []
        for prop in by_step[step]:
            if prop not in accounted_for:
                unaccounted.append(prop)
        if len(unaccounted) > 0:
            log(f"Step {step} :: UNACCOUNTED :: :: :: {' '.join(unaccounted)}", c=red)
    log(f"{total_steps} proof steps in total")

async def prove_mode(all_props: list[tuple[int, str]], by_step: list[list[str]]):
    all_strategies: list[Strategy] = []
    for step, props in enumerate(by_step):
        if step < args.start:
            log(f"Skipping step {step}", c=orange)
            continue
        strategy = load_strategy(step)
        if strategy is None or len(strategy) == 0:
            log(f"No strategy for step {step}, skipping", c=orange)
            continue

        if args.by_step:
            log(f"Running strategy for step {step} ({len(props)} properties)", c=white)
            run_start = time.time()
            await run_strategy(strategy)
            run_dt = time.time() - run_start
            log(f"Ran strategy for step {step} in {run_dt:.3f}s", c=white)
        all_strategies.extend(strategy)

    if args.check_complete:
        covered: set[str] = set()
        for step in all_strategies:
            covered.update(step.props)
        uncovered = set(prop[1] for prop in all_props).difference(covered)
        if len(uncovered) > 0:
            log(f"Missing proof steps for {len(uncovered)} properties: {' '.join(uncovered)}", c=red)
            exit(1)
        else:
            log(f"All {len(all_props)} properties are covered.", c=green)

    if not args.by_step:
        log(f"Running strategy for everything", c=white)
        run_start = time.time()
        results = await run_strategy(all_strategies)
        run_dt = time.time() - run_start
        log(f"Ran strategy in {run_dt:.3f}s", c=white)

        unsats = 0
        has_errors = False
        for res, step in results:
            if res.code == 20:
                unsats += 1
            else:
                has_errors = True
                log(f"Failed to prove step {step.step} proof step with code {res.code} (see above, or logfile.txt, for more details): {' '.join(step.props)}", c=red)
        log(f"{unsats}/{len(all_strategies)} proof steps were UNSAT", c=white)
        if has_errors:
            exit(1) # Failed

async def construct_strategy(step: int, props: list[str]) -> tuple[bool, list[Strategy], list[str]]:
    strategy = load_strategy(step) or []
    not_done = missing_from(strategy, props)
    if len(not_done) == 0:
        return False, strategy, []

    log(f"Building strategy for step {step} ({len(not_done)}/{len(props)} properties)", c=white)
    build_start = time.time()

    failures: list[tuple[int, str]] = []
    if args.hard:
        log("strategy: each property", c=white)
        for x in await asyncio.gather(*[build_strategy_rec(step, [prop], failures, difficult=True) for prop in not_done]):
            strategy.extend(x)
    else:
        log("strategy: name based recursive splitting, linear fallback", c=white)
        blocks = split_by_prefixes(not_done)
        strategy += await build_strategy_rec(step, blocks, failures, difficult=args.hard)

    build_dt = time.time() - build_start
    log(f"Constructed strategy for step {step} of {len(strategy)} proof steps in {build_dt:.3f}s", c=white)
    strategy = store_strategy(step, strategy)
    return True, strategy, [f[1] for f in failures]

async def explore_mode(by_step: list[list[str]]):
    all_failures: list[str] = []
    for step, props in enumerate(by_step):
        if step < args.start:
            log(f"Skipping step {step}", c=orange)
            continue

        new, strategy, failures = await construct_strategy(step, props)
        all_failures.extend(failures)
        if new:
            log(f"All failures to date: {all_failures}", c=gray)

        if args.no_run:
            pass
        elif not new or len(strategy) != 1:
            log(f"Running strategy for step {step} ({len(props)} properties)", c=white)
            run_start = time.time()
            await run_strategy(strategy)
            run_dt = time.time() - run_start
            log(f"Ran strategy for step {step} in {run_dt:.3f}s", c=white)
        else:
            log(f"Skipping proof run for step {step}, since it has just one step", c=white)

async def main():
    global process_runner

    def preproc_name(name: str) -> tuple[int, str]:
        first = name.split("$")[1][5:]
        assert first.startswith("Step")
        step, rest = first.split("_", maxsplit=1)
        step = int(step[4:])
        return step, rest

    def group_by_step(names: list[tuple[int, str]], max=None) -> list[list[str]]:
        by_step = []
        for step, name in names:
            while step >= len(by_step):
                by_step.append([])
            by_step[step].append(name)
        if max is not None:
            while max >= len(by_step):
                by_step.append([])
        return by_step

    process_runner = ProcessRunner()
    process_runner.start_loop()

    log("Reading property list", c=white)
    with open("build/all.ywmap") as f:
        names = [preproc_name(x[0]) for x in json.load(f)["asserts"]]
    max_step = max(step for step, _ in names)
    names = [(step, name) for step, name in names if not name.endswith("_Cover")]

    by_step = group_by_step(names)
    props: list[tuple[int, str]] = []
    for prop in args.properties:
        for step, name in names:
            if prop == name:
                props.append((step, prop))
                break
        else:
            log(f"ERROR: Property not found {prop}", c=red)
            exit(1)
    if args.missing:
        for step, sprops in enumerate(by_step):
            strategy = load_strategy(step)
            if strategy is None:
                continue
            props.extend([(step, p) for p in missing_from(strategy, sprops)])
    elif len(props) == 0:
        props = names
    props_skipped = [(step, p) for step, p in props if p in SKIPPED_PROPS]
    props = [(step, p) for step, p in props if p not in SKIPPED_PROPS]

    if len(props) == 0 and len(props_skipped) == 0:
        log("Warning: Empty property selection", c=orange)

    skipped_by_step = group_by_step(props_skipped, max_step)
    by_step = group_by_step(props, max_step)

    match args.mode:
        case "bmc":
            await bmc_mode(props)
        case "info":
            await info_mode(by_step, skipped_by_step)
        case "prove":
            await prove_mode(props, by_step)
        case "explore":
            await explore_mode(by_step)

asyncio.run(main())
