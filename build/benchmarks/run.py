#!/usr/bin/env python3
"""Run calyx's fixed build benchmarks and write their wall time and peak RSS as JSON."""

import argparse
import datetime
import hashlib
import json
import os
import pathlib
import platform
import statistics
import subprocess
import sys
import tempfile
import time


HERE = pathlib.Path(__file__).resolve().parent
WORKLOADS = [
    "integer-product.m",
    "matrix-product.m",
    "matrix-rank.m",
    "packed-polynomial-product.m",
    "groebner-f4.m",
]


def parse_args():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--binary", default="target/release/calyx", help="calyx binary to measure")
    p.add_argument("--output", default="calyx-benchmark.json", help="JSON output path, or - for stdout")
    p.add_argument("--cpu-model", help="CPU model when the host hides CPUID details")
    p.add_argument("--repeat", type=int, default=3, help="fresh processes per workload (1-10)")
    p.add_argument("--timeout", type=int, default=300, help="seconds allowed per process (1-600)")
    args = p.parse_args()
    if not 1 <= args.repeat <= 10:
        p.error("--repeat must be between 1 and 10")
    if not 1 <= args.timeout <= 600:
        p.error("--timeout must be between 1 and 600")
    return args


def peak_bytes(ru):
    return ru.ru_maxrss if platform.system() == "Darwin" else ru.ru_maxrss * 1024


def cpu_model():
    if platform.system() == "Linux":
        for line in pathlib.Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                return line.split(":", 1)[1].strip()
    if platform.system() == "Darwin":
        return subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"], check=True, capture_output=True, text=True).stdout.strip()
    return platform.processor()


def measure(binary, script, timeout):
    started = time.perf_counter()
    with script.open("rb") as src, tempfile.TemporaryFile() as output_file, tempfile.NamedTemporaryFile() as time_file:
        command = [binary, "-b", "-S", "1"]
        if platform.system() == "Linux" and pathlib.Path("/usr/bin/time").exists():
            command = ["/usr/bin/time", "-v", "-o", time_file.name, *command]
        p = subprocess.Popen(command, stdin=src, stdout=output_file, stderr=subprocess.STDOUT, cwd=HERE)
        deadline = started + timeout
        while True:
            pid, status, ru = os.wait4(p.pid, os.WNOHANG)
            if pid:
                break
            if time.perf_counter() >= deadline:
                p.kill()
                os.wait4(p.pid, 0)
                raise RuntimeError(f"{script.name} exceeded the {timeout} s limit")
            time.sleep(0.01)
        p.returncode = os.waitstatus_to_exitcode(status)
        output_file.seek(0)
        output = output_file.read()
        time_file.seek(0)
        time_output = time_file.read().decode(errors="replace")
    wall = time.perf_counter() - started
    if p.returncode:
        raise RuntimeError(f"{script.name} exited {p.returncode}:\n{output.decode(errors='replace')}")
    rss = peak_bytes(ru)
    for line in time_output.splitlines():
        if "Maximum resident set size (kbytes):" in line:
            rss = int(line.rsplit(":", 1)[1]) * 1024
    return {"wall_seconds": wall, "peak_rss_bytes": rss, "output": output.decode(errors="replace")}


def main():
    args = parse_args()
    binary = str(pathlib.Path(args.binary).resolve())
    env = dict(os.environ)
    env["OPENBLAS_NUM_THREADS"] = "1"
    version = subprocess.run([binary, "--version", "--verbose"], env=env, check=True, capture_output=True, text=True).stdout.rstrip()
    report = {
        "schema": 1,
        "recorded_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform": platform.platform(),
        "cpu_model": args.cpu_model or cpu_model(),
        "binary": binary,
        "environment": {"OPENBLAS_NUM_THREADS": "1"},
        "version": version,
        "benchmarks": [],
    }
    os.environ.update(env)
    for name in WORKLOADS:
        script = HERE / name
        runs = [measure(binary, script, args.timeout) for _ in range(args.repeat)]
        outputs = {run.pop("output") for run in runs}
        if len(outputs) != 1:
            raise RuntimeError(f"{name} printed inconsistent results")
        result = outputs.pop().strip()
        if not result.startswith(script.stem + " "):
            raise RuntimeError(f"{name} did not print its result marker:\n{result}")
        walls = [run["wall_seconds"] for run in runs]
        rss = [run["peak_rss_bytes"] for run in runs]
        report["benchmarks"].append({
            "name": script.stem,
            "script_sha256": hashlib.sha256(script.read_bytes()).hexdigest(),
            "repeat": args.repeat,
            "result": result,
            "runs": runs,
            "best_wall_seconds": min(walls),
            "median_wall_seconds": statistics.median(walls),
            "peak_rss_bytes": max(rss),
        })
    text = json.dumps(report, indent=2) + "\n"
    if args.output == "-":
        sys.stdout.write(text)
    else:
        pathlib.Path(args.output).write_text(text)


if __name__ == "__main__":
    main()
