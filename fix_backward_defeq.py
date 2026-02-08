#!/usr/bin/env python3
"""
Script to automatically add `set_option backward.isDefEq.respectTransparency false in`
before declarations with errors, testing if it fixes the error.
"""

import subprocess
import re
import os
import sys
from pathlib import Path
from threading import Lock, Thread
from queue import Queue, Empty
import time

SET_OPTION_LINE = "set_option backward.isDefEq.respectTransparency false in"
PROJECT_DIR = Path(__file__).parent

# ANSI escape codes
CLEAR_LINE = "\033[2K"
HIDE_CURSOR = "\033[?25l"
SHOW_CURSOR = "\033[?25h"


class StatusDisplay:
    """Manages a multi-line status display that updates in place."""

    def __init__(self, num_workers: int):
        self.num_workers = num_workers
        self.lock = Lock()
        self.worker_status: dict[int, str] = {i: "idle" for i in range(num_workers)}
        self.summary_line = ""
        self.build_status = ""  # e.g. "3000/7000 built successfully"
        self.discovery_status = ""
        self.last_failed = ""  # Last file we gave up on
        self.messages: list[str] = []  # Messages to print above status
        self.displayed_lines = 0
        self.started = False

    def start(self):
        """Initialize the display."""
        self.started = True
        print(HIDE_CURSOR, end="", flush=True)
        self._redraw()

    def stop(self):
        """Clean up the display."""
        if self.started:
            print(SHOW_CURSOR, end="", flush=True)
            self.started = False

    def _redraw(self):
        """Redraw the entire status display."""
        if not self.started:
            return

        # Move cursor up to overwrite previous status display (not messages)
        if self.displayed_lines > 0:
            print(f"\033[{self.displayed_lines}A", end="")

        # Print any queued messages first (these scroll up and are not overwritten)
        for msg in self.messages:
            print(CLEAR_LINE + msg)
        self.messages.clear()

        # Build status lines (these get overwritten each time)
        status_lines = []

        # Summary line
        status_lines.append(CLEAR_LINE + self.summary_line)

        # Build success status
        if self.build_status:
            status_lines.append(CLEAR_LINE + f"  🏗️  {self.build_status}")
        else:
            status_lines.append(CLEAR_LINE)

        # Discovery build status (always show line for consistent height)
        if self.discovery_status:
            status_lines.append(CLEAR_LINE + f"  🔍 {self.discovery_status}")
        else:
            status_lines.append(CLEAR_LINE)

        # Last failed file (clickable path)
        if self.last_failed:
            status_lines.append(CLEAR_LINE + f"  ❌ {self.last_failed}")
        else:
            status_lines.append(CLEAR_LINE)

        # Worker status lines
        for i in range(self.num_workers):
            status = self.worker_status.get(i, "idle")
            status_lines.append(CLEAR_LINE + f"  [{i}] {status}")

        # Print status lines
        output = "\n".join(status_lines)
        print(output, flush=True)
        self.displayed_lines = len(status_lines)

    def set_summary(self, text: str):
        """Update the summary line."""
        with self.lock:
            self.summary_line = text
            self._redraw()

    def set_worker_status(self, worker_id: int, status: str):
        """Update a worker's status."""
        with self.lock:
            self.worker_status[worker_id] = status
            self._redraw()

    def set_discovery_status(self, status: str):
        """Update the discovery build status."""
        with self.lock:
            self.discovery_status = status
            self._redraw()

    def set_build_status(self, status: str):
        """Update the build success status."""
        with self.lock:
            self.build_status = status
            self._redraw()

    def set_last_failed(self, filepath: str, reason: str):
        """Update the last failed file display."""
        with self.lock:
            self.last_failed = f"{filepath}  ({reason})"
            self._redraw()

    def log_message(self, msg: str):
        """Log a message that scrolls up above the status display."""
        with self.lock:
            self.messages.append(msg)
            self._redraw()


class BuildCoordinator:
    """Coordinates parallel file processing with dynamic discovery of new failing files."""

    def __init__(self, num_workers: int):
        self.num_workers = num_workers
        self.work_queue: Queue[str] = Queue()
        self.display = StatusDisplay(num_workers)

        # File tracking (all protected by lock)
        self.lock = Lock()
        self.queued_files: set[str] = set()      # Files in queue or being processed
        self.processed_files: set[str] = set()   # Files we've finished with
        self.in_progress: set[str] = set()       # Files currently being worked on
        self.failed_files: dict[str, str] = {}   # filepath -> reason

        # Statistics
        self.total_fixes = 0
        self.build_count = 0

        # Discovery build control
        self.discovery_build_running = False
        self.discovery_build_pending = False

        # Control
        self.shutdown = False

    def log(self, msg: str):
        """Log a message (scrolls above status display when running)."""
        if self.display.started:
            self.display.log_message(msg)
        else:
            print(msg, flush=True)

    def update_summary(self):
        """Update the summary line with current stats."""
        with self.lock:
            queued = self.work_queue.qsize()
            in_prog = len(self.in_progress)
            done = len(self.processed_files)
            fixes = self.total_fixes
        self.display.set_summary(
            f"📊 Queued: {queued} | In progress: {in_prog} | Done: {done} | Fixes: {fixes}"
        )

    def run_lake_build(self) -> str:
        """Run lake build and capture output."""
        result = subprocess.run(
            ["lake", "build", "--verbose"],
            capture_output=True,
            text=True,
            cwd=PROJECT_DIR
        )
        return result.stdout + result.stderr

    def run_lake_build_file(self, filepath: str) -> str:
        """Run lake build on a specific file and capture output."""
        rel_path = filepath
        if rel_path.startswith("./"):
            rel_path = rel_path[2:]
        if rel_path.endswith(".lean"):
            rel_path = rel_path[:-5]
        module_name = rel_path.replace("/", ".")

        result = subprocess.run(
            ["lake", "build", module_name],
            capture_output=True,
            text=True,
            cwd=PROJECT_DIR
        )
        return result.stdout + result.stderr

    def parse_build_stats(self, build_output: str) -> dict:
        """Parse lake build output for summary statistics."""
        # Get total from [N/M] pattern
        build_pattern = re.compile(r'\[(\d+)/(\d+)\]')
        total_files = 0
        for match in build_pattern.finditer(build_output):
            total_files = max(total_files, int(match.group(2)))

        # Count by marker type (with --verbose, all files are printed)
        built_pattern = re.compile(r'✔ \[\d+/\d+\]')
        fail_pattern = re.compile(r'✖ \[\d+/\d+\]')

        built = len(built_pattern.findall(build_output))
        failed = len(fail_pattern.findall(build_output))

        return {
            "total": total_files,
            "success": built,
            "failed": failed,
        }

    def parse_errors(self, build_output: str) -> dict[str, list[int]]:
        """Parse lake build output to find files with errors and their line numbers."""
        error_pattern = re.compile(r'^error: ([^:\s]+\.lean):(\d+):\d+:', re.MULTILINE)
        files_with_errors: dict[str, list[int]] = {}

        for match in error_pattern.finditer(build_output):
            filepath = match.group(1)
            line_num = int(match.group(2))

            if filepath not in files_with_errors:
                files_with_errors[filepath] = []
            if line_num not in files_with_errors[filepath]:
                files_with_errors[filepath].append(line_num)

        for filepath in files_with_errors:
            files_with_errors[filepath].sort()

        return files_with_errors

    def add_files_to_queue(self, files: list[str]) -> int:
        """Add files to queue if not already queued/processed. Returns count added."""
        added = 0
        with self.lock:
            for f in files:
                if f not in self.queued_files and f not in self.processed_files:
                    self.queued_files.add(f)
                    self.work_queue.put(f)
                    added += 1
        return added

    def request_discovery_build(self):
        """Request a discovery build. Only one runs at a time; extra requests are coalesced."""
        with self.lock:
            if self.discovery_build_running:
                # A build is running; mark that another is needed when it finishes
                self.discovery_build_pending = True
                return
            self.discovery_build_running = True

        # Run builds until no more are pending
        while True:
            self._run_discovery_build()

            with self.lock:
                if self.discovery_build_pending:
                    self.discovery_build_pending = False
                    # Continue loop to run another build
                else:
                    self.discovery_build_running = False
                    self.display.set_discovery_status("")
                    break

    def _run_discovery_build(self):
        """Actually run a discovery build (internal, called by request_discovery_build)."""
        with self.lock:
            self.build_count += 1
            build_num = self.build_count

        self.display.set_discovery_status(f"Build #{build_num} running...")
        build_output = self.run_lake_build()

        log_file = f"/tmp/lake-build-discovery-{build_num}.log"
        with open(log_file, "w") as f:
            f.write(build_output)

        stats = self.parse_build_stats(build_output)
        files_with_errors = self.parse_errors(build_output)

        new_files = [f for f in files_with_errors.keys()
                     if f not in self.queued_files and f not in self.processed_files]
        added = self.add_files_to_queue(new_files)

        self.update_summary()
        self.display.set_build_status(f"{stats['success']}/{stats['total']} built successfully")
        self.display.set_discovery_status(f"Build #{build_num}: +{added} files")

        if added > 0:
            self.log(f"🔍 Discovery #{build_num}: found {added} new files")

    def is_inside_doc_comment(self, lines: list[str], line_idx: int) -> bool:
        """Check if the given line index is inside a /-- ... -/ doc-comment."""
        for i in range(line_idx - 1, -1, -1):
            line = lines[i]
            if "/--" in line:
                start_pos = line.find("/--")
                end_pos = line.find("-/", start_pos + 3)
                if end_pos == -1:
                    return True
                return False
            if "-/" in line:
                return False
        return False

    def find_declaration_start(self, lines: list[str], error_line: int) -> int:
        """Find the start of the declaration containing the error."""
        idx = error_line - 1

        while idx > 0:
            idx -= 1
            if lines[idx].strip() == "":
                if not self.is_inside_doc_comment(lines, idx):
                    return idx + 1

        return 0

    def process_file(self, filepath: str, worker_id: int) -> tuple[int, int]:
        """
        Process a single file, trying to fix errors with set_option.
        Returns (fixes_applied, errors_remaining).
        """
        def status(msg: str):
            self.display.set_worker_status(worker_id, f"{filepath}: {msg}")

        status("starting...")

        if not os.path.exists(filepath):
            self.log(f"✗ File not found: {filepath}")
            return (0, 0)

        fixes_applied = 0

        # Initial build to get errors
        status("building...")
        build_output = self.run_lake_build_file(filepath)
        errors = self.parse_errors(build_output)

        initial_error_count = len(errors.get(filepath, []))

        while filepath in errors and errors[filepath]:
            error_lines = errors[filepath]
            first_error_line = error_lines[0]
            progress = f"line {first_error_line}, fixed {fixes_applied}/{initial_error_count}"

            status(progress)

            with open(filepath, 'r') as f:
                lines = f.readlines()

            decl_start = self.find_declaration_start(lines, first_error_line)

            # Check if set_option is already there
            if decl_start > 0 and SET_OPTION_LINE in lines[decl_start - 1]:
                reason = f"set_option already present at line {decl_start}"
                status(f"⚠ {reason}")
                with self.lock:
                    self.failed_files[filepath] = reason
                self.display.set_last_failed(filepath, reason)
                break

            if lines[decl_start].strip().startswith(SET_OPTION_LINE):
                reason = "set_option already at declaration start"
                status(f"⚠ {reason}")
                with self.lock:
                    self.failed_files[filepath] = reason
                self.display.set_last_failed(filepath, reason)
                break

            # Insert the set_option line
            new_lines = lines[:decl_start] + [SET_OPTION_LINE + "\n"] + lines[decl_start:]

            with open(filepath, 'w') as f:
                f.writelines(new_lines)

            # Rebuild and check - reuse this output for next iteration
            status(f"{progress}, testing...")
            build_output = self.run_lake_build_file(filepath)
            errors = self.parse_errors(build_output)

            expected_error_line = first_error_line + 1

            if filepath in errors and expected_error_line in errors[filepath]:
                reason = f"set_option didn't fix error at line {first_error_line}"
                status(f"{progress}, reverting...")
                with open(filepath, 'w') as f:
                    f.writelines(lines)
                with self.lock:
                    self.failed_files[filepath] = reason
                self.display.set_last_failed(filepath, reason)
                break
            else:
                fixes_applied += 1
                self.log(f"✓ {filepath}:{first_error_line} fixed!")
                # errors dict is already updated from the test build, loop continues

        status("done")
        errors_remaining = len(errors.get(filepath, []))
        return (fixes_applied, errors_remaining)

    def worker(self, worker_id: int):
        """Worker thread that processes files from the queue."""
        self.display.set_worker_status(worker_id, "idle")

        while not self.shutdown:
            try:
                filepath = self.work_queue.get(timeout=1.0)
            except Empty:
                self.display.set_worker_status(worker_id, "idle")
                continue

            with self.lock:
                if filepath in self.processed_files:
                    self.work_queue.task_done()
                    continue
                self.in_progress.add(filepath)

            self.update_summary()

            try:
                fixes, remaining = self.process_file(filepath, worker_id)

                with self.lock:
                    self.in_progress.discard(filepath)
                    self.processed_files.add(filepath)
                    self.total_fixes += fixes

                self.update_summary()

                if fixes > 0:
                    self.log(f"✓ {filepath}: {fixes} fixes applied")
                elif remaining > 0:
                    self.log(f"⚠ {filepath}: {remaining} errors remain")
                else:
                    self.log(f"○ {filepath}: no changes needed")

                self.display.set_worker_status(worker_id, "idle")

                # If we applied fixes, trigger a discovery build
                if fixes > 0:
                    Thread(target=self.request_discovery_build, daemon=True).start()

            except Exception as e:
                self.log(f"✗ {filepath}: {e}")
                with self.lock:
                    self.in_progress.discard(filepath)
                    self.processed_files.add(filepath)
                    self.failed_files[filepath] = f"Exception: {e}"
                self.display.set_worker_status(worker_id, "idle")
                self.update_summary()

            self.work_queue.task_done()

    def run(self):
        """Main entry point."""
        print("=" * 60)
        print("Running initial lake build to find all errors...")
        print("=" * 60)

        build_output = self.run_lake_build()

        with open("/tmp/lake-build-initial.log", "w") as f:
            f.write(build_output)
        print("Build output saved to /tmp/lake-build-initial.log")

        stats = self.parse_build_stats(build_output)
        files_with_errors = self.parse_errors(build_output)

        print(f"\nBuild summary:")
        print(f"  Total files:       {stats['total']}")
        print(f"  Succeeded:         {stats['success']}")
        print(f"  Failed:            {stats['failed']}")
        print(f"  Files with errors: {len(files_with_errors)}")

        if not files_with_errors:
            print("\nNo errors found!")
            return

        self.add_files_to_queue(list(files_with_errors.keys()))

        print(f"\nStarting {self.num_workers} workers...\n")

        # Start the display
        self.display.start()
        self.update_summary()
        self.display.set_build_status(f"{stats['success']}/{stats['total']} built successfully")

        try:
            # Start workers
            for i in range(self.num_workers):
                Thread(target=self.worker, args=(i,), daemon=True).start()

            # Wait for queue to drain and all work to complete
            while True:
                with self.lock:
                    active = len(self.in_progress)
                    queued = self.work_queue.qsize()

                if active == 0 and queued == 0:
                    # Double-check after a brief pause
                    time.sleep(0.5)
                    with self.lock:
                        if len(self.in_progress) == 0 and self.work_queue.qsize() == 0:
                            break

                time.sleep(0.5)

            self.shutdown = True

        finally:
            self.display.stop()

        # Final summary
        print("\n" + "=" * 60)
        print("FINAL SUMMARY")
        print("=" * 60)

        print(f"\nTotal fixes applied: {self.total_fixes}")
        print(f"Files processed: {len(self.processed_files)}")
        print(f"Discovery builds: {self.build_count}")

        if self.failed_files:
            print("\n" + "=" * 60)
            print("FILES THAT NEED MANUAL ATTENTION")
            print("=" * 60)
            for filepath, reason in sorted(self.failed_files.items()):
                print(f"  {filepath}")
                print(f"    Reason: {reason}")


def main():
    num_workers = os.cpu_count() or 4
    coordinator = BuildCoordinator(num_workers)

    try:
        coordinator.run()
    except KeyboardInterrupt:
        coordinator.display.stop()
        print("\n\nInterrupted by user")
        sys.exit(1)


if __name__ == "__main__":
    main()
