"""Coding agent for the proof engine. Edits src/theorems/ only.

Usage:
    python agent.py
    python agent.py --max-turns 50

API key loaded from .env. Goals defined in goal.py.
"""

import os
import sys
import json
import subprocess

sys.path.insert(0, os.path.join(os.path.dirname(__file__), 'vendor'))

from dotenv import load_dotenv
load_dotenv()

import anthropic
client = anthropic.Anthropic()

TOOLS = [
    {
        "name": "read_file",
        "description": "Read a file. Always read before editing.",
        "input_schema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "offset": {"type": "integer", "description": "Start line (1-indexed)"},
                "limit": {"type": "integer", "description": "Number of lines"},
            },
            "required": ["path"],
        },
    },
    {
        "name": "edit_file",
        "description": "Replace lines in a file under src/theorems/ only. Specify start line and number of lines to replace.",
        "input_schema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "offset": {"type": "integer", "description": "Start line (1-indexed)"},
                "count": {"type": "integer", "description": "Number of lines to remove"},
                "text": {"type": "string", "description": "Replacement text"},
            },
            "required": ["path", "offset", "count", "text"],
        },
    },
    {
        "name": "run",
        "description": "Run a shell command. Use for testing.",
        "input_schema": {
            "type": "object",
            "properties": {
                "command": {"type": "string"},
            },
            "required": ["command"],
        },
    },
    {
        "name": "commit",
        "description": "Git add files and commit.",
        "input_schema": {
            "type": "object",
            "properties": {
                "message": {"type": "string"},
                "files": {
                    "type": "array",
                    "items": {"type": "string"},
                },
            },
            "required": ["message", "files"],
        },
    },
    {
        "name": "done",
        "description": "Signal that the task is complete.",
        "input_schema": {
            "type": "object",
            "properties": {
                "summary": {"type": "string"},
            },
            "required": ["summary"],
        },
    },
]

SYSTEM = """You are a coding agent working on a formal proof engine.

Project: a sequent calculus engine that verifies proofs from ZFC axioms.
You can only edit files under src/theorems/. Core, definitions, and tactics are fixed.

Test command: python goal.py
This runs the goals and prints pass/fail for each.

Test with: python goal.py
Commit when tests pass.
When all goals pass, call the done tool."""


def execute_tool(name, inp):
    if name == "read_file":
        try:
            with open(inp["path"]) as f:
                lines = f.readlines()
        except FileNotFoundError:
            return f"Error: {inp['path']} not found"
        offset = inp.get("offset", 1) - 1
        limit = inp.get("limit", len(lines) - offset)
        selected = lines[max(0, offset):offset + limit]
        return "".join(f"{i + offset + 1}\t{line}" for i, line in enumerate(selected))

    elif name == "edit_file":
        path = inp["path"]
        if not path.startswith("src/theorems/"):
            return f"Error: can only edit files under src/theorems/"
        try:
            with open(path) as f:
                lines = f.readlines()
        except FileNotFoundError:
            return f"Error: {path} not found"
        offset = inp["offset"] - 1
        count = inp["count"]
        if offset < 0 or offset > len(lines):
            return f"Error: offset out of range (file has {len(lines)} lines)"
        new_lines = inp["text"].splitlines(True)
        if new_lines and not new_lines[-1].endswith("\n"):
            new_lines[-1] += "\n"
        lines[offset:offset + count] = new_lines
        with open(path, "w") as f:
            f.writelines(lines)
        return "OK"

    elif name == "run":
        try:
            result = subprocess.run(
                inp["command"], shell=True,
                capture_output=True, text=True, timeout=300,
            )
            out = ""
            if result.stdout:
                out += result.stdout[-3000:]
            if result.stderr:
                out += "\nSTDERR:\n" + result.stderr[-1000:]
            out += f"\nexit: {result.returncode}"
            return out or "(no output)"
        except subprocess.TimeoutExpired:
            return "Error: timeout"

    elif name == "commit":
        for f in inp["files"]:
            subprocess.run(["git", "add", f], capture_output=True)
        result = subprocess.run(
            ["git", "commit", "-m", inp["message"]],
            capture_output=True, text=True,
        )
        return result.stdout + result.stderr

    elif name == "done":
        return "DONE"

    return f"Error: unknown tool {name}"


def run_agent(task, max_turns=200):
    messages = [{"role": "user", "content": task}]

    for turn in range(max_turns):
        response = client.messages.create(
            model="claude-sonnet-4-6",
            max_tokens=16000,
            system=SYSTEM,
            tools=TOOLS,
            messages=messages,
            thinking={"type": "adaptive"},
        )

        # Print text
        for block in response.content:
            if block.type == "text":
                print(block.text)

        if response.stop_reason == "end_turn":
            print(f"\n[stopped after {turn + 1} turns]")
            return

        tool_uses = [b for b in response.content if b.type == "tool_use"]
        if not tool_uses:
            return

        messages.append({"role": "assistant", "content": response.content})

        tool_results = []
        for tool in tool_uses:
            print(f"  [{tool.name}] {json.dumps(tool.input)[:120]}")
            result = execute_tool(tool.name, tool.input)
            if tool.name == "done":
                print(f"\n{tool.input['summary']}")
                print(f"[completed in {turn + 1} turns]")
                return
            print(f"  -> {result[:120]}")
            tool_results.append({
                "type": "tool_result",
                "tool_use_id": tool.id,
                "content": result,
            })

        messages.append({"role": "user", "content": tool_results})

    print(f"\n[max turns ({max_turns}) reached]")


if __name__ == "__main__":
    max_turns = 200
    if "--max-turns" in sys.argv:
        idx = sys.argv.index("--max-turns")
        max_turns = int(sys.argv[idx + 1])

    # Read goal.py for context
    with open("goal.py") as f:
        goal_src = f.read()

    task = f"""Fix the theorems in src/theorems/ so that goal.py passes.

goal.py:
```python
{goal_src}
```

Run `python goal.py` to test. Read the relevant theorem files to understand what needs to change."""

    run_agent(task, max_turns)
