"""Autonomous coding agent using Claude API.

Usage:
    ANTHROPIC_API_KEY=... python agent.py "task description"
    ANTHROPIC_API_KEY=... python agent.py "task description" --max-turns 50
"""

import os
import sys
import json
import subprocess
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
        "description": "Replace exact text in a file. old_text must match uniquely.",
        "input_schema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "old_text": {"type": "string"},
                "new_text": {"type": "string"},
            },
            "required": ["path", "old_text", "new_text"],
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

SYSTEM = """You are a disciplined coding agent working on a formal proof engine.

Rules:
1. Read before you edit.
2. One edit at a time.
3. Test after every edit.
4. Commit after each test passes.
5. No shortcuts. No batch edits.

When done, call the done tool with a summary."""


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
        try:
            with open(inp["path"]) as f:
                content = f.read()
        except FileNotFoundError:
            return f"Error: {inp['path']} not found"
        count = content.count(inp["old_text"])
        if count == 0:
            return "Error: old_text not found"
        if count > 1:
            return f"Error: old_text found {count} times, must be unique"
        content = content.replace(inp["old_text"], inp["new_text"], 1)
        with open(inp["path"], "w") as f:
            f.write(content)
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
    if len(sys.argv) < 2:
        print("Usage: python agent.py 'task'")
        sys.exit(1)

    max_turns = 200
    args = sys.argv[1:]
    if "--max-turns" in args:
        idx = args.index("--max-turns")
        max_turns = int(args[idx + 1])
        args = args[:idx] + args[idx + 2:]

    run_agent(args[0], max_turns)
