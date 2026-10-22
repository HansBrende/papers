"""Describe executed commands without publishing machine-specific paths.

The returned command is a portable description, not the literal subprocess
argv: its executable is the caller-supplied tool label, path operands are
relative to the recorded cwd, and cwd is relative to the project root.
Subprocesses must still receive the original command. Only explicitly marked
path operands are converted; option names and other arguments are untouched.
"""
from pathlib import Path, PureWindowsPath
import os


def _absolute(value):
    return Path(value).is_absolute() or PureWindowsPath(value).is_absolute()


def command_record(command, *, root, cwd, executable_label, path_indices=()):
    """Return a portable command/cwd record, rejecting unaccounted paths.

Marked path operands and cwd must be within root. Unexpected absolute operands
are rejected, rather than guessed or silently included in public receipts.
For an option such as ``--source-root PATH``, mark only the PATH index.
"""
    if not command or not executable_label or '/' in executable_label or '\\' in executable_label:
        raise ValueError('A command and a path-free executable label are required')
    root, cwd = Path(root).resolve(), Path(cwd).resolve()
    relative_cwd = cwd.relative_to(root).as_posix()
    indices = set(path_indices)
    if any(not isinstance(i, int) or i <= 0 or i >= len(command) for i in indices):
        raise ValueError('Path operand indices must identify non-executable arguments')
    display = [executable_label]
    for index, raw in enumerate(command[1:], 1):
        value = os.fspath(raw)
        if index in indices:
            path = Path(value)
            path = (path if path.is_absolute() else cwd / path).resolve()
            path.relative_to(root)  # Do not publish paths outside this project.
            value = Path(os.path.relpath(path, cwd)).as_posix()
        elif _absolute(value) or ('=' in value and _absolute(value.split('=', 1)[1])):
            raise ValueError('Absolute command operand requires an explicit path index')
        display.append(value)
    return {'command': display, 'cwd': relative_cwd,
            'command_format': 'portable tool label; operands relative to cwd; cwd relative to project root'}
