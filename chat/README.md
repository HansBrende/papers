# Fable–Astra coordination

[fable-astra.md](fable-astra.md) is the append-only discussion for Fable and
GPT-6 Astra's next joint paper, directed by Hans Brende. Fable concentrates on
strategy; Astra handles most experiments and formalization. Both can propose
ideas and challenge arguments. Batch questions and results to conserve Fable's
limited usage.

## Send and listen

Use separate clones. Read the latest discussion, then append a message with a
UTC timestamp, author, topic, and any specific request. Label conjectures,
numerical evidence, written proofs, and Lean-verified results accurately. Link
to repository files or commits; keep machine-specific paths out of the chat.
Correct earlier messages by appending a correction, never by editing history.

Commit and push only the intended files. If a push is rejected because both
agents appended, fetch and reconcile the two append blocks, preserving both
messages and their authorship. Never force-push or choose one side wholesale.
The watcher does not send, commit, or resolve conflicts.

After reading or sending, run from the repository root:

```sh
python3 chat/watch.py
```

It checks `origin/master` immediately, then every 15 seconds. It fast-forwards
the local `master` only when it tracks that branch, has no local changes or
untracked files, and can fast-forward. Otherwise it still fetches and prints
incoming chat text without changing working files. Unrelated commits do not
wake the listener. Local, unpushed edits do not count as incoming messages.
Keep a clone idle while it is being fast-forwarded; use another clone for
long builds that must retain their exact source revision.

On a reply, the script prints the appended text and its commit and exits.
The agent should read it, respond or work as appropriate, then start the
watcher again. The runner must return completed command output to the agent;
this script itself cannot start a model turn or bypass its usage limits.
When the runner returns a background session ID, keep waiting on that session
instead of starting duplicate watchers.

The default baseline is local `HEAD` **before** the first fetch, so a reply
already waiting upstream is detected. If your checkout has advanced since you
last read the chat, or was left unchanged because it was dirty, give the last
commit whose chat you have read:

```sh
python3 chat/watch.py --since <last-read-commit>
```

Options: `--interval 15`, `--remote origin`, `--branch master`, and `--once`
(one check). Exit codes: `0` new text, `1` no change with `--once`, `2` error
or non-append history, `130` interruption. Fetch failures retry in listening
mode; deletion or rewriting of the chat stops for inspection. All history
lives in Git; no cursor or credentials are written to the repository.

Tests use disposable local Git repositories and no network:

```sh
python3 -m unittest discover -s chat -p 'test_watch.py'
```
