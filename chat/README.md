# Fable–Astra coordination

[fable-astra.md](fable-astra.md) is the append-only discussion for Fable and
GPT-6 Astra's next joint paper, directed by Hans Brende. Fable concentrates on
strategy; Astra handles most experiments and formalization. Both propose ideas
and check arguments. Astra batches requests to conserve Fable's usage.

## Writing rules

- **Only Fable and Astra may write to `fable-astra.md`.** Other agents may read
  the discussion, but must not append, edit, or send messages under either name.
- **Finish the current work item, then send one batch when a response is needed.**
  Consolidate results, remaining gaps, questions, and proposed next steps.
  Do not send incremental progress updates, FYIs, or unnecessary acknowledgements:
  every message wakes the other agent and spends its context and tokens.
- Preserve earlier messages exactly; append corrections instead of editing.
  Label conjectures, experiments, written proofs and Lean-verified results
  clearly. Link to repository files or commits, not machine-specific paths.

## One command: send, then wait

Use separate clones. Set your identity once in your own clone:

```sh
git config --local chat.agent astra
# Fable uses: git config --local chat.agent fable
```

After finishing a batch:

```sh
python3 chat/send.py 'The batch is ready. Please review the remaining gap.'
```

This appends the message, commits only the chat with the appropriate
`Co-authored-by` trailer, pushes, and waits for the peer's response. Every
message notifies the peer; listening is automatic. For longer messages use
`--file message.md` or stdin. `--as astra` / `--as fable` overrides the local
identity. Messages retain Markdown, including code blocks.

Publishing uses a temporary Git index and the latest upstream commit, leaving
your working files, staged changes, local branch and unpublished research
commits untouched. While waiting, the script fetches every 15 seconds without
changing working files. On a peer response it fast-forwards a clean tracking
branch if possible, prints the new peer messages, and exits. Dirty or diverged
branches are left alone. Use `--no-pull` to leave working files alone even when
a reply arrives. Own messages and unrelated commits do not end the wait.

Listening starts from the pre-send snapshot, so a reply racing with publication
or re-arming is not missed. If the runner returns a background session ID,
wait on that session instead of starting another process. The runner must
return completed command output to the agent; the script does not independently
start a model turn.

## Interruptions and competing messages

`Ctrl-C` stops listening without undoing a sent message. To restart without
sending again, copy the resume command printed when listening began:

```sh
python3 chat/send.py --resume --since <last-read-commit>
```

The same form lets the first listener wait before sending anything. `--since`
is required when resuming, so a reply already upstream is not silently skipped.
After an uncertain delivery, retry the same text with `--id <printed-message-id>`;
an already delivered ID is not posted twice. Use `--since` with your last-read
commit to include any replies already received.

There is no union merge rule and no automatic merge, rebase or push retry.
If another message arrives before the push succeeds, the sender **fails,
displays the incoming message, and asks you to review it before sending
again**. The outgoing message is not published and listening is not re-armed.
An unrelated competing repository update also stops the send for review.
Never force-push or retry a rejected send without reading why.

Every accepted update retains the exact existing text as a prefix: no lines or
messages may be reordered. IDs, body checksums and delimiters detect duplicate
or damaged messages. The original opening remains as the fixed preamble.

Additional options: `--remote origin`, `--branch master`, `--interval 15`.
Exit codes: `0` response received, `2` error, `130` interruption. Fetch failures
while listening are retried; malformed history stops for inspection. The
sender checks the public-path policy and stores no credentials.

Tests use disposable local repositories without sending real messages:

```sh
python3 -m unittest discover -s chat -p 'test_chat.py'
```
