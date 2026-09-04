# Codex task: recover the Lean Verifier tunnel and verify the restart

Work on the local WSL host that contains this repository at approximately:

`~/lean-projects/RiemannResearch`

The ChatGPT Lean Verifier connection failed before Lean was reached. The observed transport failure was an MCP SSE probe returning HTTP 404, after an earlier 429. Treat this as a tunnel/service registration problem unless evidence shows otherwise.

## Safety constraints

- Do not reset or delete Lean agent workspaces.
- Do not modify proofs, dependencies, `lakefile.toml`, or `lean-toolchain` during recovery.
- Do not replace the service unit or tunnel profile unless diagnostics prove one is malformed.
- Preserve and report the existing unit definition and recent logs before making any configuration change.
- The permitted first repair action is restarting the existing `lean-tunnel.service`.
- Stop and report rather than guessing if the actual service name, endpoint, or profile materially differs.

## Execute

1. Confirm this is the intended repository and inspect:
   - `git status --short`
   - `systemctl cat lean-tunnel.service`
   - `systemctl status lean-tunnel.service --no-pager --full`
   - the tunnel profile referenced by the service, expected to be near `~/.config/tunnel-client/lean-local.yaml`
2. Run:

   ```bash
   bash tools/recover_lean_verifier.sh
   ```

3. If the script reports that the service is active but `healthz` or `readyz` fails:
   - inspect the service command and tunnel profile;
   - determine the actual local listen address and port;
   - rerun using `LEAN_HEALTH_BASE=http://127.0.0.1:<actual-port>`;
   - do not silently edit configuration merely to match the script default.
4. If the service fails to become active, collect:

   ```bash
   sudo systemctl status lean-tunnel.service --no-pager --full
   sudo journalctl -u lean-tunnel.service -n 200 --no-pager
   ```

   Identify the first causal error, repair only that error, restart, and rerun the recovery script.
5. Verify direct Lean compilation in the repository succeeds. The script tests:

   ```lean
   import Mathlib

   example : 1 + 1 = 2 := by
     norm_num
   ```

6. Report exactly:
   - service active/inactive status;
   - health endpoint results;
   - direct Lean smoke-test result;
   - whether a fresh external tunnel/connection registration was produced;
   - any remaining action that must occur in ChatGPT rather than on the host.

## After host recovery

The existing ChatGPT conversation may remain pinned to the stale remote tunnel identifier. If local service health and Lean compilation pass while ChatGPT still receives HTTP 404, the remaining fix is to reconnect the Lean Verifier or open a fresh ChatGPT session so it obtains the newly registered tunnel.

Once MCP access succeeds, use `agent_workspace_open`, then compile the same smoke theorem through `agent_workspace_run_code`. Only after that should RH work resume.

## Branch scope after recovery

The default Lean workspace publishes to the RH-focused `main` branch. The former
Serre II development is preserved on `serre-ii-archive-20260904`; do not resume it
through the default main-only workspace. Resume RH work only after the smoke test,
or first add and verify explicit branch-aware workspace support for Serre II.
