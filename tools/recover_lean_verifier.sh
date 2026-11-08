#!/usr/bin/env bash
# Recover and diagnose the local Lean Verifier MCP tunnel.
#
# Usage from WSL:
#   cd ~/lean-projects/RiemannResearch
#   bash tools/recover_lean_verifier.sh
#
# Optional overrides:
#   LEAN_TUNNEL_SERVICE=my-unit.service \
#   LEAN_HEALTH_BASE=http://127.0.0.1:8080 \
#   bash tools/recover_lean_verifier.sh

set -Eeuo pipefail

SERVICE="${LEAN_TUNNEL_SERVICE:-lean-tunnel.service}"
HEALTH_BASE="${LEAN_HEALTH_BASE:-http://127.0.0.1:8080}"
REPO_ROOT="${LEAN_REPO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
WAIT_SECONDS="${LEAN_RECOVERY_WAIT_SECONDS:-30}"

log() {
  printf '[lean-verifier-recovery] %s\n' "$*"
}

fail() {
  printf '[lean-verifier-recovery] ERROR: %s\n' "$*" >&2
  exit 1
}

show_diagnostics() {
  log "Service status:"
  sudo systemctl status "$SERVICE" --no-pager --full || true
  log "Recent service logs:"
  sudo journalctl -u "$SERVICE" -n 120 --no-pager || true
}

command -v systemctl >/dev/null 2>&1 || fail "systemctl is not available; this script must run in the WSL distribution hosting the verifier."
command -v curl >/dev/null 2>&1 || fail "curl is required for health checks."
command -v sudo >/dev/null 2>&1 || fail "sudo is required to restart and inspect $SERVICE."

if ! systemctl list-unit-files --type=service --no-legend | awk '{print $1}' | grep -Fxq "$SERVICE"; then
  fail "Systemd unit $SERVICE was not found. Inspect 'systemctl list-unit-files | grep -i lean' before changing anything."
fi

log "Repository: $REPO_ROOT"
log "Tunnel service: $SERVICE"
log "Health base: $HEALTH_BASE"

log "Current unit definition:"
sudo systemctl cat "$SERVICE" || true

log "Restarting $SERVICE"
sudo systemctl restart "$SERVICE"

log "Waiting for the service to become active (maximum ${WAIT_SECONDS}s)"
active=0
for ((i = 1; i <= WAIT_SECONDS; i++)); do
  if systemctl is-active --quiet "$SERVICE"; then
    active=1
    break
  fi
  sleep 1
done

if [[ "$active" -ne 1 ]]; then
  show_diagnostics
  fail "$SERVICE did not become active."
fi

sudo systemctl status "$SERVICE" --no-pager --full

check_endpoint() {
  local endpoint="$1"
  local body
  if ! body="$(curl --fail --silent --show-error --max-time 10 "$endpoint")"; then
    return 1
  fi
  printf '%s\n' "$body"
}

health_ok=1
for suffix in healthz readyz; do
  endpoint="${HEALTH_BASE%/}/$suffix"
  log "Checking $endpoint"
  if ! response="$(check_endpoint "$endpoint")"; then
    health_ok=0
    printf '[lean-verifier-recovery] Health check failed: %s\n' "$endpoint" >&2
  else
    printf '[lean-verifier-recovery] %s -> %s\n' "$endpoint" "$response"
  fi
done

if [[ "$health_ok" -ne 1 ]]; then
  show_diagnostics
  fail "The service is active, but one or more local health checks failed. Verify the listen address/port in the unit and tunnel profile; rerun with LEAN_HEALTH_BASE if needed."
fi

backend="${LEAN_VERIFICATION_BACKEND:-bazel}"
log "Running a local verification smoke test with backend=$backend"
if [[ "$backend" == bazel ]]; then
  command -v bazel >/dev/null 2>&1 || fail "bazel is not on PATH in this WSL shell."
  (
    cd "$REPO_ROOT"
    python3 tools/bazel_verification.py --fix
    python3 tools/bazel_verification.py --check
    bazel build --config=buildbuddy //:smoke
  )
elif [[ "$backend" == lake ]]; then
  command -v lake >/dev/null 2>&1 || fail "lake is not on PATH in this WSL shell."
  smoke_dir="$(mktemp -d)"
  trap 'rm -rf "$smoke_dir"' EXIT
  cat >"$smoke_dir/LeanVerifierSmoke.lean" <<'LEAN'
import Mathlib.Tactic.NormNum

example : 1 + 1 = 2 := by
  norm_num
LEAN
  (
    cd "$REPO_ROOT"
    lake env lean "$smoke_dir/LeanVerifierSmoke.lean"
  )
else
  fail "LEAN_VERIFICATION_BACKEND must be bazel or lake."
fi

log "Local service health and $backend smoke verification succeeded."
log "Next: reconnect/open a fresh ChatGPT Lean Verifier session if the existing session still reports the stale remote tunnel 404."
log "Then run agent_workspace_open and submit a queued check through the MCP tool and confirm its reported backend."

