#!/usr/bin/env bash
set -euo pipefail

if [[ ${2-} == "" ]]; then
  echo "Usage: $0 SOURCE_EL CANDIDATE_ELN [FUNCTION_PREFIXES]" >&2
  echo "  FUNCTION_PREFIXES defaults to cconv-; separate several with commas." >&2
  echo "Environment variables:" >&2
  echo "  EMACS_BIN          Emacs executable (default: src/emacs or src/bootstrap-emacs)." >&2
  echo "  COMPHACK_TRACE_DIR Preserve artifacts in this directory." >&2
  exit 1
fi

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
TRACE_LISP="$SCRIPT_DIR/differential-trace.el"
COMPHACK_LISP="$REPO_ROOT/lisp/emacs-lisp/comphack/comphack.el"

if [[ -n ${EMACS_BIN-} ]]; then
  EMACS=$EMACS_BIN
elif [[ -x "$REPO_ROOT/src/emacs" ]]; then
  EMACS="$REPO_ROOT/src/emacs"
else
  EMACS="$REPO_ROOT/src/bootstrap-emacs"
fi

SOURCE=$(realpath "$1")
CANDIDATE=$(realpath "$2")
PREFIXES=${3:-cconv-}
TRACE_DIR=${COMPHACK_TRACE_DIR:-$(mktemp -d /tmp/comphack-trace.XXXXXX)}
mkdir -p -- "$TRACE_DIR"

if [[ ! -x "$EMACS" ]]; then
  echo "error: Emacs is not executable: $EMACS" >&2
  exit 2
fi

run_trace() {
  local mode=$1
  local output=$2
  shift 2
  COMPHACK_TRACE_MODE=$mode \
  COMPHACK_TRACE_SOURCE=$SOURCE \
  COMPHACK_TRACE_OUTPUT=$output \
  COMPHACK_TRACE_FILE="$TRACE_DIR/events.el" \
  COMPHACK_TRACE_REPORT="$TRACE_DIR/report.txt" \
  COMPHACK_TRACE_PREFIXES=$PREFIXES \
    "$EMACS" -Q --batch -l "$COMPHACK_LISP" "$@" -l "$TRACE_LISP"
}

echo "Recording known-good compiler trace..."
run_trace record "$TRACE_DIR/baseline.c"

echo "Checking that the trace is deterministic..."
run_trace compare "$TRACE_DIR/control.c" -l "$SOURCE"

echo "Comparing candidate compiler..."
set +e
run_trace compare "$TRACE_DIR/candidate.c" -l "$CANDIDATE"
status=$?
set -e

echo "Trace artifacts: $TRACE_DIR"
if [[ $status -ne 0 ]]; then
  if [[ -f "$TRACE_DIR/report.txt" ]]; then
    echo
    cat "$TRACE_DIR/report.txt"
  fi
fi
exit "$status"
