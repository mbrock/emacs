#!/usr/bin/env bash
set -euo pipefail

if [[ ${1-} == "" ]]; then
  echo "Usage: $0 INPUT_EL [OUTPUT_ELN]" >&2
  echo "  INPUT_EL   Path to the Elisp file to compile." >&2
  echo "  OUTPUT_ELN Destination .eln (defaults to alongside INPUT_EL)." >&2
  echo "Environment variables:" >&2
  echo "  EMACS_BIN           Path to the Emacs binary (default: repo src/emacs)." >&2
  echo "  COMPHACK_CC         C compiler command (for example: gcc or tcc)." >&2
  echo "  COMPHACK_SKIP_LOAD  If set to 1, skip loading the resulting .eln." >&2
  exit 1
fi

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
REPO_ROOT=$(cd -- "$SCRIPT_DIR/.." && pwd)
EMACS_BIN=${EMACS_BIN:-"$REPO_ROOT/src/emacs"}
COMPHACK_LISP="$REPO_ROOT/lisp/emacs-lisp/comphack/comphack.el"

if [[ ! -x "$EMACS_BIN" ]]; then
  echo "error: EMACS_BIN is not executable: $EMACS_BIN" >&2
  exit 2
fi

INPUT_EL=$(realpath "$1")
if [[ ! -f "$INPUT_EL" ]]; then
  echo "error: INPUT_EL does not exist: $INPUT_EL" >&2
  exit 3
fi

if [[ $# -ge 2 ]]; then
  OUTPUT_ELN=$(realpath "$2")
else
  OUTPUT_ELN="${INPUT_EL%.*}.eln"
fi

mkdir -p -- "$(dirname -- "$OUTPUT_ELN")"

COMPHACK_INPUT="$INPUT_EL" COMPHACK_OUTPUT="$OUTPUT_ELN" "$EMACS_BIN" -Q --batch \
  -l "$COMPHACK_LISP" \
  --eval '(let ((input (getenv "COMPHACK_INPUT"))
                (output (getenv "COMPHACK_OUTPUT"))
                (cc (getenv "COMPHACK_CC")))
            (when (and cc (not (equal cc "")))
              (setq native-comp-comphack-cc cc))
            (comphack-compile-to-eln input output))'

if [[ "${COMPHACK_SKIP_LOAD:-0}" != "1" ]]; then
  COMPHACK_LOAD_TARGET="$OUTPUT_ELN" "$EMACS_BIN" -Q --batch \
    --eval '(let ((eln (getenv "COMPHACK_LOAD_TARGET")))
              (load eln nil t)
              (message "Loaded %s" eln))'
fi

echo "ELN ready at $OUTPUT_ELN"
