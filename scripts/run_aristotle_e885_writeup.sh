#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROMPT_FILE="${ROOT}/prompts/e885_aristotle_writeup_prompt.txt"
STAMP="$(date +%Y%m%d-%H%M%S)"
WORK_DIR="${ROOT}/artifacts/aristotle/e885-writeup-${STAMP}"
BUNDLE_DIR="${WORK_DIR}/bundle"
OUT_DIR="${WORK_DIR}/result"
ARCHIVE_PATH="${WORK_DIR}/result.tar.gz"

if [[ -z "${ARISTOTLE_API_KEY:-}" ]]; then
  echo "ARISTOTLE_API_KEY is not set." >&2
  exit 1
fi

mkdir -p "${BUNDLE_DIR}" "${OUT_DIR}"
mkdir -p "${BUNDLE_DIR}/FormalConjectures/Problems/Erdos"

cp "${ROOT}/README.md" "${BUNDLE_DIR}/README.md"
cp "${ROOT}/lakefile.toml" "${BUNDLE_DIR}/lakefile.toml"
cp "${ROOT}/lean-toolchain" "${BUNDLE_DIR}/lean-toolchain"
cp -R "${ROOT}/FormalConjectures/Util" "${BUNDLE_DIR}/FormalConjectures/"
cp -R "${ROOT}/FormalConjectures/Problems/Erdos/E885" \
  "${BUNDLE_DIR}/FormalConjectures/Problems/Erdos/"
cp "${PROMPT_FILE}" "${BUNDLE_DIR}/ARISTOTLE_TASK.txt"

PROMPT="$(cat "${PROMPT_FILE}")"

echo "Submitting Aristotle E885 writeup job..."
echo "Bundle: ${BUNDLE_DIR}"
echo "Output: ${OUT_DIR}"

uvx --from aristotlelib@1.0.1 aristotle submit \
  "${PROMPT}" \
  --project-dir "${BUNDLE_DIR}" \
  --wait \
  --destination "${ARCHIVE_PATH}"

rm -rf "${OUT_DIR}"
mkdir -p "${OUT_DIR}"
tar -xzf "${ARCHIVE_PATH}" -C "${OUT_DIR}"

echo "Aristotle archive downloaded to ${ARCHIVE_PATH}"
echo "Aristotle output unpacked to ${OUT_DIR}"
