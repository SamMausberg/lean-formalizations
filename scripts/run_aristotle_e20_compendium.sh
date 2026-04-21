#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PROMPT_FILE="${ROOT}/prompts/e20_aristotle_compendium_prompt.txt"
SOURCE_TEX="${ROOT}/sunflower_compendium_research_notes_augmented_revised.tex"
STAMP="$(date +%Y%m%d-%H%M%S)"
WORK_DIR="${ROOT}/artifacts/aristotle/e20-compendium-${STAMP}"
BUNDLE_DIR="${WORK_DIR}/bundle"
OUT_DIR="${WORK_DIR}/result"
ARCHIVE_PATH="${WORK_DIR}/result.tar.gz"

if [[ -z "${ARISTOTLE_API_KEY:-}" ]]; then
  echo "ARISTOTLE_API_KEY is not set." >&2
  exit 1
fi

mkdir -p "${BUNDLE_DIR}" "${OUT_DIR}"
mkdir -p "${BUNDLE_DIR}/FormalConjectures/Problems/Erdos"
mkdir -p "${BUNDLE_DIR}/FormalConjectures/Problems"
mkdir -p "${BUNDLE_DIR}/FormalConjectures"

cp "${ROOT}/README.md" "${BUNDLE_DIR}/README.md"
cp "${ROOT}/lakefile.toml" "${BUNDLE_DIR}/lakefile.toml"
cp "${ROOT}/lake-manifest.json" "${BUNDLE_DIR}/lake-manifest.json"
cp "${ROOT}/lean-toolchain" "${BUNDLE_DIR}/lean-toolchain"
cp "${ROOT}/FormalConjectures.lean" "${BUNDLE_DIR}/FormalConjectures.lean"
cp "${ROOT}/FormalConjectures/Problems.lean" "${BUNDLE_DIR}/FormalConjectures/Problems.lean"
cp "${ROOT}/FormalConjectures/Problems/Erdos.lean" \
  "${BUNDLE_DIR}/FormalConjectures/Problems/Erdos.lean"
cp -R "${ROOT}/FormalConjectures/Util" "${BUNDLE_DIR}/FormalConjectures/"
cp -R "${ROOT}/FormalConjectures/Problems/Erdos/E20" \
  "${BUNDLE_DIR}/FormalConjectures/Problems/Erdos/"
cp "${SOURCE_TEX}" "${BUNDLE_DIR}/sunflower_compendium_research_notes_augmented_revised.tex"
cp "${PROMPT_FILE}" "${BUNDLE_DIR}/ARISTOTLE_TASK.txt"

git -C "${ROOT}" rev-parse HEAD > "${BUNDLE_DIR}/E20_COMMIT.txt"

rg -n "^(theorem|lemma|proposition|corollary|def|structure|class|abbrev) " \
  "${ROOT}/FormalConjectures/Problems/Erdos/E20" -g '*.lean' \
  > "${BUNDLE_DIR}/THEOREM_INVENTORY.txt"

rg -n "\\bsorry\\b" "${ROOT}/FormalConjectures/Problems/Erdos/E20" -g '*.lean' \
  > "${BUNDLE_DIR}/E20_SORRY_INVENTORY.txt" || true

python3 - <<'PY' > "${BUNDLE_DIR}/COMPENDIUM_STATEMENT_INVENTORY.tsv"
import pathlib
import re

source = pathlib.Path("sunflower_compendium_research_notes_augmented_revised.tex")
text = source.read_text()
pat = re.compile(
    r'\\begin\{(theorem|lemma|proposition|corollary)\}'
    r'(?:\[[^\]]*\])?'
    r'(?:\\label\{([^}]*)\})?'
)

print("index\tkind\tlabel\tline")
for i, match in enumerate(pat.finditer(text), 1):
    kind, label = match.groups()
    line = text.count("\n", 0, match.start()) + 1
    print(f"{i}\t{kind}\t{label or ''}\t{line}")
PY

PROMPT="$(cat "${PROMPT_FILE}")"

echo "Submitting Aristotle E20 compendium job..."
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
