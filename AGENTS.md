# Project collaboration rules

- Scope is the 33-bus / 12-node system unless the user explicitly expands it.
- Use this repository for subsequent work requested in this conversation. Preserve existing work and inspect the current branch before editing.
- Record each completed change and each material report, question, and user answer in the root REUSE.md. Append a unique CHG-NNNN entry; do not erase history.
- Each entry includes the request, files changed, validation actually executed, remaining limitations, and any pending questions. Never describe pending tests as passed.
- Use a clearly named branch under revcs/ and a commit message beginning with the change ID. Do not merge without the user's instruction.
- Deliver the complete consolidated Julia file after changes, together with environment files and reports. Keep versioned source packages under versions/.
- Keep the downloadable ZIP and SHA256SUMS consistent. Preserve the CI workflow that builds a source ZIP and publishes test logs.
- Never manufacture paper data or report synthetic unit-test values as paper results. Explicitly retain unresolved model assumptions.
- Code and reports are public in this repository. Do not add credentials, account data, or unrelated user files.

- Deliver a single self-contained .jl runtime file for every future step. Bundle sourced data in a clearly separated section of that file; do not require separate data/test files for the user to run it. Keep development tools and provenance in Git.
