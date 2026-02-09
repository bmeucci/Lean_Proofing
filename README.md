# LeanProofing

Formal verification of mathematical proofs using Lean 4 and Mathlib.

## Setup

This project requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
# Install elan
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Fetch dependencies and Mathlib cache
lake update
lake exe cache get

# Build the project
lake build
```

## Project Structure

- `LeanProofing/` - Lean source files containing formal proofs
- `paper/` - Source paper (PDF) being formalized
- `lakefile.toml` - Project configuration and dependencies
- `lean-toolchain` - Lean version specification

## Adding the paper

Place your paper PDF in the `paper/` directory. The formalization will be developed
in corresponding `.lean` files under `LeanProofing/`.
