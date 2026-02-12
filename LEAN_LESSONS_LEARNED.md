# Lean 4 + Mathlib Compilation: Lessons Learned

A complete record of every issue encountered during the formalization of
"The Golden-Ratio Polyhedral Journey" in Lean 4 with Mathlib, how each was
diagnosed, and how to avoid it from the start.

---

## 1. Environment & Setup

### 1.1 Lean version must exactly match Mathlib's expectation

**Problem:** Installed Lean 4.27.0 but Mathlib master required 4.28.0-rc1.
Build failed with cryptic errors.

**Solution:** Always check Mathlib's `lean-toolchain` file first:
```bash
curl -s https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain
```
Then set your project's `lean-toolchain` to match exactly.

**Prevention:** Before starting, clone or check Mathlib's current `lean-toolchain`
and pin yours to the same version from the beginning.

### 1.2 `lake: command not found` in Codespaces

**Problem:** Opening a fresh Codespace terminal doesn't have `lake` on PATH.

**Solution:**
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
echo 'source ~/.elan/env' >> ~/.bashrc
source ~/.elan/env
```

**Prevention:** Always add `source ~/.elan/env` to `.bashrc` immediately after
installing elan. This ensures every new terminal session has lake available.

### 1.3 Mathlib dependency resolution via Reservoir blocked

**Problem:** `lake init ... math` failed because the Reservoir package registry
was blocked by proxy/firewall.

**Solution:** Specify Mathlib via direct git URL in `lakefile.toml`:
```toml
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "master"
```

**Prevention:** Always use direct git URLs for dependencies rather than relying
on Reservoir lookups, especially in restricted environments.

### 1.4 Precompiled Mathlib cache

**Problem:** Building Mathlib from source takes 1-2+ hours.

**Solution:** Run `lake exe cache get` before `lake build` to download
precompiled .olean files from Azure blob storage.

**Prevention:** Always run `lake exe cache get` as the first step after
`lake update`. Include it in all build instructions.

### 1.5 Always capture build output

**Problem:** Long builds finish while you're away; terminal history lost
when Codespace disconnects.

**Solution:**
```bash
lake build 2>&1 | tee build.log
```

Check later with `tail -20 build.log`.

**Prevention:** Always use `tee build.log` on every build. Make it a habit.

---

## 2. Import Path Issues

### 2.1 Mathlib modules get renamed/moved between versions

**Problem:** `import Mathlib.GroupTheory.Subgroup.Basic` failed — module
moved to `Mathlib.Algebra.Group.Subgroup.Basic`.

**Diagnosis:** Error message: "unknown module" or "could not find module."

**Solution:** Search the Mathlib source for the correct current path:
```bash
find .lake/packages/mathlib -name "*.lean" | xargs grep "namespace Subgroup" | head
```

**Prevention:** When writing imports, search the actual installed Mathlib
source rather than relying on documentation or memory. Module paths change
frequently between Mathlib versions.

### 2.2 Deprecated imports produce warnings

**Problem:** `import Mathlib.Data.Real.Irrational` produced a deprecation warning.

**Solution:** Remove the import; the needed functionality was available through
other imports.

**Prevention:** If a file compiles but gives import warnings, clean them up
immediately — they may become errors in future Mathlib versions.

---

## 3. Lemma/API Name Changes

### 3.1 `div_add_eq_add_div` removed from Mathlib

**Problem:** `Unknown identifier 'div_add_eq_add_div'`

**Solution:** Replaced proof strategy using `field_simp` + `nlinarith` instead
of manual rewriting with named lemmas.

**Prevention:** **Prefer tactic-based proofs over named-lemma rewrites.**
Tactics like `field_simp`, `nlinarith`, `linarith`, `ring`, `norm_num` are
far more stable across Mathlib versions than specific lemma names.

### 3.2 `pow_lt_pow_right` renamed to `pow_lt_pow_right₀` with different signature

**Problem:** First attempt: "Unknown identifier `pow_lt_pow_right`."
Second attempt with `pow_lt_pow_right₀`: "Application type mismatch."

**Original broken code:**
```lean
apply pow_lt_pow_right₀ (le_of_lt φ_pos) (ne_of_gt φ_gt_one).symm
omega
```

**Actual signature:** `pow_lt_pow_right₀ (h : 1 < a) (hmn : m < n) : a ^ m < a ^ n`

**Working code:**
```lean
exact pow_lt_pow_right₀ φ_gt_one (by omega)
```

**Prevention:** When you get a type mismatch, read the expected type carefully.
Use `apply` and let Lean show you what arguments it expects rather than guessing
the full signature. Or search the Mathlib source:
```bash
grep -r "pow_lt_pow_right" .lake/packages/mathlib --include="*.lean" -l
```

### 3.3 `MulAction.IsPretransitive.nonempty` doesn't exist

**Problem:** Tried to derive `Nonempty F` from a pretransitive action.
The constant simply doesn't exist.

**Reason:** A pretransitive action is vacuously true on an empty set.
`Nonempty` must be a separate hypothesis.

**Solution:** Removed the problematic proof steps (the theorem already
used `sorry` and was later removed entirely).

**Prevention:** For group actions in Mathlib, always provide `[Nonempty F]`
as a separate hypothesis alongside `[MulAction.IsPretransitive G F]`.

### 3.4 `List.maximum?` doesn't exist

**Problem:** `Invalid field 'maximum?': The environment does not contain
'List.maximum?'`

**Solution:** Replaced with equivalent formulation:
```lean
theorem max_face_count :
    60 ∈ faceCountJourney ∧ ∀ n ∈ faceCountJourney, n ≤ 60 := by
  constructor
  · simp [faceCountJourney, ...]
  · intro n hn; simp [...] at hn; omega
```

**Prevention:** Before using any `List.` or `Finset.` method, verify it exists
in the current Mathlib version. When in doubt, state the property directly
rather than calling a library function.

---

## 4. Lean 4 Language Rules

### 4.1 `theorem` must return a `Prop` — use `def` for data

**Problem:** `theorem myResult : SomeStructure where ...` fails because
structures are `Type`, not `Prop`.

**Error:** Various type mismatch errors.

**Solution:** Use `def` for anything that produces data (structures, records):
```lean
-- WRONG:
theorem rect_data : RectificationData where ...

-- RIGHT:
def rect_data : RectificationData where ...
```

**Rule:** `theorem` is ONLY for `Prop`-valued statements (equalities,
inequalities, logical assertions). Everything else is `def`.

### 4.2 `rfl` only works for definitional equality

**Problem:** `rfl` failed for equalities that seem obviously true.

**Example:** `phaseI.source = tetrahedron` where `phaseI` is a `def` whose
`.source` field is set to `tetrahedron`.

**Reason:** Lean's `rfl` only closes goals where both sides reduce to the
same term by unfolding definitions. If there are nested `def`s or the
reduction path is complex, `rfl` may not see the equality.

**Solution:** Use `simp [defName1, defName2, ...]` to unfold definitions,
then close with `rfl` or let `simp` close it.

**Prevention:** Reserve `rfl` for truly trivial definitional equalities
(simple field access on a concrete structure literal). For anything involving
nested definitions, use `simp` with the relevant definition names.

### 4.3 `sorry` introduces `sorryAx` — contaminates all downstream theorems

**Problem:** Any theorem that transitively depends on a `sorry` has
`sorryAx` in its axiom list, making it unverified.

**Detection:**
```lean
#print axioms my_theorem  -- will show sorryAx if contaminated
```

**Solution:** Either prove the theorem fully or remove it entirely.

**Prevention:** Never use `sorry` in any theorem that the main result
depends on. If something is too hard to prove, restructure so the main
theorem chain doesn't reference it. Use `sorry` only in isolated,
non-essential lemmas during development, and eliminate all of them
before declaring the project complete.

---

## 5. Tactic Pitfalls

### 5.1 `ring` cannot use hypotheses

**Problem:** After rewriting φ⁸ and ψ⁸, needed to use `φ + ψ = 1`
to finish. `ring` can't see hypotheses.

**Broken approach:**
```lean
rw [φ_pow8, ψ_pow8, φ_add_ψ]  -- φ_add_ψ rewrite fails in context
ring
```

**Working approach:**
```lean
rw [φ_pow8, ψ_pow8]
have h := φ_add_ψ
linarith
```

**Rule:** `ring` works on pure polynomial identities. If the goal requires
a hypothesis (like `φ + ψ = 1`), use `linarith`, `nlinarith`, or `linear_combination`
instead.

### 5.2 `field_simp` + `nlinarith` is the robust strategy for √ expressions

**Problem:** Various named lemmas for division/sqrt manipulation were
deprecated or renamed.

**Solution:** The combo `field_simp` then `nlinarith [sqrt5_sq]` handles
nearly all golden-ratio identities:
```lean
theorem φ_sq : φ ^ 2 = φ + 1 := by
  unfold φ
  have h5 : Real.sqrt 5 ^ 2 = 5 := sqrt5_sq
  field_simp
  nlinarith [h5]
```

**Prevention:** For any identity involving division or square roots,
default to `field_simp; nlinarith [relevant_sq_lemma]` rather than
manual rewrite chains with named lemmas.

### 5.3 `simp` sometimes closes the goal entirely — subsequent tactics error

**Problem:** `simp [...]` followed by `omega` gave "No goals to be solved."

**Example:**
```lean
-- BROKEN:
theorem foo : ¬ (24 ∣ 60) := by
  simp [FiniteRotationGroup3D.order]
  omega  -- ERROR: No goals to be solved

-- FIXED:
theorem foo : ¬ (24 ∣ 60) := by
  simp [FiniteRotationGroup3D.order]
```

**Prevention:** After writing a `simp` call, check if it fully closes the goal
before adding follow-up tactics. If unsure, add a `sorry` after and see if
Lean reports "no goals" or "unsolved goals."

### 5.4 `simp` with struct projections on generic instances: "no progress"

**Problem:** This pattern always fails:
```lean
-- BROKEN: d is a generic instance, fields could be anything
theorem foo (d : MyStruct) : d.field1 + d.field2 = 60 := by
  simp [MyStruct.field1, MyStruct.field2]  -- "simp made no progress"
```

**Reason:** `simp` with projection names can only simplify constructor
applications like `(MyStruct.mk 1 24).field1 → 1`. For a generic `d`,
it can't know what the field values are.

**Solution:** Don't universally quantify over struct instances when you
mean the default values:
```lean
-- FIXED: use concrete values
theorem foo : 1 + 24 + 20 + 15 = (60 : ℕ) := by norm_num
```

**Prevention:** NEVER write `theorem foo (x : MyStruct) : x.field ...`
unless the property truly holds for ALL instances. If you defined the
struct with specific default values and want to state a fact about those
defaults, use the concrete numbers directly.

This was the single most repeated bug in the project — it appeared in
FiniteGroups.lean, ForwardReturn.lean, Incommensurability.lean, and
Synthesis.lean. Catch it at definition time.

### 5.5 Flexible simp warning

**Problem:** `simp [foo] at hs` triggers linter warning about flexible
tactic modifying a hypothesis.

**Solution:** Use `simp only [specific_lemmas] at hs` instead. Lean
often suggests the exact replacement in the warning message.

**Prevention:** Prefer `simp only` over `simp` when modifying hypotheses.
Plain `simp` (without `only`) is fine for closing goals.

---

## 6. Proof Architecture Decisions

### 6.1 Prefer tactics over named lemmas for stability

Named lemmas (`div_add_eq_add_div`, `pow_lt_pow_right`, etc.) frequently
get renamed, removed, or have their signatures changed between Mathlib
versions. Tactics are far more stable:

| Instead of | Use |
|-----------|-----|
| Named rewrite lemmas | `field_simp`, `ring`, `norm_num` |
| Manual `rw` chains | `calc` blocks with `ring` steps |
| Specific monotonicity lemmas | `exact ... (by omega)` or `gcongr` |
| `Finset.max'` computation | Direct membership + upper bound |
| `List.maximum?` | Direct membership + `∀ n ∈ list, n ≤ max` |

### 6.2 Structure fields with defaults: don't universally quantify

If a structure has default field values and you want to prove something about
those defaults, state the theorem with concrete numbers, not universally
quantified over all instances.

### 6.3 Keep `sorry` out of the dependency chain

Structure your project so the main theorem never transitively depends on
any `sorry`. Use `#print axioms main_theorem` to verify. It's fine to have
`sorry` in isolated, auxiliary lemmas during development — but they must be
eliminated or disconnected before the final build.

### 6.4 Use `noncomputable section` for real-number definitions

Any `def` involving `Real.sqrt` or real-number division needs to be inside
a `noncomputable section` block:
```lean
noncomputable section
def φ : ℝ := (1 + Real.sqrt 5) / 2
-- ... all real-number definitions ...
end
```

### 6.5 Verify with `#print axioms`

At the end of your main file, add:
```lean
#print axioms main_theorem_name
```

Expected output for a clean proof:
```
'main_theorem_name' depends on axioms: [propext, Classical.choice, Quot.sound]
```

If `sorryAx` appears, trace back to find which dependency uses `sorry`.

---

## 7. Build & Workflow

### 7.1 Build times

- Full Mathlib build from source: 1-2+ hours
- Individual file with heavy Mathlib imports: 10-20 minutes
- File with only `Mathlib.Tactic` + light imports: 5-10 minutes
- Incremental rebuild after small change: only changed files + dependents

### 7.2 Codespace management

- Codespaces auto-sleep after ~30 min inactivity but persist for 30 days
- Terminal history is lost on disconnect; `build.log` persists on disk
- Access sleeping Codespaces at github.com/codespaces
- After reconnecting: `source ~/.elan/env` (or set up .bashrc per §1.2)

### 7.3 Iterative development strategy

Since builds are slow:
1. Write the full module structure first
2. Audit every proof for known pitfalls (this document) BEFORE building
3. Use `sorry` as placeholder during structural development
4. Replace all `sorry` with real proofs before final build
5. Capture output: `lake build 2>&1 | tee build.log`
6. Fix ALL errors in one pass — don't fix one and rebuild

### 7.4 Publishing

- Commit only: `.lean` sources, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`
- Do NOT commit: `.lake/`, `build/`, `.olean`/`.ilean` files
- `.gitignore` should contain: `.lake/` and `build/`
- GitHub drag-and-drop cannot upload hidden files (`.gitignore`, `.github/`)
  — create these via "Add file" → "Create new file" on GitHub web interface
- Add CI via `.github/workflows/lean.yml` for automatic verification badge

---

## 8. Quick Reference: Most Reliable Proof Strategies

| Goal type | Recommended tactic |
|-----------|-------------------|
| Arithmetic on naturals | `norm_num` or `omega` |
| Polynomial identity (no hypotheses) | `ring` |
| Identity with square roots | `field_simp; nlinarith [sqrt_sq_lemma]` |
| Linear consequence of hypotheses | `linarith` or `nlinarith` |
| Nonlinear with hypotheses | `nlinarith [h1, h2]` |
| Structure field equality | `simp [def1, def2, structureName]` |
| Finset membership | `simp [finsetName]` |
| Fin cases exhaustion | `fin_cases i <;> simp_all [defName]` |
| Inductive type cases | `cases x with \| constructor => tactic` |
| Decidable concrete computation | `decide` or `native_decide` |
| Power/exponent comparison | `exact pow_lt_pow_right₀ h_base_gt_one (by omega)` |

---

*Document created during formalization of "The Golden-Ratio Polyhedral Journey"
in Lean 4 v4.28.0-rc1 with Mathlib, February 2026.*
