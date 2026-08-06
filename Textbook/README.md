# The Lait Book

An [mdbook](https://rust-lang.github.io/mdBook/) whose ` ```lean ` blocks are
elaborated by the Lean language server through
[leandown](https://github.com/mzhang28/leandown), so code in the book gets real
highlighting, hover types, go-to-definition links and diagnostics.

## Prerequisites

- `mdbook`, `bun`, `npm`, and a Lean toolchain (`lake`) on `PATH`.
- A leandown checkout at `../../leandown` (i.e. next to this repo's directory).
  `package.json` depends on it with `file:` paths, so `npm install` links
  `packages/mdbook` and `packages/core` into `node_modules` and the preprocessor
  runs the development sources directly — edits there take effect on the next
  book build, with no rebuild of leandown needed. Running the TypeScript sources
  is why the preprocessor is invoked via `bun`: in the unpublished workspace,
  `@leandown/core`'s exports point at `src/*.ts`.

## Building

```bash
npm install                 # links the leandown checkout into node_modules
(cd .. && lake build Lait)  # imports resolve against build artifacts, so build first
npm run build               # == npm run assets && mdbook build
npm run serve               # same, with mdbook's live reload
```

`npm run assets` regenerates `leandown.js` and `leandown.css` (the browser
runtime and stylesheet, both gitignored) from the linked checkout;
`leandown-overrides.css` on top of them is ours and is checked in.

Code blocks are elaborated inside the Lait Lean project at the repo root
(`lean-project-path = ".."` in `book.toml`), which is what lets a block say
`import Lait`. Blocks accumulate within a chapter but not across chapters, and
Lean requires imports first, so **each page's first ` ```lean ` block must start
with `import Lait`**.

Only ` ```lean ` blocks are processed; plain ` ``` ` blocks are passed through to
mdbook's static highlighter untouched.
