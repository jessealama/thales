# disagree-spurious (placeholder)

Intended to catch thales regressions that report a TS#### diagnostic not produced
by tsc. No such divergence exists today for the tiny subset we cover, so
`expected-outcome.txt` currently says `pass:accept`. The fixture exists as
a slot: when the first real spurious thales error surfaces, replace the `input.ts`
with that case and change `expected-outcome.txt` to `fail:spurious`.
