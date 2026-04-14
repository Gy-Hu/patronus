# Patronus


[![Crates.io Version](https://img.shields.io/crates/v/patronus)](https://crates.io/crates/patronus)
[![docs.rs](https://img.shields.io/docsrs/patronus)](https://docs.rs/patronus)
[![GitHub License](https://img.shields.io/github/license/ekiwi/patronus)](LICENSE)


### BTOR2 cone-of-influence reduction

Patronus can parse a BTOR2 file, compute the cone of influence (COI) of the
properties, and write out a reduced BTOR2 file that is semantically equivalent
for all observable behaviour. The `coi_demo` example wraps the full flow:

```bash
cargo run --example coi_demo -p patronus -- \
    inputs/repair/sha3_keccak.w2.replace_variables.btor \
    /tmp/full.btor       \
    /tmp/reduced.btor
# full   : 18 inputs, 173 states, 0 bads, 0 constraints, 3 outputs
# reduced: 18 inputs,  69 states, 0 bads, 0 constraints, 3 outputs
```

The reduced file stays valid BTOR2, and by default the primary-input interface
is preserved (unused inputs are left dangling) so equivalence-checking tools
can line the two circuits up.

#### Verifying the reduction with ABC

`btor2aiger` only promotes `bad` / `constraint` lines into AIGER outputs, so
`coi_demo` automatically promotes every `output` to a per-bit `bad` before
reducing. Then:

```bash
btor2aiger /tmp/full.btor    > full.aig
btor2aiger /tmp/reduced.btor > reduced.aig
abc -c "dsec full.aig reduced.aig"
# Networks are equivalent.  Time = 0.20 sec
```

Use `dsec` for sequential circuits (different latch counts are allowed —
ABC finds the register correspondence). Use `cec` only when both sides have
the same number of latches, e.g. for validating a parse → serialize round
trip rather than a state-reducing transform.

#### Comparing patronus's COI against pono's

`coi_demo` exposes three env-var knobs for apples-to-apples comparison with
[pono](https://github.com/upscale-project/pono)'s `StaticConeOfInfluence`:

| env var | effect |
|---|---|
| `COI_SINGLE_PROP=N` | Root the cone on `bads[N]` plus all constraints, mirroring `pono --static-coi --prop N`. Default is the union of every bad, constraint, and output. |
| `COI_DUMP_NAMES=1` | Print the kept state names and in-cone input names on stderr, ready to diff against pono's `--verbosity 3` `found COI statevar/inputvar` lines. |
| `COI_NO_WRITE=1` | Skip BTOR2 serialization. Useful under `COI_SINGLE_PROP`, where the leftover bads/outputs reference symbols outside the trimmed cone and would panic the writer. |

Quick sanity run on Quiz1:

```bash
COI_DUMP_NAMES=1 cargo run --example coi_demo -p patronus -- \
    inputs/chiseltest/Quiz1.btor /tmp/full.btor /tmp/red.btor
# COI statevars (kept): _resetCount, counter
# COI inputvars (in cone): reset
pono --static-coi --verbosity 3 --engine bmc --bound 0 \
    inputs/chiseltest/Quiz1.btor 2>&1 | grep 'found COI'
# state4 (counter), state6 (_resetCount), input2 (reset)
```

Both tools converge on the same three symbols. On larger inputs the counts
may differ by a handful because patronus follows `state.init` edges into the
cone directly, whereas pono excludes init-only symbols from the cone and
re-adds them via a separate pass — the final set of retained symbols is the
same.


### TODO

Some things we will hopefully get to one day.

- simulator
  - JIT based implementation
  - better debugging, add option to print expressions with trace
  - waveform generation
  - quickly update only parts of the circuit


#### API Changes

- `patronus::btor2::parse_file` should take in a `Context` instead of producing one
- `Context` should use `RefCell` to allow expressions to be built with a immutable reference