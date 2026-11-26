# Checked shared native data

A `.definition` can stage a pure, checked Source recipe as one shared native
constant:

```soma
OCaml Native Static Data choices : list (string * console) :=
  console_occurrence With [raw_console; screen_console; quiet_console].
```

Here `console_occurrence` is a transparent ordinary `.soma` definition, for
example a generic function returning three string/input pairs. Its leading
type parameters are inferred from the checked input and declared result
types. `With` supplies symbolic unit-getter inputs; omit it for a closed
recipe. The directive declares a native callback from unit to the result.
It does not run those getters or any native evaluator while checking.

Reduction uses the kernel's pure reduction machinery. Supported data are
strings (including all byte values), ASCII characters, native machine words,
representable naturals, finite primitive floats, booleans, unit, pairs,
lists and options. Inputs may be declared nullary variant constructors,
constructors with a closed unit payload, float constants or previously checked
static data. Recipes may build containers around these typed symbolic inputs.
Native reads, arbitrary external values, dependent runtime results, effects,
forged native handles, missing/extra inputs and domain/result mismatches are
rejected. This adds no logical assumption or unchecked evaluator.

The backend emits `soma_data_<owner-hash>.ml` modules containing complete
literal definitions. Named references preserve reuse of static data, boxed
constructor inputs and float inputs. One generated module per constant avoids
extra captured environments in native and bytecode callbacks, and allows
static invocation, value reexports and lexical functor scopes to refer to the
same data. Constants retain inferred principal types; they do not acquire a
caller's abstract type or a monomorphic annotation that prevents generic
function/contravariant-row instantiations. Ordinary constructor getters retain
their existing behavior; staging a unit-payload constructor creates a shared
atom for the staged data, not a runtime call to that constructor.

`native_static_data.manifest` starts with `soma-native-static-data-v1`. Each
quoted row contains the checked owner symbol, Source path/hash and product
filename/hash. Primitive shared atoms record their parent static-data
Source witness. Receipts cover these complete bytes. The recipe and input
references are recorded as checked logical dependencies; their validated data
and references participate in semantic and ABI fingerprints. Existing operation
tags are unchanged, and projects without this directive retain their former
products and fingerprints. Obsolete producer-owned constants and manifests are
removed only while their recorded bytes still match; caller edits survive.

`test-suite/misc/soma_native_static_data.sh` checks typed reduction and invalid
inputs, all 256 string bytes, signed word boundaries, option/list/pair data,
shared float/boxed inputs, generic functions and contravariant variant types,
abstract lexical functors and standalone reexports. Native and bytecode checks
retain the exact original owners, payloads, promises, caller context,
exceptions, cancellation, natural Weak release phases and exact allocation for
reads, factory creation and calls. It also checks Source/product provenance,
fingerprint sensitivity and stale-file cleanup. Existing static-invocation
and lexical-scope regression suites remain separate.
