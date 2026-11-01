# upgrade_check

An app, and an upgrade of the library it depends on. The new version announces
"internal cleanup, no change in behaviour". The app builds against it and all
its proofs check, so nothing you would normally run says otherwise. `soma diff`
does.

```
soma build -v main.soma               the invoice, from pricing 1.0: 5400
soma diff pricing-1.0 pricing-1.1     what the upgrade is
```

```
soma.toml      the project, and which pricing it depends on
soma.lock      the version of it, written by soma
main.soma      an invoice
main.proof     nothing_lost: no money is lost to rounding, from pricing's discount_le
pricing-1.0/   the library
pricing-1.1/   the same library, "cleaned up"
```

## What the report says

```
pricing-1.0 -> pricing-1.1

The same, and resting on more (what uses it still builds):
  rates.discount_le, now assumes rates.discount_small

Edited:
  totals.shipping

Changed by what they use:
  totals.invoice

Another proof, or one beneath it, of the same statement:
  totals.subtotal_app

Added:
  rates.discount_small

3 unchanged. Notations, instances, hints and tactics are not compared.
```

Each line is one of the things that were done in this release:

- **`rates.soma` was reformatted, with comments added.** It is not in the report.
  `discount` and `discounted` are among the 3 unchanged.
- **`subtotal_app` got another proof.** The statement is the same, so what uses
  it is not affected.
- **`shipping` changed.** Free shipping went from 50.00 to 100.00, so this cart
  now costs 5.00 more. `invoice` did not change, and what it does did, which is
  why it is listed apart.
- **`discount_le` kept its statement, and lost its proof.** It rests now on
  `discount_small`, an axiom added "to keep the build fast". This is the one to
  stop at. The axiom is false: a discount of 200% is more than the price. From
  it, anything follows.

## Try it: everything still passes

Change `soma.toml` to `{ path = "pricing-1.1" }` and build:

```
soma build -v main.soma         builds, and main.proof checks: 5900
soma hash main.soma             main.nothing_lost now assumes pricing.rates.discount_small
```

`nothing_lost`, this project's own theorem, has not changed by a character, and
it now rests on a false axiom. `soma explore` lists that axiom too, once you are
on the new version. `soma diff` says which release brought it, before you take it.

## With a published library

The two sides are usually tags:

```
soma diff owner/pricing@1.0.0 owner/pricing@1.1.0
```

Each is fetched and compiled as a dependency, so it is checked and not run. Your
project and its `soma.lock` are not touched.

## What it does not see

Notations, instances, hints and tactics are not in the terms the kernel checks,
so a changed notation is not reported, though it can change what a file that
uses it means. Nor is what an OCaml library does: a `.ml` file's source is
compared, and an opam package's version is not.

It reports and does not judge. An edited definition may be why you are upgrading.
