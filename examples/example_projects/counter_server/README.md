# counter_server

The +1 counter of `sexp_html`, served over HTTP by a unikernel. Each
request starts the counter at the count in the address (`/?count=41`), or
else in the cookie `count`, or else at 0. A count is accepted only when it
is a whole number, 0 or more, which is proved; so is that the counter's
state, from whatever start was accepted, strictly increases.

```
main.soma            main: serve 8080 answer, a MirageOS image (main.hvt)
pages/
  pages.lang         the rules of pages/: the language, and the state
  pages.proof        the state, from any start, strictly increases
  counter.soma       the counter, in the language
web/
  request.soma       where a page starts: address, cookie, or 0
  request.proof      only whole numbers, 0 or more, are accepted
  server.soma        the response to each request
  server.proof       what is served: the state increases, the +1 link is accepted
```

## Running it

```
soma run examples/example_projects/counter_server/main.soma
```

builds the image and runs it under `solo5-vmnet`, which gives it an
address on the Mac's vmnet network; it prints the address
(`Lease obtained! IP: 192.168.105.185`), then
`serving the counter on port 8080`. Then:

| Asked for | Answer |
| --- | --- |
| `http://ADDRESS:8080/` | the page at 0, or at the cookie's count |
| `http://ADDRESS:8080/?count=41` | the page at 41; the cookie is set to 41 |
| clicking `+1` on it | `/?count=42`, the page at 42 |
| `/?count=-1`, `?count=1.5`, `?count=abc`, `?count=007`, `?count=` | `400 Bad Request`, saying what a count is |
| a cookie `count=x` | `400`, and the cookie is cleared |
| any other address | `404 Not Found` |

The address comes before the cookie. A count in the address that is not
accepted leaves the cookie as it was. `dev/mirage-check.sh` runs these
requests against the image (`counter-server`).

## What is proved

**Only whole numbers, 0 or more** (`web/request.proof`). The count is an
`N`, which has no negative numbers, and the parser accepts a string only
when it is exactly how Soma writes some `N`:

- `accepted_is_written`: whatever is accepted, `s`, is `to_string n` for
  the `n` it is accepted as. So no sign, no point, no letter, no leading
  zero, nothing empty;
- `no_negative`: nothing that starts with `-` is accepted;
- `written_is_accepted`: every count the server writes, in its links and
  its cookie, is accepted, as itself;
- `nothing_found_starts_at_zero`, `started_count_was_written`,
  `rejected_is_not_accepted`: where the start comes from, and that a
  count is rejected only when it is not accepted.

**The state strictly increases** (`pages/pages.proof`, as in
`sexp_html`, now from any start): the only action is +1, so the state
after some clicks is the start and one more for each, and each click
increases it. `web/server.proof` puts the two together:
`served_state_increases` holds for the start of any request that is
accepted, and `next_count_is_accepted`: the +1 link of the page at `n`
carries `n + 1`, which is greater, and which the server accepts.

The count is binary, an `N`, and not a `nat`: a `nat` is unary in the
image, so a request for `?count=99999999999999999999` would take that
much memory. As an `N`, it is 67 bits.

## How a click reaches the server

The page is HTML from the server, without scripts: `(increment "+1")`,
the language's only control, is a link to the page at the next count,
`/?count=N+1`. It also carries the event `Increment`, so that the app, as
the proofs see it, is the same as the page.

What the proofs do not cover: a page under `pages/` may link to any
address, `/?count=0` among them; that is a new start, not an action of
the app. And, as in `sexp_html`, an app put together by hand with JSX's
`make_app` is not an app of the language.
