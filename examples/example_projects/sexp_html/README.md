# sexp_html

A counter app, written in a language of its own: HTML as s-expressions,
for apps whose state the language holds, and proves things about.

```
counter := app count
  (html
    (head (title "Counter"))
    (body
      (div (attrs (class "counter"))
        (h1 "Count: " count)
        (button (attrs (on click Increment)) "+1")))).
```

```
main.soma            renders the counter, before any click and after three
pages/
  pages.lang         the rules of pages/: the language (sexp, app), and the state
  pages.proof        about the state of every app of pages/: it only increases
  counter.soma       the counter, in the language
  counter.proof      the counter's state, by the theorems of pages.proof
```

`soma build -v main.soma` prints the page at `Count: 0`, the state after
three clicks (`3`), and the page at `Count: 3`.

## The state

The state of every app of this language is in `pages.lang`, and only
there: a count, from 0, and one action, `Increment`, which adds 1. It is
global, and functional: an app is its initial state, the function from an
action and a state to the next state (`step`), and the view of a state.
Clicks are replayed: `state_after counter clicks` is the state after
`clicks`, from the start.

A page gives only the view. `app count (div ...)` is the app whose state
is the language's, and whose view is `(div ...)`, `count` being the state
where it is shown. So a page cannot add a button that does anything but
+1: there is no other action.

`pages.proof` is checked once, with the rules of `pages/`, and is about
every app made with `app`, whatever its view:

- `state_is_clicks`: the state is the number of clicks;
- `click_increases`: each click adds one;
- `strictly_increasing`: the state after a click is greater than before it.

`counter.proof` applies them to the counter (`counter_increases`). Were
`step` to subtract on some action, or a second action to do nothing,
`pages.proof` would no longer check, and no page under `pages/` would
build.

What it does not cover: an app put together by hand. `pages.lang` exports
JSX, whose `make_app` makes an app with any update; one made with it is
not an app of the language, and the theorems say nothing about it.

## The language

`sexp` takes one s-expression, and `app` a name and one s-expression.
Soma already reads them: `(div (h1 "Hello world"))` is `div` applied to
`h1 "Hello world"`. The macros receive it as a tree and build the JSX
element:

| Written | Is |
| --- | --- |
| `(div child ...)` | the element `div`: a lowercase name is a tag |
| `"text"`, `42` | text |
| `count` | its value: an element, a string, or a number (its digits) |
| `(attrs (class "page") (on click Increment))` | the attributes and events, among the children |
| `data_id` | the attribute `data-id`: names have no dashes |
| `(Greeting "Soma")` | a call of the component `Greeting`: uppercase, as in JSX |
| `(br _)` | an element without children; `(br)` is the name `br` |

Attribute names cannot be `for`, `in`, `with` or `as`, which Soma keeps
for itself. JSX notation cannot write `data-id` at all; here it is
`data_id`.

Mistakes are reported where the page has them: `(attrs class)` gives
`an attribute is (name value), or (on event action)`, and `(br)` gives
`(br) is the name br; an element without children is written (br _)`.

## Where it applies

`pages/pages.lang` is the rules of the folder `pages/`, so every file under
`pages/` has the language, and nothing else does. `main.soma` is outside
`pages/`: it imports `pages.pages` itself, for `Increment` and `render`.
The rules export `JSX`, so the pages have `element`, `render` and JSX
notation without importing anything.

The macros are ordinary Soma code in `pages.lang`: functions on `syntax`
(`Var`, `Str`, `App`, `Lam`, ...) that build the code of the element.
Changing the language is changing those functions.
