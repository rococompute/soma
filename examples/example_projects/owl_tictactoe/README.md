# Owl tic-tac-toe

A minimal neural-network example using the optional
[soma-owl](https://github.com/rococompute/soma-owl) package over HTTPS.
If access is restricted, authenticate GitHub first (`gh auth login` and
`gh auth setup-git`) before running this example. Owl's native dependencies
are additional requirements; the pure Soma examples do not need them.

```sh
cd examples/example_projects/owl_tictactoe
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
soma run main.soma
./test.sh
```

The first build resolves `v0.1.0` of `https://github.com/rococompute/soma-owl.git`,
records its commit in `soma.lock`, checks the package's Soma code, and links
its OCaml adapter against Owl 1.2. Subsequent builds use the locked commit.
Soma uses Git's configured credential helper. Configure authentication before
building if needed, since dependency fetches do not prompt for credentials.

Owl needs system BLAS/LAPACKE libraries. On Debian/Ubuntu install
`libopenblas-dev liblapacke-dev`; on Homebrew install `openblas llvm libomp`.
For this machine's Homebrew OpenMP setup, run
`~/Development/soma-owl/scripts/install-owl.sh` once. `SOMA_OCAML_SWITCH`
selects the program switch; the default is `~/.cache/soma/ocaml`.
The test uses one OpenBLAS/OpenMP thread for this small workload.

## What runs

- `game.soma`: legal moves, wins, eight board symmetries, and a minimax
  teacher. `game.exp` checks basic rules without calling Owl.
- `policy.soma`: player-relative board encoding, teacher targets, and a
  legal-move mask over the network's nine output scores.
- `main.soma`: trains a 9-input, 32-hidden-unit tanh, 9-output softmax
  classifier for 8,000 full-batch steps, then prints its loss, two tactical
  predictions, and a self-play game.
- `soma_owl.nn.mlp`: reusable forward propagation and gradient descent,
  written in Soma. `soma_owl.matrix` supplies the Owl-backed operations.

Cells are numbered 0–8 in row-major order. Features are 0 for an empty
cell, 1 for the player to move, and -1 for the opponent. The 80 training
positions are ten seed boards, each rotated and reflected. Minimax gives
all optimal moves equal target probability. During prediction, only the
trained network supplies scores; the game masks occupied cells and takes
the highest remaining score.

With seed 17, the example produced:

```text
Cross-entropy: 2.253772 -> 0.935412
Winning move (expected 2): 2
Blocking move (expected 2): 2
PASS training improves loss and learns the two tactical examples
```

The nonzero loss partly reflects targets shared across several equally
good moves. This small training set demonstrates integration and learning;
the policy is not guaranteed to play optimally on unseen boards. Owl's
floating-point operations are opaque to the proof checker. The pure game
proofs do not certify the learned policy or the foreign numerical code.
