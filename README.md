<p align="center">
  <img width="150" src="https://avatars.githubusercontent.com/u/275293734?s=200&v=4">
</p>

<h1 align="center">X Proofs</h1>

<p align="center">
  Lean 4 Models and Proofs for the Semantic Keywords in X.
</p>

## Getting started

Install [Elan](https://lean-lang.org/install/manual/) and add its `bin` directory to
PATH. Lake uses the compiler pinned in [`lean-toolchain`](lean-toolchain).

```sh
lake build
```

## Modules

| Keyword | Module | Contract |
| :--- | :--- | :--- |
| `pure` | [Pure](XProof/Pure.lean) | Observable-state preservation |
| `unique` | [Unique](XProof/Unique.lean) | Exclusive borrowing |
| `invariant` | [Invariant](XProof/Invariant.lean) | Checked construction and mutation |
| `static` | [Static](XProof/Static.lean) | Evaluation-preserving specialization |
| `memoise` | [Memoise](XProof/Memoise.lean) | Cache validity and result preservation |
| `become` | [Become](XProof/Become.lean) | Constant-depth tail transfer |
| `multi` | [Multi](XProof/Multi.lean) | Unique typed overload selection |
| `throws` | [Throws](XProof/Throws.lean) | Error propagation and handling |
| `parallel` | [Parallel](XProof/Parallel.lean) | Range coverage and state preservation |
| `layout` | [Layout](XProof/Layout.lean) | Logical AoS/SoA equivalence |
