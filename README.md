# Formalization of Polynomial ABC and FLT

- Jineon Baek (University of Michigan, Ann Arbor -- jineon@umich.edu)
- Seewoo Lee (University of California, Berkeley -- seewoo5@berkeley.edu)

This is a formalization of the proof of ABC theorem on polynomials (Mason-Stothers Theorem) and their corollaries (nonsolvability of Fermat-Catalan equation and FLT for polynomials, Davenport's theorem) in Lean 3.
More precisely, we formalized the proofs of the following theorems:

> **Theorem (Mason-Stothers, Polynomial ABC)** Let $k$ be a field. If $a, b, c \in k[X]$ are nonzero and $a + b + c = 0$ and they are coprime to each other, then either $\text{max}(\text{deg } a, \text{deg }b, \text{deg }c) < \text{deg} (\text{rad } a b c)$ or all $a', b', c'$ are zero.

> **Corollary (Nonsolvability of Fermat-Catalan equation)** Let $k$ be a field and $p, q, r \geq 1$ be integers satisfying $1/p + 1/q + 1/r \leq 1$ and not divisible by the characteristic of $k$. Let $u, v, w$ be units in $k[X]$.
If $ua^p + vb^q + wc^r = 0$ for some nonzero polynomials $a, b, c \in k[X]$, then $a, b, c$ are all constant polynomials.

> **Corollary (Polynomial FLT)** If $n \geq 3$, the characteristic of $k$ does not divide $n$ (this holds when characteristic is equal to zero), $a^n+b^n=c^n$ in $k[X]$, and $a, b, c$ are nonzero all coprime to each other, then $a, b, c$ are constant polynomials.

> **Corollary** Let $k$ be a field of characteristic $\neq 2, 3$.
Then the elliptic curve defined by the Weierstrass equation $y^2 = x^3 + 1$ is not parametrizable by rational functions in $k(t)$. In other words, there does not exist $f(t), g(t) \in k(t)$ such that $g(t)^2 = f(t)^3 + 1$.

> **Corollary (Davenport's theorem)** Let $k$ be a field (not necessarily has characteristic zero) and $f, g \in k[X]$ be coprime polynomials with nonzero deriviatives. Then we have $\deg (f) + 2 \le 2 \deg (f^3 - g^2)$.

The proof is based on the [online note] by Franz Lemmermeyer, which is a slight variation of Noah Snyder's proof (*An Alternate Proof of Mason's Theorem*, Elem. Math. 55 (2000) 93--94).
See `proof_sketch.md` for details.

## Installation

After you install Lean 3 properly (see [here](https://leanprover-community.github.io/get_started.html) for details), run the following script:

```sh
leanproject get seewoo5/lean-poly-abc
```

This script will clone this repository along with mathlib codes.

## Gitpod

Using [Gitpod](https://www.gitpod.io/), you can compile the codes on your browser. Sign up to Gitpod and use the following URL:

```
gitpod.io/#https://github.com/seewoo5/lean-poly-abc
```

## Acknowledgement

Thanks to Kevin Buzzard ([@kbuzzard](https://github.com/kbuzzard)) for recommending this project, and also Thomas Browning ([@tb65536](https://github.com/tb65536)) for helping us to get start with and answer many questions.

[online note]: http://www.fen.bilkent.edu.tr/~franz/ag05/ag-02.pdf
