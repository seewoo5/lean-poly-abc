Our formalization of the proof of polynomial ABC (Mason-Stothers) and polynomial FLT mainly follows the Franz's note on Snyder's short proof.
The main ingredients of the proof are Wronskian and radical.
We work on field $k$ with no prior assumption on its characteristic.

## Preliminaries

First, Wronskian of two functions $a$ and $b$ are defined as follows. (See `wronskian.lean`.)

> **Definition (Wronskian).** $W(a, b)=ab'-a'b$. Note that this is bilinear and antisymmetric.

We have the following lemma.

> **Lemma 1.** If $a+b+c=0$ then $W(a, b) = W(b, c) = W(c, a)$.

Quick check: $W(a, b) = W(a, a+b) = W(a, -c) = W(c, a)$.

For any nonzero $f \in k[X]$, $\text{rad} (f)$ is the multiplication of all the irreducible monic factors of $f$ with no multiplicity.
(See `radical.lean`.)
The following lemma is the key step for the proof. (See `div_radical.lean`.)

> **Lemma 2.** $f / \text{rad } f$ divides $f'$ for any nonzero $f$.

For this one should use UFDness of $k[X]$. Factor $f$ into multiplications of prime powers and count the power of primes to check (we use `unique_factorization_domain.induction_on_coprime` for this).
So note that $f / \text{rad }f$ divides both $f$ and $f'$. The corollary is this:

> **Lemma 3.** $a/\text{rad }a$ divides $W(a, b)$ for nonzero $a$.

We factor out a part of the main proof.

> **Lemma 4.** If $a, b \in k[X]$ are nonzero and coprime to each other, then $W = W(a, b)$ is zero if and only if $a'=b'=0$.

*Proof.* If $a'=b'=0$ then it is evident that $W = 0$.
We now assume $W = 0$ and show $a'=b'=0$.
As $W(a, b) = 0$ we have $ab' = a'b$. As $b$ divides $ab'$, it also divides $b'$.
Now if $b'$ is not zero, then the degree of $b'$ is strictly less than $b$ so we get a contradiction. So $b' = 0$. By a similar argument we also get $a' = 0$ with $W(a, b) = 0$. □

## Mason-Stothers theorem

At last, we have the following main theorem. (See `mason_stothers.lean`)

> **Theorem (Mason-Stothers, Polynomial ABC)** If $a, b, c \in k[X]$ are nonzero and $a + b + c = 0$ and they are coprime to each other, then either $\text{max}(\text{deg } a, \text{deg }b, \text{deg }c) < \text{deg} (\text{rad } a b c)$ or all $a', b', c'$ are zero.

*Proof.* (of Snyder) We have $W = W(a, b) = W(b, c)$ by Lemma 1. And $a/\text{rad }a, b/\text{rad }b, c/\text{rad }c$ all divide $W$. Then, $a b c / \text{rad }(a b c)$ divides $W$ because $a/\text{rad }a, b/\text{rad }b, c/\text{rad }c$ are all coprime (informal note: This is the key step. $W$ is too good that it is divisible by all the factors, but has a small degree from its formula).

We divide the case into whether $W = 0$ or not. 
If $W = W(a, b) = W(b, c)$ is zero, then by Lemma 4 we have $a' = b' = c' = 0$.
So assume otherwise that $W \neq 0$.
As $W$ is nonzero, $W = W(a, b) = a b' - a' b$ has degree $< \text{deg }a + \text{deg }b$ (note that this requires case analysis on whether $a'=0$ or $b' = 0$ or not for an exact treatment). Now $\text{deg }\left( a b c / \text{rad }(a b c) \right) < \text{deg }a + \text{deg }b$. 
Arranging terms then gives $\text{deg }(a) + \text{deg }(b) + \text{deg }(c) < \text{deg }a+\text{deg }b + \text{deg }\left( \text{rad }(a b c) \right)$ or $\text{deg }(c) < \text{deg }\left( \text{rad }(a b c) \right)$. The argument is symmetric, so applying the argument by rotation shows the other inequalities $\text{deg }(a) < \text{deg }\left( \text{rad }(a b c) \right)$ and $\text{deg }(b) < \text{deg }\left( \text{rad }(a b c) \right)$. Taking the max gives the desired inequality $\text{max}(\text{deg } a, \text{deg }b, \text{deg }c) < \text{deg} (\text{rad } a b c)$. □

## Nonsolvability of Fermat-Catalan equation and FLT

Using this, we can prove the following version of FLT for polynomials.

> **Theorem (Polynomial FLT)** If $n \geq 3$, the characteristic of $k$ does not divide $n$ (this holds when characteristic is equal to zero), $a^n+b^n=c^n$ in $k[X]$, and $a, b, c$ are nonzero all coprime to each other, then $a, b, c$ are constants polynomials.

*Proof.* Applying Mason-Stothers to the triple $(a^n, b^n, -c^n)$ gives either one of the following.
- $\text{max}(\text{deg } a^n, \text{deg }b^n, \text{deg }c^n) < \text{deg} (\text{rad } a^n b^n c^n)$, so $n \max(\deg a, \deg b, \deg c) < \deg(\text{rad }a b c)$. But in this case then the following holds.
$\deg(\text{rad }a b c) = \deg(\text{rad }a) + \deg(\text{rad } b) + \deg(\text{rad } c)$
$\leq \deg(a) + \deg(b) + \deg(c) \leq 3 \max (\deg a, \deg b, \deg c)$. This is only possible when all degrees of $a, b, c$ are equal to zero. That is, $a, b, c$ are constants.
- In the other case of Mason-Stothers we get $(a^n)' = (b^n)' = (c^n)' = 0$. As $(a^n)' = n a' a^{n-1} = 0$ and $n$ is not zero in $k$, we have $a' = 0$. Similar arguments also give $b' = c' = 0$. If the characteristic of $k$ is zero, then $a' = 0$ is equivalent to $a$ being a constant, and same for $b$ and $c$. When $k$ has a positive characteristic $\ell > 0$, then we can use infinite descent argument to show that $a, b, c$ are constant polynomials. In fact, one can show that $a' = 0$ implies $a(X) = a_1(X^\ell)$ for some $a_1 \in k[X]$. Hence any nontrivial solution of Fermat's equation $a^n + b^n = c^n$ yields another solution $a_1^n + b_1^n = c_1^n$ with smaller degree $\deg(a_1) = \deg(a) / \ell < \deg(a)$. □


Note that we have a "counterexample" when $n$ is divisible by the characteristic of $k$: $(X - 1)^{p} + (1)^{p} = X^p$ for odd $p$ and the characteristic of $k$ is equal to $p$.
