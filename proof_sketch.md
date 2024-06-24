Our formalization of the proof of polynomial ABC (Mason-Stothers) and polynomial FLT mainly follows the Franz's note on Snyder's short proof.
The main ingredients of the proof are Wronskian and radical.
We work on field $k$ with no prior assumption on its characteristic.

## Preliminaries

First, Wronskian of two functions $a$ and $b$ are defined as follows. (See `Lib/Wronskian.lean`.)

> **Definition (Wronskian).** $W(a, b)=ab'-a'b$. Note that this is bilinear and antisymmetric.

We have the following lemma.

> **Lemma 1.** If $a+b+c=0$ then $W(a, b) = W(b, c) = W(c, a)$.

Quick check: $W(a, b) = W(a, a+b) = W(a, -c) = W(c, a)$.

For any nonzero $f \in k[X]$, $\text{rad} (f)$ is the multiplication of all the irreducible monic factors of $f$ with no multiplicity.
(See `Lib/Radical.lean`.)
The following lemma is the key step for the proof. (See `Lib/DivRadical.lean`.)

> **Lemma 2.** $f / \text{rad } f$ divides $f'$ for any nonzero $f$.

For this one should use UFDness of $k[X]$. Factor $f$ into multiplications of prime powers and count the power of primes to check (we use `UniqueFactorizationMonoid.induction_on_coprime` for this).
So note that $f / \text{rad }f$ divides both $f$ and $f'$. The corollary is this:

> **Lemma 3.** $a/\text{rad }a$ divides $W(a, b)$ for nonzero $a$.

We factor out a part of the main proof.

> **Lemma 4.** If $a, b \in k[X]$ are nonzero and coprime to each other, then $W = W(a, b)$ is zero if and only if $a'=b'=0$.

*Proof.* If $a'=b'=0$ then it is evident that $W = 0$.
We now assume $W = 0$ and show $a'=b'=0$.
As $W(a, b) = 0$ we have $ab' = a'b$. As $b$ divides $ab'$, it also divides $b'$.
Now if $b'$ is not zero, then the degree of $b'$ is strictly less than $b$ so we get a contradiction. So $b' = 0$. By a similar argument we also get $a' = 0$ with $W(a, b) = 0$. □

## Mason-Stothers theorem

At last, we have the following main theorem. (See `MasonStothers.lean`)

> **Theorem (Mason-Stothers, Polynomial ABC)** If $a, b, c \in k[X]$ are nonzero and $a + b + c = 0$ and they are coprime to each other, then either $\text{max}(\text{deg } a, \text{deg }b, \text{deg }c) + 1 \le \text{deg} (\text{rad } a b c)$ or all $a', b', c'$ are zero.

*Proof.* (of Snyder) We have $W = W(a, b) = W(b, c)$ by Lemma 1. And $a/\text{rad }a, b/\text{rad }b, c/\text{rad }c$ all divide $W$. Then, $a b c / \text{rad }(a b c)$ divides $W$ because $a/\text{rad }a, b/\text{rad }b, c/\text{rad }c$ are all coprime (informal note: This is the key step. $W$ is too good that it is divisible by all the factors, but has a small degree from its formula).

We divide the case into whether $W = 0$ or not. 
If $W = W(a, b) = W(b, c)$ is zero, then by Lemma 4 we have $a' = b' = c' = 0$.
So assume otherwise that $W \neq 0$.
As $W$ is nonzero, $W = W(a, b) = a b' - a' b$ has degree $< \text{deg }a + \text{deg }b$ (note that this requires case analysis on whether $a'=0$ or $b' = 0$ or not for an exact treatment). Now $\text{deg }\left( a b c / \text{rad }(a b c) \right) < \text{deg }a + \text{deg }b$. 
Arranging terms then gives $\text{deg }(a) + \text{deg }(b) + \text{deg }(c) < \text{deg }a+\text{deg }b + \text{deg }\left( \text{rad }(a b c) \right)$ or $\text{deg }(c) < \text{deg }\left( \text{rad }(a b c) \right)$. The argument is symmetric, so applying the argument by rotation shows the other inequalities $\text{deg }(a) < \text{deg }\left( \text{rad }(a b c) \right)$ and $\text{deg }(b) < \text{deg }\left( \text{rad }(a b c) \right)$. Taking the max gives the desired inequality $\text{max}(\text{deg } a, \text{deg }b, \text{deg }c) < \text{deg} (\text{rad } a b c)$. □

## Nonsolvability of Fermat-Catalan equation and FLT

<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
Using this, we can prove that Fermat-Catalan equation is not solvable in $k[X]$ (i.e. does not admit nonconstant solutions) under certain assumptions on exponents and the characteristic of $k$.
=======
> **Theorem (Polynomial FLT)** If $n \geq 3$, the characteristic of $k$ does not divide $n$ (this holds when characteristic is equal to zero), $a^n+b^n+c^n = 0$ in $k[X]$, and $a, b, c$ are nonzero all coprime to each other, then $a'=b'=c'=0$.
>>>>>>> 38cf49b (update readme & fix minor)


> **Corollary (Nonsolvability of Fermat-Catalan equation)** Let $k$ be a field and $p, q, r \geq 1$ be integers satisfying $1/p + 1/q + 1/r \leq 1$ and not divisible by the characteristic of $k$. Let $u, v, w$ be units in $k[X]$.
If $ua^p + vb^q + wc^r = 0$ for some nonzero polynomials $a, b, c \in k[X]$, then $a, b, c$ are all constant polynomials.


*Proof.* Applying Mason-Stothers to the triple $(ua^p, vb^q, wc^r)$ gives either one of the following.

*When inequality holds.* $\max(\mathrm{deg} (ua^p), \mathrm{deg}(vb^q), \mathrm{deg}(wc^r)) < \mathrm{deg} (\mathrm{rad} (uvw a^p b^q c^r))$. If we put $m = \max(\mathrm{deg} (a^p), \mathrm{deg}(b^q), \mathrm{deg}(c^r))$, then

$$
\begin{align*}
m &= \max(p \deg(a), q\deg(b), r\deg(c)) \\
&< \deg(\mathrm{rad}(a^p b^q c^r)) \\
& = \deg(\mathrm{rad}(abc)) \\
& \le \deg(abc) \\
& = \frac{1}{p} \deg(a^p) + \frac{1}{q} \deg(b^q) + \frac{1}{r} \deg(c^r) \\
& \le \left(\frac{1}{p} + \frac{1}{q} + \frac{1}{r}\right) m
\end{align*}
$$

and this gives a contradiction.

*When derivatives vanish.* In the other case of Mason-Stothers we get $(ua^p)' = (vb^q)' = (wc^r)' = 0$. As $(ua^p)' = u a' a^{p-1} = 0$ and $p$ is not zero in $k$, we have $a' = 0$. Similar arguments also give $b' = c' = 0$. If the characteristic of $k$ is zero, then $a' = 0$ is equivalent to $a$ being a constant, and same for $b$ and $c$. When $k$ has a positive characteristic $\ell > 0$, then we can use infinite descent argument to show that $a, b, c$ are constant polynomials. In fact, one can show that $a' = 0$ implies $a(X) = a_1(X^\ell)$ for some $a_1 \in k[X]$. Hence any nontrivial solution of Fermat's equation $u a^p + v b^q + w c^r = 0$ yields an another solution $u a_1^p + v b_1^q + w c_1^r = 0$ with smaller degree $\deg(a_1) = \deg(a) / \ell < \deg(a)$. □

FLT is just a special case of the above corollary when $p = q = r = n \geq 3$ and $u = v = 1, w = -1$.

> **Corollary (Polynomial FLT)** If $n \geq 3$, the characteristic of $k$ does not divide $n$ (this holds when characteristic is equal to zero), $a^n+b^n=c^n$ in $k[X]$, and $a, b, c$ are nonzero all coprime to each other, then $a, b, c$ are constant polynomials.



Note that we have a "counterexample" when $n$ is divisible by the characteristic of $k$: $(X - 1)^{p} + (1)^{p} = X^p$ for odd $p$ and the characteristic of $k$ is equal to $p$.

## Nonparametrizability of an elliptic curve $y^2 = x^3 + 1$

As an example of using non-solvability of Fermat-Catalan equation, we adopt the same strategy as in Franz's note to show that $y^2 = x^3 + 1$ is non-parametrizable.

> **Corollary** Let $k$ be a field of characteristic $\neq 2, 3$.
Then the elliptic curve defined by the Weierstrass equation $y^2 = x^3 + 1$ is not parametrizable by rational functions in $k(t)$. In other words, there does not exist $f(t), g(t) \in k(t)$ such that $g(t)^2 = f(t)^3 + 1$.

*Proof.*
Assume that a parametrization exists, so that $x = m / M$ and $y = n / N$ for some $m, n, M, N \in k[t]$ with $(m, M) = 1$ and $(n, N) = 1$.
Then by clearing denominators, we obtain $n ^ 2 M ^ 3 = (m ^ 3 + M ^ 3) N ^ 2$. 
From this one can show that $N^2$ and $M^3$ divide each other.
Using the unique factorization of $N^2 = M^3$, we can find $\alpha, \beta \in k^\times$ and $e \in k[t]$ such that $M = \alpha e^2$ and $N = \beta e^3$.
Now the equation reduces to $\beta^2 m^3 + \alpha^3 \beta^2 e^6 = \alpha^3 n^2$, which is a nontrivial solution for the Fermat-Catalan equation with $(p, q, r) = (3, 6, 2)$.
This is a contradiction as the characteristic of $k$ is not $2$ or $3$. □


## Davenport's theorem

> **Corollary (Davenport's theorem)** Let $k$ be a field (not necessarily has characteristic zero) and $f, g \in k[X]$ be coprime polynomials with nonzero deriviatives. Then we have $\deg (f) + 2 \le 2 \deg (f^3 - g^2)$.

*Proof.*
For given coprime non-constant polynomials $f, g \in k[X]$ with $f^3 - g^2 \ne 0$, apply apply Mason-Stothers to the zero-sum coprime triple $(-f^3, g^2, f^3 - g^2)$.
Then either we get the following inequality

$$
\begin{align*}
    \max \{3 \deg (f), 2 \deg (g) \} + 1 &=\max \{ \deg(-f^3), \deg(g^2), \deg(f^3 - g^2) \} + 1 \\
    &\leq \deg(\mathrm{rad}(-f^3 g^2 (f^3 - g^2))) \\
    &= \deg (\mathrm{rad} (fg(f^3 - g^2))) \\
    &\le \deg (f) + \deg(g) + \deg(f^3 - g^2).
\end{align*}
$$

where the first equality follows from $\deg(f^3 - g^2) \leq \max \{ \deg(f^3), \deg(g^2)\}$, or we get $(f^3)' = (g^2)' = (f^3 - g^2)' = 0$.
However, the latter case cannot happen since it would imply $3f^2f' = 0 = 2gg' \Rightarrow 3 = 0 = 2$, which is impossible in any field $k$.
This gives two inequalities

$$
\begin{align*}
    3 \deg(f) \leq \deg(f) + \deg(g) + \deg(f^3 - g^2) \\
    2 \deg(g) \leq \deg(f) + \deg(g) + \deg(f^3 - g^2) \\
\end{align*}
$$

and adding these two inequalities and rearranging gives the desired inequality.
It is worth nothing that we don't need the assumption $f^3 - g^2 \neq 0$ too, because this can be proven with coprimality assumption and $f' \neq 0$.
In fact, if $f^3 = g^2$, then both $f$ and $g$ should be unit, and this contradicts to $f' \neq 0$ since units in $k[t]$ are constants ($k[t]^\times = k^\times$). □
=======
> **Theorem (Polynomial FLT)** If $n \geq 3$, the characteristic of $k$ does not divide $n$ (this holds when characteristic is equal to zero), $a^n+b^n=c^n$ in $k[X]$, and $a, b, c$ are nonzero all coprime to each other, then $a'=b'=c'=0$.
=======
Using this, we can prove that Fermat-Catalan equation is not solvable in $k[X]$ (i.e. does not admit nonconstant solutions) under certain assumptions on exponents and the characteristic of $k$.
>>>>>>> fef38b0 (Update sketch for fermat-catalan & Davenport (#35))


<<<<<<< HEAD
Finally, note that for general field the derivative $a'$ of some $a \in k[X]$ being equal to zero is not equivalent to $a = 0$. If the characteristic is $p$ then the derivative of $X^p$ is $pX^{p-1} = 0$.
(In fact, we have a "counterexample" $(X - 1)^{p} + (1)^{p} = X^p$ for the polynomial FLT when $p$ is odd and the characteristic of $k$ is equal to $p$.)
However, if the characteristic of $k$ is zero then $a' = 0$ is equivalent to $a$ being a constant.
>>>>>>> 2ebd38b (Gitpod & update readme (#16))
=======
> **Corollary (Nonsolvability of Fermat-Catalan equation)** Let $k$ be a field and $p, q, r \geq 1$ be integers satisfying $1/p + 1/q + 1/r \leq 1$ and not divisible by the characteristic of $k$. Let $u, v, w$ be units in $k[X]$.
If $ua^p + vb^q + wc^r = 0$ for some nonzero polynomials $a, b, c \in k[X]$, then $a, b, c$ are all constant polynomials.


*Proof.* Applying Mason-Stothers to the triple $(ua^p, vb^q, wc^r)$ gives either one of the following.

*When $\max(\mathrm{deg} (ua^p), \mathrm{deg}(vb^q), \mathrm{deg}(wc^r)) < \mathrm{deg} (\mathrm{rad} (uvw a^p b^q c^r))$.* If we put $m = \max(\mathrm{deg} (a^p), \mathrm{deg}(b^q), \mathrm{deg}(c^r))$, then

$$
\begin{align*}
m &= \max(p \deg(a), q\deg(b), r\deg(c)) \\
&< \deg(\mathrm{rad}(a^p b^q c^r)) \\
& = \deg(\mathrm{rad}(abc)) \\
& \le \deg(abc) \\
& = \frac{1}{p} \deg(a^p) + \frac{1}{q} \deg(b^q) + \frac{1}{r} \deg(c^r) \\
& \le \left(\frac{1}{p} + \frac{1}{q} + \frac{1}{r}\right) m
\end{align*}
$$
and this gives a contradiction.

*When derivatives vanish.* In the other case of Mason-Stothers we get $(ua^p)' = (vb^q)' = (wc^r)' = 0$. As $(ua^p)' = u a' a^{p-1} = 0$ and $p$ is not zero in $k$, we have $a' = 0$. Similar arguments also give $b' = c' = 0$. If the characteristic of $k$ is zero, then $a' = 0$ is equivalent to $a$ being a constant, and same for $b$ and $c$. When $k$ has a positive characteristic $\ell > 0$, then we can use infinite descent argument to show that $a, b, c$ are constant polynomials. In fact, one can show that $a' = 0$ implies $a(X) = a_1(X^\ell)$ for some $a_1 \in k[X]$. Hence any nontrivial solution of Fermat's equation $ua^p + vb^q + wc^r = $ yields another solution $ua_1^p + vb_1^q + wc_1^r = 0$ with smaller degree $\deg(a_1) = \deg(a) / \ell < \deg(a)$. □

FLT is just a special case of the above corollary when $p = q = r = n \geq 3$ and $u = v = 1, w = -1$.

> **Corollary (Polynomial FLT)** If $n \geq 3$, the characteristic of $k$ does not divide $n$ (this holds when characteristic is equal to zero), $a^n+b^n=c^n$ in $k[X]$, and $a, b, c$ are nonzero all coprime to each other, then $a, b, c$ are constant polynomials.



Note that we have a "counterexample" when $n$ is divisible by the characteristic of $k$: $(X - 1)^{p} + (1)^{p} = X^p$ for odd $p$ and the characteristic of $k$ is equal to $p$.

## Davenport's theorem

> **Corollary (Davenport's theorem)** Let $k$ be a field (not necessarily has characteristic zero) and $f, g \in k[X]$ be coprime polynomials with nonzero deriviatives. Then we have $\deg (f) + 2 \le 2 \deg (f^3 - g^2)$.

*Proof.*
For given coprime non-constant polynomials $f, g \in k[X]$ with $f^3 - g^2 \ne 0$, apply apply Mason-Stothers to the zero-sum coprime triple $(-f^3, g^2, f^3 - g^2)$.
Then either we get the following inequality

$$
\begin{align*}
    \max \{3 \deg (f), 2 \deg (g) \} + 1 &=\max \{ \deg(-f^3), \deg(g^2), \deg(f^3 - g^2) \} + 1 \\
    &\leq \deg(\mathrm{rad}(-f^3 g^2 (f^3 - g^2))) \\
    &= \deg (\mathrm{rad} (fg(f^3 - g^2))) \\
    &\le \deg (f) + \deg(g) + \deg(f^3 - g^2).
\end{align*}
$$

where the first equality follows from $\deg(f^3 - g^2) \leq \max \{ \deg(f^3), \deg(g^2)\}$, or we get $(f^3)' = (g^2)' = (f^3 - g^2)' = 0$.
However, the latter case cannot happen since it would imply $3f^2f' = 0 = 2gg' \Rightarrow 3 = 0 = 2$, which is impossible in any field $k$.
This gives two inequalities

$$
\begin{align*}
    3 \deg(f) \leq \deg(f) + \deg(g) + \deg(f^3 - g^2) \\
    2 \deg(g) \leq \deg(f) + \deg(g) + \deg(f^3 - g^2) \\
\end{align*}
$$

and adding these two inequalities and rearranging gives the desired inequality.
It is worth nothing that we don't need the assumption $f^3 - g^2 \neq 0$ too, because this can be proven with coprimality assumption and $f' \neq 0$.
In fact, if $f^3 = g^2$, then both $f$ and $g$ should be unit, and this contradicts to $f' \neq 0$ since units in $k[t]$ are constants ($k[t]^\times = k^\times$). □
>>>>>>> fef38b0 (Update sketch for fermat-catalan & Davenport (#35))
