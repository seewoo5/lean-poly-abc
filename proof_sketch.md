We work on field $k$ with no prior assumption on its characteristic. For any nonzero $f \in k[X]$, $\text{rad} (f)$ is the multiplication of all the irreducible factors of $f$ with no multiplicity. Note that $\text{rad}(f)$ is defined up to associativity (unit multiplication). Another pain point is that we don't talk about $\text{deg }f$ when $f$ is zero.

> __Theorem [mason].__ If $a, b, c \in k[X]$ are nonzero and $a + b + c = 0$ and they are coprime to each other (note: a, b being coprime implies all the others), then either $\text{max}(\text{deg } a, \text{deg }b, \text{deg }c) < \text{deg} (\text{rad } a b c)$ or all $a', b', c'$ are zero.  ^thm-mason

> __Definition [wronskian].__ $W(a, b)=ab'-a'b$. Note that this is bilinear and antisymmetric. ^def-wronskian

> __Lemma [wronskian-eq].__ If $a+b+c=0$ then $W(a, b) = W(b, c) = W(c, a)$. ^lem-wronskian-eq

Quick check: $W(a, b) = W(a, a+b) = W(a, -c) = W(c, a)$.

> __Lemma [div-rad-div].__ $f / \text{rad } f$ divides $f'$ for any nonzero $f$. ^lem-div-rad-div

For this one should use UFDness of $k[X]$. Factor $f$ into multiplications of prime powers and count the power of primes to check. So note that $f / \text{rad }f$ divides both $f$ and $f'$. The corollary is this:

> __Lemma [wronskian-div].__ $a/\text{rad }a$ divides $W(a, b)$ for nonzero $a$. ^lem-wronskian-div

We factor out a part of the main proof.

> __Lemma [wronskian-zero].__ If $a, b \in k[X]$ are nonzero and coprime to each other, then $W = W(a, b)$ is zero if and only if $a'=b'=0$. ^lem-wronskian-zero

_Proof._ If $a'=b'=0$ then it is evident that $W = 0$.
We now assume $W = 0$ and show $a'=b'=0$.

As $W(a, b) = 0$ we have $ab' = a'b$. As $b$ divides $ab'$, it also divides $b'$.
Now if $b'$ is not zero, then the degree of $b'$ is strictly less than $b$ so we get a contradiction. So $b' = 0$. By a similar argument we also get $a' = 0$ with $W(a, b) = 0$. □

_Proof._ (of [[#^thm-mason]]) We have $W = W(a, b) = W(b, c)$ by [[#^lem-wronskian-eq]]. And $a/\text{rad }a, b/\text{rad }b, c/\text{rad }c$ all divide $W$. Then, $a b c / \text{rad }(a b c)$ divides $W$ because $a/\text{rad }a, b/\text{rad }b, c/\text{rad }c$ are all coprime (informal note: This is the key step. $W$ is too good that it is divisible by all the factors, but has a small degree from its formula).

We divide the case into whether $W = 0$ or not. 
If $W = W(a, b) = W(b, c)$ is zero, then by [[#^lem-wronskian-zero]] we have $a' = b' = c' = 0$.
So assume otherwise that $W \neq 0$.
As $W$ is nonzero, $W = W(a, b) = a b' - a' b$ has degree $< \text{deg }a + \text{deg }b$ (note that this requires case analysis on whether $a'=0$ or $b' = 0$ or not for an exact treatment). Now $\text{deg }\left( a b c / \text{rad }(a b c) \right) < \text{deg }a + \text{deg }b$. 
Arranging terms then gives $\text{deg }(a) + \text{deg }(b) + \text{deg }(c) < \text{deg }a+\text{deg }b + \text{deg }\left( \text{rad }(a b c) \right)$ or $\text{deg }(c) < \text{deg }\left( \text{rad }(a b c) \right)$. The argument is symmetric, so applying the argument by rotation shows the other inequalities $\text{deg }(a) < \text{deg }\left( \text{rad }(a b c) \right)$ and $\text{deg }(b) < \text{deg }\left( \text{rad }(a b c) \right)$. Taking the max gives the desired inequality $\text{max}(\text{deg } a, \text{deg }b, \text{deg }c) < \text{deg} (\text{rad } a b c)$. □

> __Theorem [polynomial-flt].__ If $n \geq 3$ and $c^n=a^n+b^n$ in $k[X]$ and $a, b, c$ nonzero, all coprime to each other, then $a'=b'=c'=0$. ^thm-polynomial-flt

_Proof._ $a^n+b^n+(-c^n)=0$ so invoking [[#^thm-mason]] gives either one of the following.
- $\text{max}(\text{deg } a^n, \text{deg }b^n, \text{deg }c^n) < \text{deg} (\text{rad } a^n b^n c^n)$, so $n \max(\deg a, \deg b, \deg c) < \deg(\text{rad }a b c)$. But in this case then the following holds.
$\deg(\text{rad }a b c) = \deg(\text{rad }a) + \deg(\text{rad } b) + \deg(\text{rad } c)$
$\leq \deg(a) + \deg(b) + \deg(c) \leq 3 \max (\deg a, \deg b, \deg c)$
- This is only possible when all degrees of $a, b, c$ are equal to zero. That is, $a, b, c$ are constants.
- In the other case of [[#^thm-mason]] we get the conclusion immediately. □

Finally, note that for general field the derivative $a'$ of some $a \in k[X]$ being equal to zero is not equivalent to $a = 0$. If the characteristic is $p$ then the derivative of $X^p$ is $pX^{p-1} = 0$.
However, if the characteristic of $k$ is zero then $a' = 0$ is equivalent to $a$ being a constant.