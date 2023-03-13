We work on field $k$. For any nonzero $f \in k[X]$, $\text{rad} (f)$ is the multiplication of the irreducible factors of $f$ with no multiplicity. Note that $\text{rad}(f)$ is defined up to associativity (nonzero scalar multiplication). Another pain point is that we don't talk about $\text{deg }f$ when $f$ is zero.

> __Theorem [mason].__ If $a, b, c \in k[X]$ are nonzero and $a + b + c = 0$ and they are coprime to each other (a, b being coprime implies all the others), then either $\text{max}(\text{deg } a, \text{deg }b, \text{deg }c) < \text{deg} (\text{rad } a b c)$ or all $a', b', c'$ are zero.  ^thm-mason

> __Definition [wronskian].__ $W(a, b)=ab'-a'b$. Note that this is bilinear and antisymmetric. ^def-wronskian

> __Lemma [wronskian-eq].__ If $a+b+c=0$ then $W(a, b) = W(b, c) = W(c, a)$. ^lem-wronskian-eq

Quick check: $W(a, b) = W(a, a+b) = W(a, -c) = W(c, a)$.

> __Lemma [div-rad-div].__ $f / \text{rad } f$ divides $f'$ for any nonzero $f$. ^lem-div-rad-div

For this one should use UFDness of $f$. So note that $f / \text{rad }f$ divides both $f$ and $f'$. Corollary is this:

> __Lemma [wronskian-div].__ $a/\text{rad }a$ divides $W(a, b)$ for nonzero $a$. ^lem-wronskian-div

_Proof._ (of [[#^thm-mason]]) We have $W = W(a, b) = W(b, c)$ by [[#^lem-wronskian-eq]]. And $a/\text{rad }a, b/\text{rad }b, c/\text{rad }c$ all divide $W$. This is the key step. Then, $a b c / \text{rad }(a b c)$ divides $W$ because they are all coprime.

Our middle goal is to show that either $W = 0$ or $\text{max}(\text{deg } a, \text{deg }b, \text{deg }c) < \text{deg} (\text{rad } a b c)$ holds. Assume $W \neq 0$ by method of contradiction. Then $W = W(a, b) = a b' - a' b$ has degree $< \text{deg }a + \text{deg }b$ (note that this requires case analysis on whether $a'=0$ or $b' = 0$ or not for an exact treatment). Now $\text{deg }\left( a b c / \text{rad }(a b c) \right) < \text{deg }a + \text{deg }b$. Term arrangement than gives $\text{deg }(a) + \text{deg }(b) + \text{deg }(c) < \text{deg }a+\text{deg }b + \text{deg }\left( \text{rad }(a b c) \right)$ or $\text{deg }(c) < \text{deg }\left( \text{rad }(a b c) \right)$. The argument is symmetric, so applying the argument by rotation shows the other goal. 

Next, we show that $W=0$ if and only if $a'=b'=c'=0$. $ab'=a'b$, so if $a'$ is nonzero then $a$ should divide $a'$ and it is contradiction. So $a'=0$. WLOG argument gives all the other items we need. □

> __Theorem [polynomial-flt].__ If $n \geq 3$ and $c^n=a^n+b^n$ in $k[X]$ and $a, b, c$ nonzero, all coprime to each other, then $a'=b'=c'=0$. ^thm-polynomial-flt

_Proof._ $a^n+b^n+(-c^n)=0$ so invoking [[#^thm-mason]] gives either one of the following.
- $\text{max}(\text{deg } a^n, \text{deg }b^n, \text{deg }c^n) < \text{deg} (\text{rad } a^n b^n c^n)$, so $n \max(\deg a, \deg b, \deg c) < \deg(\text{rad }a b c)$. But in this case then the following holds.
$\deg(\text{rad }a b c) = \deg(\text{rad }a) + \deg(\text{rad } b) + \deg(\text{rad } c)$
$\leq \deg(a) + \deg(b) + \deg(c) \leq 3 \max (\deg a, \deg b, \deg c)$
- This is only possible when all degrees of $a, b, c$ are equal to zero. That is, $a, b, c$ are constants.
- In the other case of [[#^thm-mason]] we pretty much get the same thing. □
