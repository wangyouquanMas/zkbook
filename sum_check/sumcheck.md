\title{
Algebraic Methods for Interactive Proof Systems
}

\author{
CARSTEN LUND, LANCE FORTNOW, AND HOWARD KARLOFF \\ Unitersity of Chicago, Chicago, Illinois \\ AND
}

NOAM NISAN

Hebrew Untersity, Jerusalem, Israel

Abstract. A new algebraic technique for the construction of interactive proof systems is presented. Our technique is used to prove that every language in the polynomial-time hierarchy has an interactive proof system. This technique played a pivotal role in the recent proofs that IP = PSPACE [28] and that MIP = NEXP [4].

Categories and Subject Descriptors: F.1.2 [Computation by Abstract Devices]: Modes of Computation-Interactive computation; probablistic computation; relations among modes; relativized computation; F.1.3 [Computation by Abstract Devices]: Complexity Classes-Complexity hierarchies; relations among complexity classes

General Terms: Theory

Additional Key Words and Phrases: Interactive proof systems

\section{Introduction}

NP can be viewed as the set of languages $L$ with this property: There is a deterministic polynomial-time verifier (Vanna) and an infinitely powerful prover (Pat) such that for all $x$, if $x$ is in $L$, then in polynomial time Pat can persuade Vanna that $x$ is in $L$, and if $x$ is not in $L$, then no prover (Pat or any other) can persuade Vanna that $x$ is in $L$. Pat and Vanna communicate on a two-way channel (though two-way communication is not necessary here). For example, Pat can convince Vanna that a graph $G$ is 3-colorable by exhibiting a 3-

C. Lund's work was supported by a fellowship from the Århus University, Århus, Denmark.

L. Fortnow's work was supported by National Science Foundaton (NSF) grant CCR 90-09936.

H. Karloff's work was supported by NSF grant CCR 88-07534.

N. Nisan's work was partially performed at the Massachusetts Institute of Technology (MIT), Cambridge, Mass., and was supported by NSF grant CCR 86-5727 and Army Research Office (ARO) grant DLL03-86-K-017.

Authors' addresses: C. Lund, L. Fortnow, and H. Karloff. Department of Computer Science, University of Chicago, 1100 East 58th Street, Chicago, IL 60637; N. Nisan, Department of Computer Science, Hebrew University, Jerusalem, Israel.

Permission to copy without fee all or part of this material is granted provided that the copies are not made or distributed for direct commercial advantage, the ACM copyright notice and the title of the publication and its date appear, and notice is given that copying is by permission of the Association for Computing Machinery. To copy otherwise. or to republish. requires a fee and/or specific permission.

(C) 1992 ACM 0004-5411/92/1000-0859 $\$ 01.50$

Journal of the Association for Computıng Machinery, Vol. 39, No. 4, October 1992, pp 859-868 coloring. If $G$ is not 3-colorable, no prover will ever succeed in persuading Vanna that $G$ is 3-colorable. (Of course, co-NP-complete languages are not thought to be in NP. No prover is known who can convince a skeptical deterministic verifier that $G$ is not 3-colorable, if it is not 3-colorable.)

We can extend this idea of "provability" by allowing Vanna to flip coins and by requiring instead that if $x$ is in $L$, with probability at least $2 / 3$ Pat persuades Vanna that $x$ is in $L$, and if $x$ is not in $L$, no prover can convince Vanna that $x$ is in $L$ with probability more than $1 / 3$. Babai [2] and Goldwasser et al. [21] developed this interactive proof system model. A summary of previous results on interactive proof systems can be found in [5].

Although certain problems such as graph nonisomorphism, which are not known to be in NP, were known to have interactive proof systems [10], theoretical computer scientists generally believed that the class IP of languages accepted by interactive proof systems was not much larger than NP. In particular, it was believed that co-NP-complete languages did not have interactive proof systems.

We prove that interactive proof systems have far greater power than originally believed. Our main result is an interactive proof system for the language $\{(A, s) \mid s$ is the permanent of $0-1$ matrix $A\}$. When combined with the fact that the permanent 0-1 matrices is \#P-complete [33] and the fact that \#P is hard for the polynomial-time hierarchy [32], the existence of an interactive proof system for the permanent implies that every language in the polynomial-time hierarchy has an interactive proof system. In particular, this means that every language in co-NP has an interactive proof system, even the complement of 3-COLORABILITY, for example.

For the proof, we develop a new technique for reducing the problem of verifying the value of a low-degree polynomial at two given points to verifying the value at one new point. Shamir [28] has used this technique to prove that all languages in PSPACE have interactive proof systems. From the fact that IP $\subseteq$ PSPACE [15], it follows that IP = PSPACE. Babai et al. [4] have also used this technique in their proof that every language in nondeterministic exponential time has a two-prover interactive proof system in which the provers cannot communicate with one another.

Our results also have implications for program checking, verification and self-correction in the context of Blum and Kannan [9], Blum et al. [10], and Lipton [25]. In fact, the Blum-Luby-Rubinfeld and Lipton papers inspired our result.

Our result does not relativize. Fortnow and Sipser [18] have created an oracle under which co-NP does not have an interactive proof system. To our knowledge this is the first result to "go contrary" to a previously published oracle. Subsequent to the announcement of our result, Chor et al. [13] proved the same relativized result for a random oracle.

\section{Definitions}

A verifier $V$ is a polynomial-time, probabilistic Turing machine with a special communication tape. A prover $P$ is an arbitrary map $f$ from each finite sequence $x, q_{1}, q_{2}, q_{3}, \ldots$, where $x \in\{0,1\}^{*}$ and each $q_{l} \in\{0,1\}^{*}$, to a $0-1$ string.

The computation proceeds as follows. Both $P$ and $V$ get $x \in\{0,1\}^{*} . V$ then computes for a while, and writes a query $q_{1} \in\{0,1\}^{*}$ on her communication tape. $P$ responds by replacing the $q_{1}$ with $f\left(x, q_{1}\right) . V$ computes, overwrites $f\left(x, q_{1}\right)$ with a query $q_{2} \in\{0,1\}^{*}$, and awaits $P$ 's response, $f\left(x, q_{1}, q_{2}\right)$. This process continues until $V$ halts and accepts or rejects $x$. A round is a query from $V$ followed by a response from $P$.

The pair $(P, V)$ forms an interactive proof system for a language $L$ if for all $x \in\{0,1\}^{*}:$

(1) If $x \in L$, then $\operatorname{Pr}(V$ accepts input $x$ when interacting with $P) \geq \frac{2}{3}$.

(2) If $x \notin L$, then for all provers $P^{\prime}, \operatorname{Pr}(V$ accepts $x$ when interacting with $\left.P^{\prime}\right) \leq \frac{1}{3}$.

IP is the class of all languages which have interactive proof systems.

The class \#P consists of all functions $f:\{0,1\}^{*} \rightarrow \mathbb{N}$ for which there exists a polynomial-time, nondeterministic Turing machine $M$ such that for all inputs $x$, the number of accepting computations of $M$ on $x$ equals $f(x) . \mathrm{P}^{\# \mathrm{P}}$ is the class of languages recognized by a polynomial-time oracle Turing machine with an oracle for some function $f$ in \#P. Given $x$, the oracle Turing machine can learn $f(x)$ in one time step by querying its oracle.

\section{The Protocol}

We prove

THEOREM 1. Every language in $P^{\# P}$ has an interactive proof system.

Together with Toda's result that $\mathrm{P}^{\# \mathrm{P}}$ contains all the languages of the polynomial-time hierarchy [32], Theorem 1 implies:

COROLLARY 2. Every language in the polynomial-time hierarchy has an interactive proof system. In particular, every language in co-NP has an interactive proof system.

We list some facts about the permanent of a matrix $A$ that will be crucial in the proof of Theorem 1. If $A=\left(a_{\imath l}\right)$ is $r \times r$, the permanent $\operatorname{per}(A)=$ $\sum_{\sigma} a_{1 \sigma(1)} a_{2 \sigma(2)} \cdots a_{r \sigma(r)}$, where the sum is over all permutations $\sigma$ of $\{1,2, \ldots, r\}$. We can equivalently define the permanent recursively as $\operatorname{per}(A)=$ $\sum_{1 \leq t<r} a_{1,} \cdot \operatorname{per}\left(A_{1 \mid l}\right)$ where $A_{1 \mid i}$, the $(1, i)$-minor of $A$, is the matrix $A$ without the first row and the $i$ th column. The number of perfect matchings in an $N$-boy, $N$-girl bipartite graph $G$ is equal to the permanent of $G$ 's adjacency matrix.

We exhibit an interactive proof system for verifying the permanent of a 0-1 matrix. The following lemma implies that this is sufficient to prove Theorem 1.

LemMA 3. If $L=\{(A, s) \mid A$ is a 0-1 matrix and per $(A)=s\}$ has an interactive proof system, then every language in $P^{\# P}$ has an interactive proof system.

Proof Sketch. From the fact that computing the permanent of 0-1 matrices is \#P-complete [33], we can reduce the membership problem for a language $L^{\prime} \in \mathrm{P}^{\# \mathrm{P}}$ to that of verifying the permanents of $0-1$ matrices. Given an interactive proof system for $L$, it is easy to construct one for $L^{\prime}$.

Throughout most of this paper we work with the permanent over $\mathbb{Z}_{p}$ of an $N \times N$ matrix $A$ with entries in $\mathbb{Z}_{p}$, where $p$ is a prime in $(N !, 2 N !)$. (Bertrand's Postulate [26] guarantees the existence of such a prime.) If $A$ is $0-1$, then the permanent of $A$ over $\mathbb{Z}_{p}$ coincides with its permanent as an integer matrix, since the permanent of an $N \times N$ 0-1 matrix cannot exceed $N$ !. We use the crucial fact that if $B$ is an $r \times r$ matrix over $\mathbb{Z}_{p}$ whose entries are linear polynomials over $\mathbb{Z}_{p}$, then per $(B)$ is a polynomial of degree at most $r$ over $\mathbb{Z}_{p}$. Compared to $p$, any $r \leq N$ is minuscule.

The verifier Vanna will use this fact to "trip up" a cheating prover. She will maintain a list of pairs $\mathscr{L}=\left\langle\left(B_{1}, q_{1}\right),\left(B_{2}, q_{2}\right), \ldots,\left(B_{t}, q_{t}\right)\right\rangle$, where the $B_{i}$ 's are square matrices of the same size and $q_{l} \in \mathbb{Z}_{p}$. Initially $\mathscr{L}=\langle(A, s)\rangle$. If $s=\operatorname{per}(A)$, then a prover who truthfully answers all of Vanna's questions will induce Vanna eventually to shrink the list to a single pair $(B, q)$, where $B$ is $1 \times 1$ and $q=\operatorname{per}(B)$. At that point, Vanna will correctly accept the input.

If $s \neq \operatorname{per}(A)$, then however the prover answers Vanna's questions, with very high probability Vanna will maintain this "invariant": the list contains at least one pair $\left(B_{l}, q_{l}\right)$ such that $q_{l} \neq \operatorname{per}\left(B_{l}\right)$. ("Invariant" appears in quotes because with extremely low probability, at some point every $q_{l}$ might equal $\operatorname{per}\left(B_{t}\right)$.) When the list shrinks to one pair $(B, q)$ where $B$ is $1 \times 1$ and $q \neq \operatorname{per}(B)$, Vanna will reject the input (if not earlier).

How Vanna manipulates the list is the crux of the protocol. When $\mathscr{L}=\langle(B, q)\rangle\left(B=\left(b_{i j}\right), 1 \leq i, j \leq r\right.$, and $\left.r>1\right)$, for each $i=1,2, \ldots, r$, Vanna constructs the minor $B_{l}=B_{1 \mid l}$, asks Pat for the permanent of $B_{l}$, and gets $q_{l}$ in return. Vanna checks that $q=\sum_{t=1}^{t} b_{1} q_{i}$; if not, she halts and rejects. If $q=\sum_{t=1}^{r} b_{12} q_{t}$, she expands $\mathscr{L}$ by replacing $\mathscr{L}$ by $\left\langle\left(B_{1}, q_{1}\right)\right.$, $\left.\left(B_{2}, q_{2}\right), \ldots,\left(B_{r}, q_{1}\right)\right\rangle$. Provided that $q \neq \operatorname{per}(B), q_{l} \neq \operatorname{per}\left(B_{\imath}\right)$ for some $i$.

When the list has more than one pair, Vanna shrinks the list by replacing the first two pairs $(C, c),(D, d)$ by a new pair $(E, e)$, in the following way. The function $f(x)=\operatorname{per}(C+x(D-C))$ is a polynomial of degree at most $r$ over $\mathbb{Z}_{p}$. Vanna asks Pat for the $r+1$ coefficients of $f$ and constructs a polynomial $g$ from the responses. (Or Vanna could just ask for the value of $f$ at $r+1$ arbitrary points and interpolate herself.) If $g(0) \neq c$ or $g(1) \neq d$, Vanna rejects.

Vanna now uniformly chooses a random $a \in \mathbb{Z}_{p},{ }^{1}$ sends it to Pat, constructs $E=C+a(D-C)$ and $e=g(a)$, and replaces the pairs $(C, c),(D, d)$ in $\mathscr{L}$ by the one pair $(E, e)$. The crucial fact is that if $c \neq \operatorname{per}(C)$ or $d \neq \operatorname{per}(D)$, then with probability at least $1-r / p, \operatorname{per}(E) \neq e$. This follows from Lemma 4 .

LeMMA 4. Let $C$ and $D$ be $r \times r$ matrices over $\mathbb{Z}_{p}$. Let $g$ be a polynomial of degree at most r over $\mathbb{Z}_{p}$ such that either $g(0) \neq \operatorname{per}(C)$ or $g(1) \neq \operatorname{per}(D)$. Then if $a$ is chosen uniformly at random from $\mathbb{Z}_{p}$.

$$
\operatorname{Pr}[\operatorname{per}(C+a(D-C))=g(a)] \leq \frac{r}{p} .
$$

Proof. Let $f(x)=\operatorname{per}(C+x(D-C))$, a polynomial of degree at most $r$ over $\mathbb{Z}_{p}$. Since $f(0)=\operatorname{per}(C)$ and $f(1)=$ per $(D)$, clearly $f \neq g$. But two nonidentical polynomials of degree at most $r$ over $\mathbb{Z}_{p}$ can coincide on at most $r$

${ }^{1}$ Throughout the paper, we assume that Vanna can choose elements of $\mathbb{Z}_{p}$ uniformly at random, despite the fact that she can only pick bits uniformly at random. In reality, she will pick integers $a$ uniformly at random from $\{0,1,2, \ldots, M-1\}$, where $M$ is the least power of two exceeding $p$, until one is less than $p$. If enough trials fail to find an $a$ less than $p$, she will just halt and accept $x$. This increases the probability of erroneously accepting an $x \notin L$ only slightly. points. It follows that there are at most $r$ values $a$ such that

$$
g(a)=f(a)=\operatorname{per}(C+a(D-C)) .
$$

If $\mathscr{L}=\left\langle\left(B_{1}, q_{1}\right),\left(B_{2}, q_{2}\right), \ldots,\left(B_{t}, q_{t}\right)\right\rangle$ and at least one $i$ satisfies $\operatorname{per}\left(B_{l}\right) \neq$ $q_{l}$, then with very high probability, after $t-1$ shrinkings $\mathscr{L}$ will consist of one pair $(H, h)$ with $h \neq \operatorname{per}(H)$. The idea, then, is to replace the initial list $\mathscr{L}=\langle(A, s)\rangle$ by lists of smaller and smaller matrices, until eventually $\mathscr{L}=$ $\langle(B, q)\rangle$ where $B$ is $1 \times 1$. If $q \neq \operatorname{per}(B)-$ a condition Vanna can easily test -Vanna will reject. Otherwise, she'll accept.

How likely is it that Vanna will be able to maintain the "invariant"? A sequence of one expansion step followed by $r-1$ shrinking steps will replace $\mathscr{L}=\langle(B, q)\rangle$, where $B$ is $r \times r$, by $\mathscr{L}=\left\langle\left(B^{\prime}, q^{\prime}\right)\right\rangle$, where $B^{\prime}$ is $(r-1) \times$ $(r-1)$. Thus fewer than $N^{2}$ steps (of either kind) suffice to reduce $\mathscr{L}=$ $\langle(A, s)\rangle$ to $\mathscr{L}=\langle(B, q)\rangle$, where $B$ is $1 \times 1$. It follows that the probability that a cheating prover can induce Vanna to erroneously accept $(A, s)$ is less than $N^{2}$ times the minuscule probability (at most $N / p$ ) that a given expand or shrink step first violates the "invariant."

Now we give the full proof of Theorem 1.

Proof of TheOrem 1. By Lemma 3, it suffices to exhibit an interactive proof system for

$$
L=\{(A, s) \mid A \text { is a } 0-1 \text { matrix and } \operatorname{per}(A)=s\} .
$$

Here is a formal description of the protocol. $A$ is an $N \times N 0-1$ matrix and $0 \leq s \leq N$ !.

begin

Let $\mathscr{L}=\langle(A, s)\rangle$. Pat picks an integer in $p$ in $(N !, 2 N)$ and provides a short proof to Vanna that $p$ is prime [27]. All arithmetic in this protocol is done module $p$.

Repeat until $\mathscr{L}=\langle(B, q)\rangle$ for some $1 \times 1$ matrix $B$ :

if $\mathscr{L}=\langle(B, q)\rangle$, then do

Expand: Suppose that $B=\left(b_{t j}\right)$ is $r \times r$. Vanna constructs $B_{l}=B_{1 \mid l}$ for $1 \leq i \leq r$. She asks Pat for the permanents of $B_{l}, 1 \leq i \leq r$, and gets $q_{l}$ for the permanent of $B_{t}$. If $\sum_{i=1}^{r} b_{12} q_{l} \neq q$, Vanna rejects. Otherwise, she sets $\mathscr{L}=\left\langle\left(B_{1}, q_{1}\right),\left(B_{2}, q_{2}\right), \ldots,\left(B_{r}, q_{r}\right)\right\rangle$. else ( $\mathscr{L}$ has two or more pairs) do

Shrink: Vanna chooses the first two pairs $(C, c)$ and $(D, d)$ from $\mathscr{L}$, asks Pat for the $r+1$ coefficients of $f(x)=\operatorname{per}(C+x(D-C)$ ) (where $C$ and $D$ are $r \times r$ ), and constructs $g(x)$ from them. If $g(0) \neq c$ or $g(1) \neq d$, Vanna rejects. Otherwise, she chooses a random $a \in \mathbb{Z}_{p}$, sends it to Pat, and replaces the pairs $(C, c),(D, d)$ in $\mathscr{L}$ by $(C+a(D-C), g(a))$.

When $\mathscr{L}=\langle(B, q)\rangle$ and $B$ is $1 \times 1$, Vanna accepts if $q=\operatorname{per}(B)$ and rejects if $q \neq \operatorname{per}(B)$. end

The protocol contains exactly $N-1$ Expand steps and $(N-1)+(N-2)$ $+\cdots+2+1$ Shrink steps if Vanna accepts $(A, s)$.

We prove:

(1) There is a prover Pat such that for all $N$ and all $N \times N 0-1$ matrices $A$, if $s=\operatorname{per}(A)$, then $\operatorname{Pr}[$ Vanna accepts $(A, s)]=1$.

(2) If $s \neq \operatorname{per}(A)$, then for all powers, $\operatorname{Pr}[\operatorname{Vanna}$ accepts $(A, s)]<N^{3} / p<1 / 3$ (if $N \geq 6$ ).

It is easy to see that a prover who truthfully answers all of Vanna's questions when $\operatorname{per}(A)=s$ induces Vanna with probability one to reduce $\mathscr{L}$ to $\langle(B, q)\rangle$ with $B 1 \times 1$ and $q=\operatorname{per}(B)$. At this point Vanna accepts. This completes the proof of (1).

For (2), let $s \neq \operatorname{per}(A)$. Fix any prover Pat. If Vanna accepts $(A, s)$, then, at some time, $\mathscr{L}=\langle(B, q)\rangle$ with $q=\operatorname{per}(B)$; initially $\mathscr{L}=\langle(A, s)\rangle$ with $s \neq$ per $(A)$. We say that Pat succeeds in iteration $m$ if the repeat loop is executed in full at least $m$ times, and

$$
q=\operatorname{per}(B) \text { for all }(B, q) \text { in } \mathscr{L}
$$

first occurs just after the repeat loop has been executed exactly $m$ times. Pat succeeds in some iteration if Vanna accepts. Since there are only $N+$ $(N-1)+\cdots+2<N^{2}$ iterations, it suffices to prove that $\operatorname{Pr}[$ Pat succeeds in iteration $m]<N / p$.

Fix an $m$. Without loss of generality, we may assume that Pat never induces Vanna to reject until $\mathscr{L}$ consists of only one pair, in which the matrix is $1 \times 1$. (Otherwise, we may replace Pat by another prover Pat' who, instead of inducing Vanna to reject early, answers the remaining questions in a way that is consistent with his earlier responses, as long as possible. Against such a prover Vanna will not halt until the last stage of the protocol. The probability that Pat succeeds in iteration $m$ is no greater than the probability that Pat' does.)

Pat simply cannot succeed in an Expand step: If $\mathscr{L}=\langle(B, q)\rangle$ with $q \neq$ per $(B)$ becomes $\mathscr{L}=\left\langle\left(B_{1}, q_{1}\right), \ldots,\left(B_{r}, q_{r}\right)\right\rangle$ with $q_{l}=\operatorname{per}\left(B_{l}\right)$ for all $i$, Vanna immediately rejects.

If iteration $m$ is a Shrink step, $\mathscr{L}$ contains $(C, c)$ and $(D, d)$ before the step and $(E, e)$ afterward. If $c=\operatorname{per}(C)$ and $d=\operatorname{per}(D)$, then $\mathscr{L}$ contained a pair $(H, h)$ with $h \neq \operatorname{per}(H)$. It still does. So we may assume that either $c \neq \operatorname{per}(C)$ or $d \neq \operatorname{per}(D)$. In this case, Lemma 4 tells us that $\operatorname{Pr}[\mathrm{e}=\operatorname{per}(E)]<N / p$. Thus,

$$
\operatorname{Pr}[\text { Pat succeeds in iteration } m]<\frac{N}{p} \text {. }
$$

\section{Extensions}

The protocol above requires $\Omega\left(N^{2}\right)$ rounds of prover-verifier communication when the input matrix is $N \times N$. Babai has suggested the following scheme to reduce the number of rounds to $O(N)$. His idea makes it possible to shrink a list $\mathscr{L}$ with $r$ pairs into a list $\mathscr{L}^{\prime}$ with one pair in one round. For $1 \leq i \leq r$, let

$$
f_{i}(x)=\prod_{j: j \neq l .1 \leq j \leq r} \frac{(x-j)}{(i-j)} .
$$

Note that $f_{l}(x)$ is a polynomial over $\mathbb{Z}_{p}$ of degree $r-1$ with $f_{l}(i)=1$, and if $j \neq i$, then $f_{I}(j)=0$. Let $\mathscr{L}=\left\langle\left(B_{1}, q_{1}\right),\left(B_{2}, q_{2}\right), \ldots,\left(B_{r}, q_{r}\right)\right\rangle$ and define $C(x)=\sum_{t=1}^{r} f_{i}(x) B_{i}$. The matrix $C(x)$ has entries consisting of polynomials of degree at most $r-1$. Now $f(x)=\operatorname{per}(C(x))$ is a polynomial of degree at most $r(r-1)$ with $f(i)=\operatorname{per}(C(i))=\operatorname{per}\left(B_{l}\right)$ for all $i, 1 \leq i \leq r$. This gives us an alternative Shrink procedure:

Shrink: Vanna asks Pat for the $r(r-1)+1$ coefficients of $f(x)=$ per $(C(x))$ and constructs $g(x)$ from them. If $g(i) \neq q_{i}$ for some $1 \leq i \leq r$, then Vanna rejects. Otherwise, she chooses a random $a \in \mathbb{Z}_{p}$, sends it to Pat and replaces $\mathscr{L}$ by $\langle(C(a), g(a))\rangle$.

The proof of correctness is similar to that of Theorem 1 and is omitted here.

Because the number of rounds of an interactive proof system can be reduced by a constant factor [5], for any $\epsilon>0$ there is a variant of our permanent protocol running in at most $\epsilon N$ rounds. A bounded-round protocol for the permanent would imply that the polynomial-time hierarchy collapses, since Boppana et al. [11] have shown that if all co-NP languages have bounded-round protocols, then the hierarchy collapses. To our knowledge, this is the first example of an interactive proof system that appears to require an unbounded number of rounds.

Babai and Fortnow [3] and Shamir [28] have provided alternate interactive proof systems for verifying the values of \#P functions by counting the number of assignments satisfying a CNF formula, thus circumventing the need for Valiant's result on the completeness of the permanent. They have shown how to "arithmetize" a formula as a low-degree polynomial so that Pat and Vanna can use a protocol similar to that of Section 3 to verify the number of satisfying assignments.

Shamir [28] has shown how to arithmetize a QBF formula, using dummy variables to keep the degree low. Using a protocol similar to that in Section 3, he then proves that every language in PSPACE has an interactive proof system. Shen [29] later provided a "degree-reduction operator" as an alternate technique to keep the degree low.

Babai et al. [4] have applied the techniques of this paper to multiple-prover interactive proof systems, defined by Ben-Or et al. [8] as interactive proof systems having a polynomial number of provers unable to communicate among themselves or to see the conversation between any other prover and the verifier. Babai, Fortnow, and Lund have proven that any language computable in nondeterministic exponential time has a multiple-prover interactive proof system. Their proof uses ideas similar to those of [3] and [28] in order to reduce the problem to that of testing the multilinearity of a function.

Cai et al. [12] have used the protocols of this paper and of Shamir [28] to prove that every PSPACE language has a bounded-round multiple-prover interative proof system.

Fortnow and Lund [16] have extended the techniques from this and Shamir's paper [28] to exhibit a polynomial equivalence between time-space complexity of alternating Turing machines and the time-space complexity of the verifier in a public-coin interactive proof system. In particular, they prove that every language in NC has an interactive proof system with a public-coin, polynomialtime, logarithmic-space verifier.

\section{Implications}

Goldwasser and Sipser [22] have shown that one can convert any interative proof system to one in which the verifier uses public coins, that is, the verifier juxtaposes her coin tosses and her query message $q_{l}$ on her communication tape. Furer et al. [19] have shown how to modify an interactive proof system so that for true instances the verifier is convinced with probability one. Both of these properties already hold for our protocol. Some simple corollaries that follow from these results:

COROLLARY 5. If cryptographic one-way functions exist, then every language in the polynomial-time hierarchy has a zero-knowledge interactive proof system.

PROOF. Every language with an interactive proof system has a zeroknowledge interactive proof system if one-way functions exist [7, 23].

From Shamir [28], we infer that all languages computable in polynomial space have zero-knowledge interactive proof systems if cryptographic one-way functions exist.

COROLLARY 6. If every language in IP has a bounded-round interactive proof system, then the polynomial-time hierarchy collapses.

This is immediate from Boppana et al. [11]. Previously, Aiello et al. [1] constructed an oracle relative to which the class of languages with unboundedround interactive proof systems differs from those with bounded-round interactive proof systems.

Our theorem also has applications to program checking, verification and self-correction. Lipton [25], using ideas of Beaver and Feigenbaum [6], showed that the permanent function can be "tested." Our protocols extend this idea and show the permanent has a self-testing/correcting pair [10], a pair of functions the first of which verifies that a program computes the permanent correctly on most inputs and the second of which converts a program that passes the first test into one that correctly computes the permanent on all inputs with high probability.

Theorem 1 also provides a program correctness checker [9] for the permanent:

COROLLARY 7. There exists a probablistic polynomial-time machine $M$ that, given access to a program $P$ and a matrix $A$, will output with a high degree of confidence either " $P$ outputs the correct value of the permanent of $A$ " or " $P$ does not correctly compute the permanent of some matrix."

Proof. In the proof of Theorem 1, the prover need only answer questions about the permanents of various matrices. We can have $M$ simulate the verifier and use $P$ as the prover.

A further discussion of the relationship between interactive proof systems and program testing can be found in [4].

MA is the class of languages accepted by an interactive proof system consisting of a single message from the prover to the verifier followed by probablistic verification by the verifier. We can think of this class as the set of "publishable proofs," "proofs" that can be written down now and randomly verified years later without any help from the prover. Babai has proven that $\mathrm{MA} \subseteq \sum_{2}^{P} \cap \Pi_{2}^{P}$ [2]. Corollary 8 implies that if \#P has polynomial-size circuits, then $\mathrm{P}^{\# \mathrm{P}}$, and hence the polynomial-time hierarchy, lies in MA.

COROLLARY 8. If \#P has polynomial-size circuits, then $P^{\# P} \subseteq M A$.

Proof. The prover gives the verifier a circuit computing the permanent. She uses this circuit as the prover in the protocol in Section 3.

A general discussion of Corollary 8 appears in [4] where it is shown that a similar result holds for PSPACE and EXP. Contrast Corollary 8 with the result of Karp and Lipton [24] that if NP has polynomial-size circuits, then the polynomial-time hierarchy collapses to $\Sigma_{2}^{P}$.

\section{Further Research}

We have proven that every language reducible to a \#P-complete problem has an interactive proof system, and thus, so does every language in the polynomial-time hierarchy. In particular, every language in co-NP has an interactive proof system. However, even for a co-NP-complete language, in the protocol above the prover must answer \#P-complete questions. Is there an interactive proof system for co-SAT where the prover need only answer questions about the satisfiability of CNF formulas? Such a proof system would give an instance checker for NP-complete languages.

We believe that one should study why this result does not relativize. One simple answer is that we have exhibited an interactive proof system for a very specific \#P-complete function-the permanent-which is not \#P-complete relative to any sufficiently complex oracle (since the permanent does not depend on the oracle). Babai and Fortnow [3] have exhibited a simple characterization of \#P functions by polynomials and have used this characterization to prove the main theorem of this paper without any reference to permanents. This algebraic formulation of \#P does not hold in relativized worlds. Studying the algebraic structure of well-known complexity classes may lead to yet more exciting relationships among them.

\section{REFERENCES}

Note: References [17], [30], and [31] are not cited in text.

1. Aiello, W., Goldwasser, S., And HÅstad, J. On the power of interaction. Combinatorica, $10,1(1992), 3-25$.

2. Babal, L. Trading group theory for randomness. In Proceedings of the 17th Annual ACM Symposium on the Theory of Computing (Providence, R.I., May 6-8). ACM, New York, 1985, pp. $421-429$.

3. BABAI, L., AND FORTNOW, L. Arithmetization: a new method in structural complexity theory. Computat. Complex: 1 (1991), 41-66.

4. Babai, L., Fortnow, L. And Lund, C. Non-deterministic exponential time has two-prover interactive protocols. Computat. Complex. 1 (1991), 3-40.

5. Babal, L., AnD Moran, S. Arthur-Merlin games: A randomized proof system, and a hierarchy of complexity classes. J. Comput. Syst. Sci. 362 (1988), 254-276.

6. Beaver, D. And Feigenbaum, J. Hiding instances in multioracle queries. In Proceedings of the 7th Symposium on the Theoretical Aspects of Computer Sclence. Lecture Notes in Computer Science, vol. 415. Springer Verlag, New York, 1990, pp. 37-48.

7. Ben-Or, M., Goldreich, O., Goldwasser, S., HÅstad, J., Kilian, J., Micali, S., and Rogaway, P. Everything provable is provable in zero-knowledge. In Proceedings of Crypto 88. Lecture notes in Computer Science, vol. 403. Springer-Verlag, New York, 1988, pp. 37-56.

8. Ben-Or, M., Goldwasser, S., Kilian, J., And Wigderson, A. Multi-prover interactive proofs: How to remove intractability assumptions. In Proceedings of the 20th Annual ACM Symposium on the Theory of Computing (Chicago, Ill, May 2-4). ACM, New York, 1988, pp. $113-131$.

9. Blum, M., And Kannan, S. Designing programs that check their work. In Proceedings of the 21th Annual ACM Symposium on the Theory of Computing (Seattle, Wash., May 15-17). ACM, New York, 1989. pp. 86-97.

10. Blum, M., LuBY, M.. AND RuBinfeLD, R. Self-testing correcting with applications to numerical problems. In Proceedings of the 22nd Annual ACM Symposium on the Theory of Computing (Baltimore, Md., May 14-16). ACM, New York, 1990, pp. 73-83.

11. BoppanA, R., HÅstaD, J., AND ZAChos, S. Does co-NP have short interactive proofs? Inf. Proc. Lett. 25, 2 (1987), 127-132. 12. CAI, J., CONDON, A., AND LiPTON, R. J. PSPACE is provable by two provers in one round. In Proceedings of the 6th Annual Conference on Structure in Complexity Theory (Chicago, Ill.. June 30-July 3). IEEE, New York, 1991, pp. 110-115.

13. Chor, B., Goldreich, O., and HAstad, J. The random oracle hypothesis is false. Manuscript. Technion, Haifa, Israel, 1990.

14. СоOK, S. A. The complexity of theorem-proving procedures. In Proceedings of the 3rd Annual ACM Symposum on the Theory of Computing (Shaker Herghts, Oh., May 3-5). ACM, New York, 1971, pp. 151-158.

15. Feldman, P. The optimum prover lives in PSPACE. Manuscript. M.I.T., Cambridge, Mass., 1986.

16. Fortnow, L., AND Lund, C. Interactive proof systems and alternating time-space complexity. In Proceedings of the 8th Symposium on Theoretical Aspects of Computer Science Lecture Notes in Computer Science, vol. 480, Springer-Verlag, New York, 1991, pp. 263-274.

17. FORTNOW, L., ROMPEL, J., AND SIPSER, M. On the power of multi-prover interactive protocols. In Proceedings of the 3rd Conference on Structure in Complexity Theory (Washington, D.C., June 14-17). IEEE, New York, 1988, pp. 156-161.

18. FORTNOW, L.. AND SiPSER, M. Are there interactive protocols for co-NP languages? Inf. Proc. Lett. 28 (1988), 249-251.

19. Furer, M., Goldreich, O., Mansour, Y., Sipser, M., and Zachos, S. On completeness and soundness in interactive proof systems. In S. Micali, ed. Randomness and Computatton, (volume 5 of Advances in Computing Research). JAI Press, Greenwich. Conn. 1989, pp. $429-442$.

20. Goldreich, O. Micali, S., AND Wigderson, A. Proofs that yield nothing but their validity and a methodology of cryptographic protocol design. In Proceedings of the 27th IEEE Symposium on Foundations of Computer Sclence. IEEE, New York, 1986, pp. 174-187.

21. GoldwasSER, S., MiCALI, S., AND RACKOFF, C. The knowledge complexity of interactive proof-systems. SLAM J. Comput. 18, 1 (1989), 186-208.

22. GoldWASSER, S. AND SIPSER, M. Private coins versus public coins in interactive proof systems. In S. Micali, ed. Randomness and Computatoon, (volume 5 of Adiances in Computing Research). JAI Press, Greenwich, Conn. 1989, pp. 73-90.

23. Impagliazzo, R., and Yung, M. Direct minimum-knowledge computation. In Proceedings of Crypto 87. Lecture Notes in Computer Science, vol. 293, Springer-Verlag, New York, 1987, pp. $40-51$.

24. KARP, R., AND LIPTON, R. Some connection between nonunıform and uniform complexity classes. In Proceedings of the 12th Annual ACM Symposum on the Theory of Computing (Los Angeles, Calif, Apr. 28-30). ACM, New York, 1980, pp. 302-309.

25. Lipton, R. New directions in testing. In J. Feigenbaum and M. Merritt, eds. Distributed Computing and Cryptography (volume 2 of DIMACS Scres in Discrete Mathematics and Theoretical Computer Science). American Mathematical Society, Providence, R.I., 1991, pp. $191-202$.

26. Niven, I., And Zuckerman, H. S. An introduction to the theory of numbers 4th ed., Wiley, New York, 1980, pp. 224-225.

27. Pratt, V. Every prime has a succinct certificate. SLAM J. Comput. 4 (1975), 214-220.

28. Shamir, A. IP = PSPACE. J. ACM 39, 4 (Oct. 1992), 869-877.

29. SHEN, A. IP = PSPACE: Sımplified proof. J ACM 39, 4 (Oct. 1992), 878-880.

30. Smon, J. On some central problems in computational complexity. PhD thesis, Cornell University, Computer Science, 1975. Tech Report TR 75-224.

31. Solovay, R., AND Strassen, V. A fast Monte-Carlo test for primality. SIAM J. Comput. 6 (1977), 84-85. See also erratum 7 (1978), 118.

32. TODA, S. On the computational power of PP and $\oplus \mathbf{P}$. In Proceedings of the 30th IEEE Symposium on Foundations of Computer Science. IEEE, New York, 1989, pp. 514-519.

33. Valiant, L. The complexity of computing the permanent. Theoret. Comput. SCl 8 (1979), $189-201$.

RECEIVED NOVEMBER 1990; REVISED NOVEMBER 1991 ; ACCEPTED AUGUST 1991

Journdi of the Assiciation for Computing Machinery, Vol 39, No 4, Octobcr 1992