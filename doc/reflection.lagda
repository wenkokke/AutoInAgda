\section{Adding reflection}
\label{sec:reflection}

\review{You mention that you still need to convert between AgTerm and
  PsTerm. But equally important in this section will be the conversion
  between Proof and AgTerm (and implicitly, between AgTerm and Rules),
  right? Maybe better mention these aspects at the beginning as well.}

To complete the definition of our |auto| function, we still need to
convert between Agda's built-in |Term| data type and the
data type required by our unification and resolution algorithms, |PsTerm|. This
is an essential piece of plumbing, necessary to provide the desired proof
automation.  While not conceptually difficult, this
does expose some of the limitations and design choices of the |auto| function.

The first thing we will need are
concrete definitions for the |TermName| and |RuleName| data types,
which were parameters to the development presented in the previous
section. \pepijn{Check if it was actually the previous section.}
It would be desirable to identify both types with Agda's |Name| type,
but unfortunately Agda does not assign a name to the function
space type operator, |_→_|; nor does Agda assign names to locally bound variables.
To address this, we define two new data types |TermName| and |RuleName|.

\noindent First, we define the |TermName| data type.
\begin{code}
data TermName : Set where
  name  : Name → TermName
  pvar  : ℕ → TermName
  impl  : TermName
\end{code}
The |TermName| data type has three constructors. The |name|
constructor embeds Agda's built-in |Name| in the |TermName| type.
The |pvar| constructor describes locally bound variables, represented by
their De Bruijn index. Note that the |pvar| constructor has nothing to
do with |PsTerm|'s |var| constructor: it is not used to construct
a Prolog variable, but rather to be able to refer to a local variable
as a Prolog constant.
Finally, |impl| explicitly represents the Agda function space.

We define the |RuleName| type in a similar fashion:
\begin{code}
data RuleName : Set where
  name  :  Name → RuleName
  rvar  :  ℕ → RuleName
\end{code}
The |rvar| constructor is used to refer to Agda variables as
rules. Its argument |i| corresponds to the variable's De Bruijn index
-- the value of |i| can be used directly as an argument to the |var|
constructor of Agda's |Term| data type.

As we have seen in Section~\ref{sec:motivation}, the |auto| function
may fail to find the desired proof. Furthermore, the conversion from
|AgTerm| to |PsTerm| may also fail for various reasons. To
handle such errors, we will work in the |Error| monad defined below:
\begin{code}
  Error : (A : Set a) → Set a
  Error A = Message ⊎ A
\end{code}
Upon failure, the |auto| function will produce an error message. The
corresponding |Message| type simply enumerates the possible sources of
failure:
\begin{code}
  data Message : Set where
    searchSpaceExhausted  : Message
    unsupportedSyntax     : Message
\end{code}
The meaning of each of these error messages will be explained as we
encounter them in our implementation below.

Finally, we will need one more auxiliary function to manipulate bound
variables. The |match| function takes two bound variables of types
|Fin m| and |Fin n| and computes the corresponding variables in |Fin
(m ⊔ n)| -- where |m ⊔ n| denotes the maximum of |m| and |n|:
\begin{code}
match : Fin m → Fin n → Fin (m ⊔ n) × Fin (m ⊔ n)
\end{code}
The implementation is reasonably straightforward. We compare the
numbers |n| and |m|, and use the |inject| function to weaken the
appropriate bound variable. It is straightforward to use this |match|
function to define similar operations on two terms or a term and a
list of terms.


\subsection*{Constructing terms}

We now turn our attention to the conversion of an |AgTerm| to a
|PsTerm|. There are two problems that we must address.

First of all, the |AgTerm| type represents all (possibly higher-order)
terms, whereas the |PsTerm| type is necessarily first-order.  We
mitigate this problem by allowing the conversion to 'fail', by
producing a term of the type |Exception|, as we saw in the
introduction. \pepijn{Check if we mention |Exception| in the introduction.}

Secondly, the |AgTerm| data type uses natural numbers to represent
variables. The |PsTerm| data type, on the other hand, represents
variables using a finite type |Fin n|, for some |n|. To convert
between these representations, the function keeps track of the current
depth, i.e.\ the number of |Π|-types it has encountered, and uses this
information to ensure a correct conversion. We sketch the definition
of the main function below:
\begin{code}
    convert : (depth : ℕ) → AgTerm → Error (∃ PsTerm)
    convert d (var i [])    = inj₂ (convertVar d i)
    convert d (con n args)  = convertName n ∘ convert d ⟨$⟩ args
    convert d (def n args)  = convertName n ∘ convert d ⟨$⟩ args
    convert d (pi (arg (arg-info visible _) (el _ t₁)) (el _ t₂))
      with convert d t₁ | convert (suc d) t₂
    ... | inj₁ msg        | _         = inj₁ msg
    ... | _               | inj₁ msg  = inj₁ msg
    ... | inj₂ (n₁ , p₁)  | inj₂ (n₂ , p₂)
      with match p₁ p₂
    ... | (p₁′ , p₂′) = inj₂ (n₁ ⊔ n₂ , con impl (p₁′ ∷ p₂′ ∷ []))
    convert d (pi (arg _ _) (el _ t₂)) = convert (suc d) t₂
    convert d _             = inj₁ unsupportedSyntax
\end{code}
We define special functions, |convertVar| and |name2term|, to convert
variables and constructors or defined terms respectively. The
arguments to constructors or defined terms are processed using the
|convertChildren| function defined below.
The conversion of a |pi| node binding an explicit argument proceeds by
converting the domain and codomain. If both conversions succeed, the
resulting terms are |match|ed and a |PsTerm| is constructed using
|impl|.
Implicit arguments and instance arguments are ignored by this conversion
function. Sorts, levels, or any other Agda feature mapped to the
constructor |unknown| of type |Term| triggers a failure with the
message |unsupportedSyntax|.

The |convertChildren| function converts a list of |Term| arguments to a list
of Prolog terms, by stripping the |arg| constructor and recursively
applying the |convert| function. We only give its type signature
here, as the definition is straightforward:
\begin{code}
  convertChildren : ℕ → List (Arg Term) → Error (∃ (List ∘ PsTerm))
\end{code}
Next, the |convertName| function constructs a first-order constant from an
Agda |Name| and list of terms:
\begin{code}
  convertName : Name → ∃ (λ n → List (PsTerm n)) → ∃ PsTerm
  convertName f (n , ts) = n , con (name f) ts
\end{code}

Lastly, the |convertVar| function converts a natural number,
corresponding to a variable name in the |AgTerm| type, to the
corresponding |PsTerm|:
%{
%format (dot (a)) = "\lfloor " a "\rfloor"
\begin{code}
  convertVar : ℕ → ℕ → ∃ PsTerm
  convertVar n i with compare n i
  convertVar (dot(  _))         _    | greater  (dot(_)) k  = (suc k , var (# k))
  convertVar (dot(  _))         _    | equal    (dot(_))    = (suc 0 , var (# 0))
  convertVar        _    (dot(  _))  | less     (dot(_)) k  = (0 , con (pvar k) [])
\end{code}
%}
The |convertVar| function compares the number of binders that have been
encountered with its argument De Bruijn index. If the variable is
bound within the goal type, it computes a corresponding |PsTerm|
variable;
if the variable is bound \emph{outside} of the goal type, however, we
compute a skolem constant.

To convert between an |AgTerm| and |PsTerm| we simply call the
|convert| function, initializing the number of binders
encountered to |0|.
\begin{code}
  agda2term : AgTerm → Error (∃ PsTerm)
  agda2term t = convert 0 t
\end{code}


\subsection*{Constructing rules}

Our next goal is to construct rules. More specifically, we need to
convert a list of quoted |Name|s to a hint database of Prolog rules.
To return to our example in Section~\ref{sec:motivation}, the
definition of |even+| had the following type:
\begin{code}
  even+ : Even n → Even m → Even (n + m)
\end{code}
We would like to construct a value of type |Rule| that expresses how
|even+| can be used. In Prolog, we might formulate the lemma above as
the rule:
\begin{verbatim}
  even(add(M,N)) :- even(M), even(N).
\end{verbatim}
In our Agda implementation, we can define such a rule manually:
\begin{code}
Even+ : Rule 2
Even+ = record {
  name        =  name even+
  conclusion  =  con  (name (quote Even)) (
                 con  (name (quote _+_)) (var (# 0) ∷ var (# 1) ∷ [])
                 ∷  []
                 )
  premises    =     con  (name (quote Even)) (var (# 0) ∷ [])
                 ∷  con  (name (quote Even)) (var (# 1) ∷ [])
                 ∷  []
  }
\end{code}
In the coming subsection, we will show how to generate the above
definition from the |Name| representing |even+|.

This generation of rules is done in two steps. First, we will convert a
|Name| to its corresponding |PsTerm|:
\begin{code}
  name2term : Name → Error (∃ PsTerm)
  name2term = agda2term ∘ unel ∘ type
\end{code}
The |type| construct maps a |Name| to the |AgTerm| representing
its type; the |unel| function discards any information about sorts; the
|agda2term| was defined previously.

In the next step, we process this |PsTerm|. The |split|
function, defined below, splits a |PsTerm| at every top-most
occurrence of the function symbol |impl|. Note that it would be
possible to define this function directly on the |AgTerm| data type,
but defining it on the |PsTerm| data type is much cleaner as we
may assume that any unsupported syntax has already been removed.
\begin{code}
  split  : PsTerm n → ∃ (λ k → Vec (PsTerm n) (suc k))
  split (con impl (t₁ ∷ t₂ ∷ [])) = Product.map suc (_∷_ t₁) (split t₂)
  split t = (0 , t ∷ [])
\end{code}

Using all these auxiliary functions, we now define
the |name2rule| function below that constructs a |Rule| from an Agda |Name|.
\review{What is the type of initLast? From the name I would have
  expected |Vec A (suc n) -> Vec A n × A|, but there is a third
  component in the result.}
\pepijn{That's a decent point. While one can look this up, it may be
  worth mentioning that the discarded argument it a witness to the
  correctness of |initLast|. Or mention from where we import it.}
\begin{code}
  name2rule : Name → Error (∃ Rule)
  name2rule nm with name2term nm
  ... | inj₁ msg             = inj₁ msg
  ... | inj₂ (n , t)         with split t
  ... | (k , ts)             with initLast ts
  ... | (prems , concl , _)  = inj₂ (n , rule (name nm) concl (toList prems))
\end{code}
We convert a name to its corresponding |PsTerm|, which is split
into a vector of terms using |split|.  The last element of this
vector is the conclusion of the rule; the prefix constitutes
the premises.

\subsection*{Constructing goals}

Next, we turn our attention to converting a goal |AgTerm| to a
|PsTerm|. While we could use the |agda2term| function to do so,
there are good reasons to explore other alternatives.

Consider the example given in Section~\ref{sec:motivation}. The goal
|AgTerm| we wish to prove is |Even n → Even (n + 2)|. Calling
|agda2term| would convert this to a |PsTerm|, where the
function space has been replaced by the |impl|. What we would like to
do, however, is to introduce arguments as available assumptions, such
as |Even n|, and try to resolve the remaining goal |Even (n + 2)|.

In addition, we cannot directly reuse the implementation of |convert|
as used in the construction of terms. In this version of |convert|, an
|AgTerm| variable is mapped to a Prolog variable. When considering the
goal type, however, we want to generate \emph{skolem constants} for
our variables, rather than Prolog variables which may still be unified.
To account for this difference we have two flavours of the |convert|
function: |convert| and |convert4Goal|. Both differ only in their
implementation of |convertVar|.

\begin{code}
  agda2goal×premises : AgTerm → Error (∃ PsTerm × HintDB)
  agda2goal×premises t with convert4Goal 0 t
  ... | inj₁ msg            = inj₁ msg
  ... | inj₂ (n , p)        with split p
  ... | (k , ts)            with initLast ts
  ... | (prems , goal , _)  = inj₂ ((n , goal) , toPremises k prems)
\end{code}
Fortunately, we can reuse many of the other functions we have defined
above, and, using the |split| and |initLast| functions, we can get our
hands on the list of premises |prems| and the desired return type
|goal|. The only missing piece of the puzzle is a function, |toPremises|,
which converts a list of |PsTerm|s to a |Rules| list.
\begin{code}
  toPremises : ∀ {k} → ℕ → Vec (PsTerm n) k → HintDB
  toPremises i [] = []
  toPremises i (t ∷ ts) = (n , rule (rvar i) t []) ∷ toPremises (suc i) ts
\end{code}
The |toPremises| converts every |PsTerm| in its argument list to a
rule, using the argument's De Bruijn index as its rule name.


\subsection*{Reification of proof terms}

Now that we can compute Prolog terms, goals and rules from an Agda
|Term|, we are ready to call the resolution mechanism described in
Section~\ref{sec:prolog}. The only remaining problem is to convert the
witness computed by our proof search back to an |AgTerm|, which can
be unquoted to produce the desired proof. This is done by the
|reify| function that traverses its argument |Proof|; the only
interesting question is how it handles the variables and names it
encounters.

The |Proof| may contain two kinds of variables: locally bound
variables, |rvar i|, or variables storing an Agda |Name|, |name n|.
 Each of these variables is treated differently in the |reify|
function. Any references to locally bound variables are mapped to the |var|
constructor of the |AgTerm| data type. These variables correspond
to usage of arguments to the function being defined. As we know by
construction that these arguments are mapped to rules without
premises, the corresponding Agda variables do not need any further
arguments.
\begin{code}
  reify : Proof → AgTerm
  reify (con (rvar i) ps) = var i []
  reify (con (name n) ps) with definition n
  ... | function x    = def n (toArg ∘ reify ⟨$⟩ ps)
  ... | constructor′  = con n (toArg ∘ reify ⟨$⟩ ps)
  ... | _             = unknown
    where
      toArg : AgTerm → Arg AgTerm
      toArg = arg (arg-info visible relevant)
\end{code}
If the rule being applied is constructed using a |name|, we do
disambiguate whether the rule name refers to a function or a
constructor. The |definition| function, defined in Agda's reflection
library, tells you how a name was defined (i.e. as a function name,
constructor, etc). For the sake of brevity, we restrict
the definition here to only handle defined functions and data
constructors. It is easy enough to extend with further branches for
postulates, primitives, and so forth.

We will also need to wrap additional lambdas around the resulting
term, due to the premises that were introduced by the
|agda2goal×premises| function.
To do so, we define the |intros| function that repeatedly wraps its
argument term in a lambda.
\begin{code}
  intros : AgTerm → AgTerm
  intros = introsAcc (length args)
    where
      introsAcc : ℕ → AgTerm → AgTerm
      introsAcc  zero   t = t
      introsAcc (suc k) t = lam visible (introsAcc k t)
\end{code}

\subsection*{Hint databases}
\label{sec:hintdbs}

We allow users to provide hints, rules that may be used during
resolution, in the form of a \emph{hint database}. Such a hint
database is simply a list of Prolog rules:
\begin{code}
HintDB : Set
HintDB = List (∃ Rule)
\end{code}
We can construct hint databases using the insertion operator, |<<|.
\begin{code}
_<<_ : HintDB → Name → HintDB
db << n with name2rule n
db << n | inj₁ msg  = db
db << n | inj₂ r    = db ++ [ r ]
\end{code}
If the generation of a rule fails for whatever reason, no error is
raised, and the rule is simply ignored. Our actual implementation
requires an implicit proof argument that all the names in the argument
list can be quoted successfully. If you define such proofs to compute
the trivial unit record as evidence, Agda will fill them in
automatically in every call to the |_<<_| function on constant
arguments. This simple form of proof automation is pervasive in Agda
programs~\citep{oury,swierstra-more}.

This is the simplest possible form of hint database. In principle,
there is no reason not to define alternative versions that assign
priorities to certain rules or limit the number of times a rule may be
applied. We will investigate some possibilities for extensible proof
search in section~\ref{sec:extensible}.

Furthermore, note that a hint database is a simple list of rules. It
is an entirely first-class entity. We can combine hints databases,
filter certain rules from a hint database, or manipulate them in any
way we wish.

\subsection*{Error messages}
Lastly, we need to decide how to report error messages. Since we are
going to return an |AgTerm|, we need to transform the |Message|
type we saw previously into an |AgTerm|. When unquoted, this term
will cause a type error, reporting the reason for failure. To
accomplish this, we introduce a dependent type, indexed by a |Message|:
\begin{code}
data Exception : Message → Set where
    throw : (msg : Message) → Exception msg
\end{code}
The message passed as an argument to the |throw| constructor, will be
recorded in the |Exception|'s type, as we intended.

Next, we define a function to produce an |AgTerm| from a
|Message|. We could construct such terms by hand, but it is easier to
just use Agda's |quoteTerm| construct:
\begin{code}
quoteError : Message → Term
quoteError searchSpaceExhausted  =
  quoteTerm (throw searchSpaceExhausted)
quoteError unsupportedSyntax     =
  quoteTerm (throw unsupportedSyntax)
\end{code}

\subsection*{Putting it all together}

Finally, we can present the definition of the |auto| function used in
the examples in Section~\ref{sec:motivation}:
\begin{code}
  auto : ℕ → HintDB → AgTerm → AgTerm
  auto depth rules goalType
    with agda2goal×premises goalType
  ... | inj₁ msg = quoteError msg
  ... | inj₂ ((n , g) , args)
    with dfs depth (solve g (args ++ rules))
  ... | []      = quoteError searchSpaceExhausted
  ... | (p ∷ _) = intros (reify p)
\end{code}
The |auto| function takes the goal type, splits it into a goal and a
list of premises which may be used to construct this goal, and converts
both to |PsTerm|s.
It then proceeds by calling the |solve| function with the given hint
database and a new hint database constructed from the premises, and
searches the proof tree up to the given |depth|.
If this proof search succeeds, the |Proof| is converted to an
|AgTerm|, a witness that the original goal is inhabited.
There are two places where this function may fail: the conversion to a
|PsTerm| may fail because of unsupported syntax; or the
proof search may not find any result.


%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
