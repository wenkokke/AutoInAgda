\section{Type classes}
\label{sec:typeclasses}

As a final application of our proof search algorithm, we show how it
can be used to implement a \emph{type classes} in the style of
Haskell. Souzeau and Oury~\cite{coq-type-classes} have already shown
how to use Coq's proof search mechanism to construct
dictionaries. Using Agda's \emph{instance
  arguments}~\cite{instance-args} and the proof search presented in
this paper, we mimic their results.

We begin by declaring our `type class' as a record containing the
desired function:
\begin{code}
  record Show (A : Set) : Set where
    field
      show : A → String
\end{code}

We can write instances for the |Show| `class' by constructing explicit
dictionary objects:
\begin{code}
  ShowBool  : Show Bool
  ShowBool = record { show = ... }

  Showℕ : Show ℕ
  Showℕ = record { show = ... }
\end{code}
Using instance arguments, we can now call our |show| function without
having to pass the required dictionary explicitly:
\begin{code}
  open Show {{...}}

  example : String
  example = show 3
\end{code}
The instance argument mechanism infers that the |show| function is
being called on a natural number, hence a dictionary of type |Show ℕ|
is required. As there is only a single value of type |Show ℕ|, the
required dictionary is inserted automatically. If we have multiple
instance definitions for the same type or omit the required instance
altogether, the Agda type checker would have given an error.

It is more interesting to consider parametrized instances, such as
the |Either| instance given below.
\begin{code}
  ShowEither : Show A → Show B → Show (Either A B)
  ShowEither ShowA ShowB = record { show = showE }
    where
      showE : Either A B -> String
      showE (left x)   = "left " ++ show x
      showE (right y)  = "right " ++ show y
\end{code}
Unfortunately, instance arguments do not do any recursive search for
suitable instances. Trying to call |show| on a value of type |Either ℕ
Bool|, for example, will not succeed: the Agda type checker will
complain that it cannot find a suitable instance argument. At the
moment, the only way to resolve this is to construct the required
instances manually:
\begin{code}
  ShowEitherBoolℕ : Show (Either Bool ℕ)
  ShowEitherBoolℕ = ShowEither ShowBool Showℕ
\end{code}
Writing out such dictionaries is rather tedious.

We can, however, use the |auto| function to construct the desired
instance argument automatically. We start by putting the desired
instances in a hint database:
\begin{code}
  ShowHints : HintDB
  ShowHints = hintdb  (quote ShowEither
                      ∷ quote ShowBool
                      ∷ quote Showℕ ∷ [])
\end{code}

The desired dictionary can now be assembled for us by calling the
|auto| function:
\begin{code}
  example : String
  example = show (left 4) ++ show (right true)
    where
      instance = tactic (auto 5 ShowHints)
\end{code}
Note that the type of the locally bound |instance| record is inferred
in this example. Using this type, the |auto| function assembles the
desired dictionary. When |show| is called on different types, however,
we may still need to provide the type signatures of the instances we
desire.
While deceptively simple, this example illustrates how \emph{useful}
it can be to have even a little automation.

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% TeX-command-default: "rake"
%%% End:
