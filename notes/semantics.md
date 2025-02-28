This document describes some challenges and proposals for defining the semantics
of a Stan program and proving that the compiler preserves semantics. It combines
various ideas from the proposal and miscellaneous thoughts from various
conversations since then.

# Review of CompCert's approach

First, we sketch what CompCert proves about the correctness of compiling C programs. 
At a high level, CompCert says that programs have two kinds of observable behavior:

1. Trace events that occur when certain program steps are taken (e.g. calls to printf)
2. Final return values (i.e. the return value of int main())


CompCert's correctness theorem says that these observable behaviors are
preserved by compilation. More formally, this is captured through the idea of a
backward simulation, which CompCert proves by establishing forward simulations.

# Challenges

While CompCert's notion of observable behavior makes a lot of sense for C (and
indeed, most "normal" programming languages), it is difficult to directly use in
the context of a Stan program. After all, a Stan program just consists of a
bunch of blocks: it is the job of the runtime to glue those together to make a
"complete" program that produces IO and returns things.
Thus, we first need to clarify the semantics and observable behaviors of Stan programs.

CStan, following CompCert's operational semantics for Clight, already does a
pretty good job of describing what the *statements* inside of a block do, but
what is missing is a definition of how those blocks are combined together to
define a "whole" program.

We first describe a straw-man solution (which seems impractical) and then
propose another route that seems more feasible.

## Straw Man Proposal

One way to define the semantics of a Stan program would be to emulate/encode
the behavior of the run time inside of Coq. That is, we could encode the process that
a MH sampler uses to generate samples:

- Generate proposals for parameters
- Evaluate the likelihood for the proposal (using the statement-level semantics of the model block)
- Decide whether to accept the proposal
- Generate output trace events recording the transformed parameters that result from that parameter.

The result would be a full program that generates a trace, for which one could try to prove semantic preservation. There are a couple of draw backs of this approach:

1. It embeds a fixed/particular MCMC strategy inside the semantics, while we
   know that there are many MCMC algorithms that could be used in the runtime.

2. It would be very difficult to prove that certain transformations actually are
   semantically preserving with respect to this semantics. (In fact, there are
   some transformations that probably *don't* exactly preserve the IO behavior
   in this sense: even though they may preserve the asymptotic behavior of the
   samples generated by MCMC they may change the rate of convergence.)
   
   
## Alternative

Let us call the combination of the initial parameters of a Stan program and
the transformed parameters, the *output parameters* of a Stan program.

Then, an alternative is to treat a Stan program as defining a function from data
to a distribution on these output parameters. It is this distribution that the
runtime is trying to draw samples from. With this perspective, the compiler's
job is to preserve this distribution.

More specifically, we define this distribution semantics through the following steps.

From the CStan semantics for statements/expressions, we can interpret the model block as a Coq level function. In particular, the program AST should record the list of parameters and their constraints. Let us say they are:

[l1, u1]x1, ..., [ln, un]xn 

where xi is the name of the parameter, li is a lower bound constraint (possibly
-inf if no constraint is given), and ui is the upper bound (possibly +inf).
Additionally, let Data be the type of input data the Stan program expects, again this can be determined
from the program AST by looking at the data block.

Then, we can define a Coq-level function that represents what the model block is
intended to compute. We define modelPdf : Data -> [l1,u1] -> ... -> [ln, un] ->
R, where [li, ui] is the real interval with li as lower bound and ui as upper
bound. Given d : Data and v1, ..., vn, modelPdf(d, v1, ..., vn), we define
modelPdf to be:

1. Load values d and v1, ..., vn into the respective globals for data/parameters
   (or, alternatively, if model instead is a *function* that takes arguments, we
   would define structs containing the arguments

2. "Run" the model block on the resulting memory/arguments, by using axiom for
   constructive indefinite description to "return" some r if there exists an
   execution of the model block that return that value for target

Given this function, we can then define a function from data to a measure on parameters by integrating.

That gives us a measure on *parameters*, but note that the measure on parameters
is not really quite the right notion of observable behavior, because the
parameters change as we do things like compile away constraints. Thus, we
instead want a meausre on *output parameters* (i.e. the initial parameters +
transformed parameters), which we can obtain as the push-forward measure
obtained by "running" the transformed parameters block.

It is this last measure that should remain invariant across the stages of compilation.

# Connecting to CompCert's proof and proof techniques

Note that the notion of semantic preservation just described is actually
*weaker* than what CompCert guarantees. CompCert is promising that each
function's exact behavior is preserved (or rather, there's a way to obtain this
from the trace preservation behavior mentioned above. As John explains, you need
per function semantic preservation in order for separate compilation to work.)

That makes sense, because if the model block code has the same behavior as a
function, and similarly for transformed parameters, then the measure defined
above doesn't change either. 

Indeed, for many passes of ProbCompCert this extensional behavior of the model
block is preserved as well, and it's actually probably just easier to show this
and use that to imply measure preservation.

The major exception is the removing of constraints. There, the correctness of the pass really
depends on properies of integration. I suggest that we factor this proof into two parts:

1. Showing that the transformed code is implementing the change of variables correctly.
2. Arguing why (purely in math) that preserves the integral.
