# _Mass Effect 2_ Final Mission Analysis

> This document assumes the reader is familiar with the entirety of _Mass
> Effect 2_, including references and terminology that may be considered
> spoilers. You have been warned! :)

This Rust crate defines types that encode _decision paths_ and _outcomes_
related to the final mission of [_Mass Effect 2_]. Although the game presents
many, many choices to the player, only certain ones affect the survival of your
allies into and through [_Mass Effect 3_], if you transfer your save file. This
crate is only concerned with those aspects of the game.

## Outcome Data

The data generated by the `generate::outcome_map()` function is a map of
_outcomes_ to _metadata_ describing the decision paths that lead to those
outcomes. The metadata contains one example of a decision path and a count of
the total number of decision paths that lead to the same outcome, rather than
storing _all_ of the decision paths—there are over **64 billion** of them!

An `Outcome` encodes the following information:

- Which allies survived?
- Which surviving allies were _loyal_?
  - An ally becomes loyal if the player successfully completes their _loyalty
    mission_.
- Was the surviving crew of _The Normandy SR2_ rescued?
  - "The surviving crew" refers to the group that is still alive when Shepard
    arrives to rescue them.

A `DecisionPath` encodes the choices that affect the outcome. The examples
included in each outcome's metadata answer the following questions, some of
which are optional, depending on previous choices:

- Which optional allies should be recruited?
- Which loyalty missions should be completed?
- Which upgrades for _The Normandy_ should be purchased?
- Who should be selected for the squad to defend _The Normandy_'s cargo bay?
- Who should be selected for the various specialist roles?
- Who should be selected for the squad in the biotic shield?
- Who should be selected for the squad in the final battle?

Some player actions for which consequences for allies are realized in
_Mass Effect 2_ and beyond are not considered in the scope of this project. See
[Limitations](#limitations) for a discussion of the rationale behind the
exclusions.

To generate the data yourself, run the `generate` example provided in the
source.

```shell
$ cargo run --release --example generate -- PATH
```

## Interesting Facts

To show the kind of questions that can be answered with the data, the following
statistics were generated with the provided `analyze` example (and re-formatted
for markdown).

```shell
$ cargo run --example analyze -- outcome_map.rmp
```

- There are 64,396,302,636 total decision paths.
- There are 714,852 total outcomes.
- 111 outcomes are uniquely achievable.
  - These outcomes have the following in common:
    - Miranda survives and is loyal.
    - Garrus and Jacob are disloyal.
- The most common outcome can be achieved in 68,263,592 ways:
  - Only Jacob and Miranda survive, and both are loyal.
  - The crew is rescued.
- The 10 most common outcomes cover 419,652,725 decision paths.
- The 100 most common outcomes cover 2,068,928,184 decision paths.
- The 1000 most common outcomes cover 8,572,525,662 decision paths.
- Shepard dies in only 43 outcomes from 341,570,226 decision paths.
  - In other words, Shepard survives **99.47%** of all decision paths.
- The "best" possible outcome (a subjective measure, to be fair), in which
  everyone (except for Morinth) survives and is loyal, can be achieved in 7,968
  ways.
  - If you managed to do it on your first run, give yourself a pat on the back!

### Survival Rates

The following table, which shows the absolute survival rates for each ally
under different conditions, is also generated by the `analyze` example. Allies
are sorted in descending order by their total absolute survival rate.

| Ally     | Loyal    | Disloyal | Total    |
| -------- | -------- | -------- | -------- |
| Miranda  | 0.51996  | 0.19516  | 0.71513  |
| Jacob    | 0.43366  | 0.15589  | 0.58954  |
| Garrus   | 0.37451  | 0.15837  | 0.53288  |
| Zaeed    | 0.32652  | 0.19610  | 0.52263  |
| Grunt    | 0.30619  | 0.18244  | 0.48864  |
| Legion   | 0.26426  | 0.10292  | 0.36718  |
| Thane    | 0.22933  | 0.13319  | 0.36252  |
| Samara   | 0.21059  | 0.14190  | 0.35250  |
| Mordin   | 0.30812  | 0.03100  | 0.33912  |
| Jack     | 0.24870  | 0.06639  | 0.31509  |
| Kasumi   | 0.26672  | 0.02895  | 0.29567  |
| Tali     | 0.26154  | 0.02397  | 0.28551  |
| Morinth  | 0.22909  | 0.00000  | 0.22909  |

> NOTE: Survival implies recruitment. That is, if an ally is not recruited,
> they are _not_ regarded as surviving.

## Limitations

The following subsections discuss some of the known and perceived limitations
of this crate.

### Partial Data

As previously mentioned, only as many decision paths are recorded in the data
as there are outcomes even though there is a one-to-many relationship between
them.

As a quick thought experiment, suppose each decision path could be somehow
perfectly encoded and compressed into four-and-a-half bytes (36 bits). The
decision paths _alone_ would require almost 290 GB of memory/storage—and that's
the _best_ case!

In reality, the encoding would require more than 36 bits, so it's not
reasonable to expect potential consumers of this crate to sacrifice so much of
their storage to host the data. By embracing this limitation, it is possible to
provide the fully-generated data within the crate's source repository so users
don't have to spend the 10–15 minutes it would take to generate it themselves.

### Scope

The scope of this project is limited to only the parameters that affect the
fate of [_Mass Effect 2_] allies when carried over to [_Mass Effect 3_]. If an
ally survives _ME2_, they will be encounterable in _ME3_. Furthermore, if they
are loyal, they may become a war asset in _ME3_. If they were not loyal,
however, they would die in _ME3_.

However, there are two members of the crew of _The Normandy SR2_ who are not
specifically addressed in this implementation: Dr. Karen Chakwas and YN Kelly
Chambers. Outcomes only encode _whether_ the crew was rescued, but that is only
part of the story. Some of the crew may die _before_ they are rescued based on
the number of missions completed after the installation of the Reaper IFF.

| Missions | Result                                              |
| -------- | --------------------------------------------------- |
| 0        | Everyone in the crew survives.                      |
| 1–3      | Half of the crew dies, including YN Kelly Chambers. |
| >3       | Everyone except Dr. Karen Chakwas dies.             |

Both Chambers and Chakwas return in _ME3_ if they survive the final mission of
_ME2_, and Chambers even has an "implicit loyalty" in _ME2_ that factors into
her fate in _ME3_. So, why are they not explicitly considered?

In Dr. Chakwas's case, her survival is entirely dependent on whether an escort
is selected, so _rescuing the crew_ means, at the very least, that she
survives.

However, the decisions leading to YN Chambers's loyalty and survival have no
bearing on any of the choices the player can make during the finale of _ME2_.
_Any_ decision path can be arbitrarily annotated with all possible combinations
of Kelly's loyalty and survival without changing anything else about the
choices made in that decision path, and you would always end up with a valid
decision path.

In the end, although the previously mentioned choices have consequences in
_ME3_, the author considers them orthogonal to the decisions addressed in this
crate.

## References

This project was made possible by some amazing people in the _Mass Effect_
community, particularly those who took the time to answer some esoteric
questions on the [subreddit]. Of particular importance was this [flowchart]
for which I regrettably am unable to find any attribution, though I believe
that particular version was distilled from a primary source that is also
unknown to me.

## History

This crate is based on [a nearly identical project] I originally wrote in
Python. The statistics included in that project's README are noticeably
different than [those above](#interesting-facts). I am not entirely sure why,
though I suspect a subtle bug in the logic that allows the outcome data
generation to be paused/continued. That mechanism was necessary to prevent
unrelated problems (e.g., power outages) from causing _days_ of computing time
to be lost.

### Performance

You might be asking, "Days? Really?" Yes, really.

In retrospect, I made some poor decisions in the Python implementation that I
avoided this time around:

- I insisted on bit-packing (manually encoding) _everything_ into Python
  `int`s, which have a _variable bit width_.
  - Although the variable size is nice for performing computations with
    extremely large numbers, it makes bitwise arithmetic quite slow.
  - I didn't actually need to be so paranoid about the size of serialized data
    structures, so encoding/decoding stuff just wasted time—and made it really
    annoying to actually query the data.
- The generation logic serialized whatever progress it had made _to disk_
  _**every five seconds**_.
  - If you had lost data as often as I had, maybe you would have I/O bound your
    algorithm, too. :'(
- All decision path traversals occurred on the same thread.

The last point turned out not to be as much of an issue in Rust. A naïve port
of the Python implementation—minus the bit-packing and overly-eager disk
I/O—took less than 90 minutes to generate all of the outcome data on my system.
Not bad!

Things got _really_ fast when I finally got around to using more of the CPU's
cores. With a combination of the [`rayon`] and [`dashmap`] crates, it was very
easy to parallelize the algorithm. However, applying `rayon` to everything
eventually reaches a point of diminishing returns, so I only changed _enough_
to maximize the speed-up. It turns out that parallelizing the first three
levels of recursion was sufficient. As a result, it now takes just over ten
minutes to generate all of the data. Good enough!

[_Mass Effect 2_]: https://en.wikipedia.org/wiki/Mass_Effect_2
[_Mass Effect 3_]: https://en.wikipedia.org/wiki/Mass_Effect_3
[subreddit]: https://www.reddit.com/r/masseffect/
[flowchart]: https://external-preview.redd.it/7SeMlQbU-xFC9TjKurncqx1y8NH3RJiolYRqFAoXfWg.jpg?auto=webp&s=a57ad480a357234ec7fa5f865b00b60b95670df0
[a nearly identical project]: https://github.com/80Ltrumpet/me2-decision-tree
[`rayon`]: https://crates.io/crates/rayon
[`dashmap`]: https://crates.io/crates/dashmap