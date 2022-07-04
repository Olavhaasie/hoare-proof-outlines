# Hoare Style Proof Outlines in Agda

This repository contains my report and Agda implementation for my Master's Thesis titled:

> Mechanizing Hoare Style Proof Outlines for Imperative Programs in Agda

The library defines Hoare triples and a syntax for writing outlines independent of target language or store implementation.
The mechanization aims to make the outlines more readable by using macros in Agda to solve tedious proofs.


## Structure

The thesis can be found at the [TU Delft repository][tu-delft-repo].
The main source is in [`src/`](src/).
See [`Everything.agda`](Everything.agda) for a complete overview and description of all modules in the library.
Examples of how to use the library are contained in [`examples/`](examples/).

[tu-delft-repo]: https://repository.tudelft.nl/islandora/object/uuid:5ca6e6f3-1242-4b86-8307-4ac4f4489951?collection=education


## How to check
The library depends on:

- [Agda v2.6.2][agda-git]
- [agda/agda-stdlib (ae0702e)][agda-stdlib-git]
- [ajrouvoet/ternary.agda (fe131ce)][ternary-git]

The correct versions of these dependencies are included in [`lib/`](lib/) as git submodules, so make sure you recursively clone the repository.
See the Agda documentation on how to [install Agda][install-agda] and libraries for your system.
You can check the entire library by running the following in the root of the repository:

    $ agda -i. Everything.agda

It might take a minute or two for the type checking to finish.
The library is checked using [`--safe`][safe] and [`--without-K`][without-k].

[agda-git]: https://github.com/agda/agda/tree/v2.6.2
[agda-stdlib-git]: https://github.com/agda/agda-stdlib/commit/ae0702e5f899db6622c02455c50e4446734ac051
[ternary-git]: https://github.com/ajrouvoet/ternary.agda/commit/fe131ce9c6d96b61b8b478c79233c44117a35cc5
[install-agda]: https://agda.readthedocs.io/en/latest/getting-started/installation.html
[safe]: https://agda.readthedocs.io/en/v2.6.2/tools/command-line-options.html?highlight=safe#cmdoption-safe
[without-k]: https://agda.readthedocs.io/en/v2.6.2/tools/command-line-options.html?highlight=without%20K#cmdoption-without-k

