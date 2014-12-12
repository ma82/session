# Session

## Dependencies

### Agda

I am using the development version of Agda

    git clone https://github.com/agda/agda.git

Please let me know if some changes in Agda break compilation.

### Agda libraries

If you do not have it already, you need Agda's standard library:

    git clone https://github.com/agda/agda-stdlib.git

A couple other repositories are also required.

- [adapter](https://github.com/ma82/adapter)

    git clone http://github.com/ma82/adapter.git

- [concurrent-agda](https://github.com/ma82/concurrent-agda)

    git clone http://github.com/ma82/concurrent-agda.git

Do not forget to install `concurrent-agda`'s Haskell package.

    cd concurrent-agda/ffi
    cabal install

If everything worked, please check that the paths in `session`'s
`Makefile` are correct, otherwise edit them.

## Compilation of examples

    make examples

After a while some binaries should appear in `Session/Examples/`.

Please check that the output corresponds to that in the provided
`.out` files. Note that examples can be non-deterministic, though, so
some lines may appear in different order.

## Documentation

    make html

Or visit [this page](http://acerbi.works/html/Session.html).

## [License](https://www.gnu.org/licenses/gpl.html)

## Contacts

- [Mail](mailto:matteo.acerbi@gmail.com)
- [Site](http://acerbi.works/html/Session.html)

## Participate!

If you want to use/modify this project please let me know!
