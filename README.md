# Linear dependent session types in Agda

## No Warranty

I started working at this project circa July 2013. Nonetheless, this
is very experimental work-in-progress code, no correctness proof is
provided and it might not work as expected.

## No Logic

While the main original inspiration was Philip Wadler's "Propositions
as sessions", the use of the word *linear* in the title does not mean
I devised a syntax for a version of Linear Logic.

Apart from replacing polymorphism with dependent quantification, I
made **many** changes to the rules in order to obtain the programming
interface I wanted. I will add many comments and explanations when I
have more time.

## Documentation

    make html
    
**Warning** The above should work in any system, however I use that
command with a (too buggy to share) patch to Agda that translates the
Markdown paragraphs to HTML using `pandoc`.

I guess the same can be done more properly using `PandocAgda` from
Hackage (which I never tried), but you might need to change the
command.

## Agda version

I am using the development version of Agda

    darcs get --lazy http://code.haskell.org/Agda
   
Please let me know if some changes in Agda break compilation.

## Agda dependencies

If you do not have it already, you need Agda's standard library:

    darcs get --lazy http://www.cse.chalmers.se/~nad/repos/lib/

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

After a (possibly long) while some binaries should appear in
`Session/Examples/`.

In the unlikely case that they run, please check if the output
corresponds to that in the provided `.out` files. Note that examples
can be non-deterministic, though.

## [License](https://www.gnu.org/licenses/gpl.html)

## Contacts

[Mail](mailto:matteo.acerbi@gmail.com)
[Site](http://ma82.github.io/)

## Participate!

If you want to use/modify this project please let me know!