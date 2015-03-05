# Coq #

## Software ##

Use designated versions of software in this class to avoid version incompatibility. Your submission will not be properly graded if you do not follow this instruction.
- Use [Coq 8.4pl5](https://coq.inria.fr/distrib/V8.4pl5/files/).
    + Coq is already installed in the lab.
    + For your personal computer:
        * Install [opam](http://opam.ocaml.org/doc/Install.html), and make sure you can use OCaml 4.01.0.
        * Download [tarball](https://coq.inria.fr/distrib/V8.4pl5/files/coq-8.4pl5.tar.gz) file.
        * Extract the tarball, `./configure`, `make`, and then `make install`.
        * Test by `coqc -v` in the command line. Check your `PATH` variable if you get an error.
    + For OS X, I recommend you to download [those with CoqIDE bundle](https://coq.inria.fr/distrib/V8.4pl5/files/coqide-8.4pl5.dmg). And you may have to properly set path variable. add the following in `~/.bashrc`: `export PATH=/Applications/CoqIdE_8.4pl5.app/Resources/bin/:$PATH`. (May not work in your environment; be cautious before blindly adding the line.)
    + For OS X, an alternative way to install Coq is using `brew`. See [#1](https://github.com/snu-sf/pl2015/issues/1) for more details.
- Use software foundations material in this repository (as explained in the Homeworks section below).
